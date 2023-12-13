/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.analysis.constprop;

import fj.test.Bool;
import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import java.awt.*;
import java.sql.Statement;
import java.util.Optional;

import static pascal.taie.ir.exp.ArithmeticExp.Op.DIV;
import static pascal.taie.ir.exp.ArithmeticExp.Op.REM;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        CPFact fact = new CPFact();
        for (Var param: cfg.getIR().getParams()) {
            if (canHoldInt(param)) {
                fact.update(param, Value.getNAC());
            }
        }
        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        for (Var var: fact.keySet()) {
            target.update(var, meetValue(fact.get(var), target.get(var)));
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
//        What is the value NAC and UNDEF?
        if (v1.isConstant() && v2.isConstant()) {
            if (v1.getConstant() == v2.getConstant()) {
                return v1;
            } else {
                return Value.getNAC();
            }
        }
        else if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        }
        else if (v1.isUndef()) {
            return v2;
        }
        else if (v2.isUndef()) {
            return v1;
        }
        else {
            return Value.getUndef();
        }
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        if (stmt == null || in == null || out == null) {
            assert(false);
            return false;
        }
        Optional<LValue> assignedVar = stmt.getDef();
        // Left side is field access or something like that, out should be the same as in.
        if (assignedVar.isPresent()) {
            if (assignedVar.get() instanceof Var) {
                Var var = (Var) assignedVar.get();
                // If the left side is an integer variable, then we can update the value of it.
                if (canHoldInt(var)) {
                    // Get the last in stmt.getUses
                    Exp rValue = stmt.getUses().get(stmt.getUses().size() - 1);
                    Value value = evaluate(rValue, in, null);
                    Value prevValue = out.get(var);
                    Boolean changed = false;
                    for (Var v : in.keySet()) {
                        changed |= out.update(v, in.get(v));
                    }
                    changed |= out.update(var, value);
                    return changed;
                }
            }
        }
        boolean changed = false;
        for (Var v : in.keySet()) {
            changed |= out.update(v, in.get(v));
        }
        return changed;
    }
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out, PointerAnalysisResult pta) {
        if (stmt == null || in == null || out == null) {
            assert(false);
            return false;
        }
        Optional<LValue> assignedVar = stmt.getDef();
        // Left side is field access or something like that, out should be the same as in.
        if (assignedVar.isPresent()) {
            if (assignedVar.get() instanceof Var) {
                Var var = (Var) assignedVar.get();
                // If the left side is an integer variable, then we can update the value of it.
                if (canHoldInt(var)) {
                    // Get the last in stmt.getUses
                    Exp rValue = stmt.getUses().get(stmt.getUses().size() - 1);
                    Value value = evaluate(rValue, in, pta);
                    Value prevValue = out.get(var);
                    Boolean changed = false;
                    for (Var v : in.keySet()) {
                        changed |= out.update(v, in.get(v));
                    }
                    changed |= out.update(var, value);
                    return changed;
                }
            }
        }
        boolean changed = false;
        for (Var v : in.keySet()) {
            changed |= out.update(v, in.get(v));
        }
        return changed;
    }
    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in, PointerAnalysisResult pts) {
        if (exp instanceof Var) {
            return in.get((Var) exp);
        }
        else if (exp instanceof IntLiteral) {
            return Value.makeConstant(((IntLiteral) exp).getValue());
        }
        else if (exp instanceof BinaryExp) {
            if (exp instanceof ArithmeticExp) {
                Var v1 = (Var) ((ArithmeticExp) exp).getOperand1();
                Var v2 = (Var) ((ArithmeticExp) exp).getOperand2();
                Value value1 = in.get(v1);
                Value value2 = in.get(v2);
                if (value1.isConstant() && value2.isConstant()) {
                    switch (((ArithmeticExp) exp).getOperator()) {
                        case ADD: {
                            return Value.makeConstant(value1.getConstant() + value2.getConstant());
                        }
                        case SUB: {
                            return Value.makeConstant(value1.getConstant() - value2.getConstant());
                        }
                        case MUL: {
                            return Value.makeConstant(value1.getConstant() * value2.getConstant());
                        }
                        case DIV: {
                            if (value2.getConstant() == 0) {
                                return Value.getUndef();
                            }
                            else {
                                return Value.makeConstant(value1.getConstant() / value2.getConstant());
                            }
                        }
                        case REM: {
                            if (value2.getConstant() == 0) {
                                return Value.getUndef();
                            }
                            else {
                                return Value.makeConstant(value1.getConstant() % value2.getConstant());
                            }
                        }
                    }
                }
                else if (value1.isNAC() || value2.isNAC()) {
                    if (value1.isNAC() && value2.isConstant() && value2.getConstant() == 0) {
                        if (((ArithmeticExp) exp).getOperator() == DIV || ((ArithmeticExp) exp).getOperator() == REM) {
                            return Value.getUndef();
                        }
                    }
                    return Value.getNAC();
                }
                else {
                    return Value.getUndef();
                }

            } else if (exp instanceof ConditionExp) {
                Var v1 = (Var) ((ConditionExp) exp).getOperand1();
                Var v2 = (Var) ((ConditionExp) exp).getOperand2();
                Value value1 = in.get(v1);
                Value value2 = in.get(v2);
                if (value1.isConstant() && value2.isConstant()) {
                    return switch (((ConditionExp) exp).getOperator()) {
                        case EQ -> Value.makeConstant(value1.getConstant() == value2.getConstant() ? 1 : 0);
                        case NE -> Value.makeConstant(value1.getConstant() != value2.getConstant() ? 1 : 0);
                        case GT -> Value.makeConstant(value1.getConstant() > value2.getConstant() ? 1 : 0);
                        case GE -> Value.makeConstant(value1.getConstant() >= value2.getConstant() ? 1 : 0);
                        case LT -> Value.makeConstant(value1.getConstant() < value2.getConstant() ? 1 : 0);
                        case LE -> Value.makeConstant(value1.getConstant() <= value2.getConstant() ? 1 : 0);
                    };
                }
                else if (value1.isNAC() || value2.isNAC()) {
                    return Value.getNAC();
                }
                else {
                    return Value.getUndef();
                }

            } else if (exp instanceof ShiftExp) {
                Var v1 = (Var) ((ShiftExp) exp).getOperand1();
                Var v2 = (Var) ((ShiftExp) exp).getOperand2();
                Value value1 = in.get(v1);
                Value value2 = in.get(v2);
                if (value1.isConstant() && value2.isConstant()) {
                    return switch (((ShiftExp) exp).getOperator()) {
                        case SHL -> Value.makeConstant(value1.getConstant() << value2.getConstant());
                        case SHR -> Value.makeConstant(value1.getConstant() >> value2.getConstant());
                        case USHR -> Value.makeConstant(value1.getConstant() >>> value2.getConstant());
                    };
                }
                else if (value1.isNAC() || value2.isNAC()) {
                    return Value.getNAC();
                }
                else {
                    return Value.getUndef();
                }
            } else if (exp instanceof BitwiseExp) {
                Var v1 = (Var) ((BitwiseExp) exp).getOperand1();
                Var v2 = (Var) ((BitwiseExp) exp).getOperand2();
                Value value1 = in.get(v1);
                Value value2 = in.get(v2);
                if (value1.isConstant() && value2.isConstant()) {
                    return switch (((BitwiseExp) exp).getOperator()) {
                        case AND -> Value.makeConstant(value1.getConstant() & value2.getConstant());
                        case OR -> Value.makeConstant(value1.getConstant() | value2.getConstant());
                        case XOR -> Value.makeConstant(value1.getConstant() ^ value2.getConstant());
                    };
                }
                else if (value1.isNAC() || value2.isNAC()) {
                    return Value.getNAC();
                }
                else {
                    return Value.getUndef();
                }
            }
            else {
                return Value.getNAC();
            }
        }
        else if (exp instanceof StoreField storeField) {
            if (storeField.isStatic()) {

            }
            else {

            }
        }
        else if (exp instanceof LoadField loadField) {
            if (loadField.isStatic()) {

            }
            else {

            }
        }
        else if (exp instanceof LoadArray loadArray) {

        }
        else if (exp instanceof StoreArray storeArray) {

        }
        else {
            return Value.getNAC();
        }
        return Value.getNAC();
    }
}

