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

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;

import java.util.*;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;


    private PointerAnalysisResult pta;
    private HashMap<Var, Set<Var>> aliasMap = new HashMap<>();

    private HashMap<Var, Set<Obj>> pointsToMap = new HashMap<>();

    private HashMap<FieldAccess, Value> fieldAccessValueHashMap = new HashMap<>();
    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        pta = World.get().getResult(ptaId);
        // You can do initialization work here
        for (Var var : pta.getVars()) {
            pointsToMap.put(var, pta.getPointsToSet(var));
        }
        for (Var var : pointsToMap.keySet()) {
            Set<Obj> pointsToSet = pointsToMap.get(var);
            for (Var otherVar: pointsToMap.keySet()) {
//                if (var == otherVar) {
//                    continue;
//                }
                Set<Obj> otherPointsToSet = pointsToMap.get(otherVar);
                boolean intersect = !Collections.disjoint(pointsToSet, otherPointsToSet);
                if (intersect) {
                    Set<Var> aliasSet = aliasMap.getOrDefault(var, new HashSet<>());
                    aliasSet.add(otherVar);
                    aliasMap.put(var, aliasSet);
                }
            }
        }
        FieldAccess a = null;
//        pta.getPointsToSet(a.getFieldRef().resolve())
//        pta.getInstanceFields().forEach(field -> {
//            if (field.getName().equals("a")) {
//                a = field;
//            }
//        });
    }
    public Set<Var> getAlias(Var var) {
        return aliasMap.get(var);
    }
    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        Boolean changed = false;
        if (!in.keySet().equals(out.keySet())) {
            changed = true;
        }
        out.clear();
        changed |= out.copyFrom(in);
        return changed;
    }

    public boolean isAliasVar(Var var1, Var var2) {
        Set<Var> aliasVars = getAlias(var1);
        return aliasVars.contains(var2);
    }
    public boolean isAliasFieldAccess(FieldAccess fieldAccess1, FieldAccess fieldAccess2) {
        if (fieldAccess1 instanceof InstanceFieldAccess fieldAccess11 && fieldAccess2 instanceof InstanceFieldAccess fieldAccess22) {
            Var base1 = fieldAccess11.getBase();
            Var base2 = fieldAccess22.getBase();
            return isAliasVar(base1, base2) && fieldAccess11.getFieldRef().equals(fieldAccess22.getFieldRef());
        }
        else if (fieldAccess1 instanceof StaticFieldAccess fieldAccess11 && fieldAccess2 instanceof StaticFieldAccess fieldAccess22) {
            return fieldAccess11.getFieldRef().equals(fieldAccess22.getFieldRef());
        }
        return false;
    }
    public Set<FieldAccess> getAliasFieldAccesses(FieldAccess fieldAccess) {
        Set<FieldAccess> aliasFields = new HashSet<>();
        for (FieldAccess fieldAccess1 : fieldAccessValueHashMap.keySet()) {
            if (isAliasFieldAccess(fieldAccess, fieldAccess1)) {
                aliasFields.add(fieldAccess1);
            }
        }
        return aliasFields;
    }
    public void storeFieldAccessValue(StoreField storeField, Value value) {
        FieldAccess fieldAccess = storeField.getFieldAccess();
        Value prevStoredValue = fieldAccessValueHashMap.get(fieldAccess);
        if (prevStoredValue == null) {
            prevStoredValue = Value.getUndef();
        }
        Value newValue = cp.meetValue(prevStoredValue, value);
        if (fieldAccess instanceof InstanceFieldAccess fieldAccess1) {
            Set<FieldAccess> aliasFields = getAliasFieldAccesses(fieldAccess1);
            Value newValueForAll = newValue;
            for (FieldAccess aliasField : aliasFields) {
                Value prevStoredValueForAlias = fieldAccessValueHashMap.get(aliasField);
                if (prevStoredValueForAlias == null) {
                    prevStoredValueForAlias = Value.getUndef();
                }
                newValueForAll = cp.meetValue(prevStoredValueForAlias, newValueForAll);
            }
            for (FieldAccess aliasField : aliasFields) {
                fieldAccessValueHashMap.put(aliasField, newValueForAll);
            }
            fieldAccessValueHashMap.put(fieldAccess, newValueForAll);
        }
        else if (fieldAccess instanceof StaticFieldAccess fieldAccess1) {
            fieldAccessValueHashMap.put(fieldAccess, newValue);
        }
    }

    public Value loadFieldAccessValue(FieldAccess fieldAccess) {
        Set<FieldAccess> aliasFields = getAliasFieldAccesses(fieldAccess);
        Value value = Value.getUndef();
        for (FieldAccess aliasField : aliasFields) {
            Value prevStoredValueForAlias = fieldAccessValueHashMap.get(aliasField);
            if (prevStoredValueForAlias == null) {
                prevStoredValueForAlias = Value.getUndef();
            }
            value = cp.meetValue(prevStoredValueForAlias, value);
        }
        return value;

//        if (fieldAccess instanceof InstanceFieldAccess fieldAccess1) {
//            Var base = fieldAccess1.getBase();
//            Set<Var> aliasVars = getAlias(base);
//            Value newValue = fieldAccessValueHashMap.get(fieldAccess);
//            if (newValue != null) {
//                for (Var aliasVar : aliasVars) {
//                    Value oldValue = fieldAccessValueHashMap.get(fieldAccess);
//                    if (oldValue == null || oldValue != newValue) {
//                        fieldAccessValueHashMap.put(fieldAccess, cp.meetValue(newValue, oldValue));
//                    }
//                }
//            }
//        }
//        else if (fieldAccess instanceof StaticFieldAccess fieldAccess1) {
//            Value value = fieldAccessValueHashMap.get(fieldAccess);
////            if (value != null) {
////                cp.updateValue(loadedVar, value);
////            }
//        }
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        if (stmt instanceof StoreField storeField) {
            Value value = in.get(storeField.getRValue());
            storeFieldAccessValue(storeField, value);
            Boolean changed = false;
            for (Var v : in.keySet()) {
                changed |= out.update(v, in.get(v));
            }
            return changed;
        }
        else if (stmt instanceof LoadField loadField) {
            FieldAccess fieldAccess = loadField.getFieldAccess();
            JField field = fieldAccess.getFieldRef().resolve();
            Var loadedVar = loadField.getLValue();
            Value newValue = loadFieldAccessValue(fieldAccess);
            Value oldValue = in.get(loadedVar);
            Boolean changed = false;
            for (Var v : in.keySet()) {
                changed |= out.update(v, in.get(v));
            }
            changed = out.update(loadedVar, cp.meetValue(newValue, oldValue));
            return changed;
        }
        else {
            return cp.transferNode(stmt, in, out);
        }
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // Identity transfer function
        return out;
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        Stmt callSite = edge.getSource();
        CPFact ret = out.copy();
        if (callSite.getDef().isPresent()){
            LValue lftVar = callSite.getDef().get();
            if (lftVar instanceof Var) {
                ret.remove((Var) lftVar);
            }
        }
        return ret;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        IR ir = edge.getCallee().getIR();
        CPFact ret = new CPFact();
        List<Var> params = ir.getParams();
        List<Var> vars = ((Invoke)edge.getSource()).getInvokeExp().getArgs();
        for (int i = 0; i < params.size(); i++) {
            Var param = params.get(i);
            Var var = (Var) vars.get(i);
            if (!ConstantPropagation.canHoldInt(param)) {
//                ret.update(param, Value.getNAC());
                continue;
            }
            ret.update(param, callSiteOut.get(var));
        }
        return ret;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        Collection<Var> returnVars = edge.getReturnVars();
        Stmt callSite = edge.getCallSite();
        CPFact ret = new CPFact();
        Value value = Value.getUndef();
        if (callSite.getDef().isEmpty()) {
            return ret;
        }
        for (Var returnVar : returnVars) {
            value = cp.meetValue(value, returnOut.get(returnVar));
        }
        ret.update((Var) callSite.getDef().get(), value);
        return ret;
    }
}
