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

import heros.fieldsens.AccessPathHandler;
import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
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
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;

import java.util.*;
import java.util.stream.Collectors;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

//    LinkedList<Node> workList = new LinkedList<>();
    private PointerAnalysisResult pta;
    private HashMap<Var, Set<Var>> aliasMap = new HashMap<>();
    private HashMap<Var, Set<Obj>> pointsToMap = new HashMap<>();
    private HashMap<FieldAccess, Value> fieldAccessValueHashMap = new HashMap<>();
//    private HashMap<FieldAccess, Set<LoadField>>

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
                    aliasMap.computeIfAbsent(var, k -> new HashSet<>()).add(otherVar);
                }
            }
        }
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
        if (aliasVars == null) {
            return false;
        }
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
    public boolean isAliasArrayAccess(ArrayAccess arrayAccess1, ArrayAccess arrayAccess2, Value index1, Value index2) {
        Var base1 = arrayAccess1.getBase();
        Var base2 = arrayAccess2.getBase();
        if (!isAliasVar(base1, base2)) {
            return false;
        }
        if (index1.isUndef() || index2.isUndef()) {
            return false;
        }
        if (index1.isNAC() || index2.isNAC()) {
            return true;
        }
        if (index1.isConstant() && index2.isConstant()) {
            return index1.equals(index2);
        }
//        assert false;
        return false;
    }

    public Set<LoadField> getAliasFieldLoads(FieldAccess fieldAccess) {
        return icfg.getNodes()
                .stream()
                .filter(node -> node instanceof LoadField)
                .map(node -> (LoadField) node)
                .filter(node -> isAliasFieldAccess(node.getFieldAccess(), fieldAccess))
                .collect(Collectors.toSet());
    }
    public Set<StoreField> getAliasStoreFields(FieldAccess fieldAccess) {
        return icfg.getNodes()
                .stream()
                .filter(node -> node instanceof StoreField)
                .map(node -> (StoreField) node)
                .filter(node -> isAliasFieldAccess(node.getFieldAccess(), fieldAccess))
                .collect(Collectors.toSet());
    }
    public Set<LoadArray> getAliasLoadArrays(StoreArray storeArray) {
        ArrayAccess arrayAccess = storeArray.getArrayAccess();
        Value indexVar = solver.getResult().getInFact(storeArray).get(arrayAccess.getIndex());
        return icfg.getNodes()
                .stream()
                .filter(node -> node instanceof LoadArray)
                .map(node -> (LoadArray) node)
                .filter(node -> isAliasArrayAccess(node.getArrayAccess(), arrayAccess, solver.getResult().getInFact(node).get(node.getArrayAccess().getIndex()), indexVar))
                .collect(Collectors.toSet());
    }

    public Set<StoreArray> getAliasStoreArrays(LoadArray loadArray) {
        ArrayAccess arrayAccess = loadArray.getArrayAccess();
        Value indexVar = solver.getResult().getInFact(loadArray).get(arrayAccess.getIndex());
        return icfg.getNodes()
                .stream()
                .filter(node -> node instanceof StoreArray)
                .map(node -> (StoreArray) node)
                .filter(node -> isAliasArrayAccess(node.getArrayAccess(), arrayAccess, solver.getResult().getInFact(node).get(node.getArrayAccess().getIndex()),indexVar))
                .collect(Collectors.toSet());
    }

    public void handleStoreField(StoreField storeField) {
        FieldAccess fieldAccess = storeField.getFieldAccess();
        Set<LoadField> aliasLoads = getAliasFieldLoads(fieldAccess);
        solver.getWorkList().addAll(aliasLoads);
    }

    public Value handleLoadField(LoadField loadField) {
        FieldAccess fieldAccess = loadField.getFieldAccess();
        Set<StoreField> aliasStores = getAliasStoreFields(fieldAccess);
        Value finalValue = Value.getUndef();
        for (StoreField storeField : aliasStores) {
            Var rhtVar = storeField.getRValue();
            Value storedValue = solver.getResult().getInFact(storeField).get(rhtVar);
            finalValue = cp.meetValue(finalValue, storedValue);
        }
        return finalValue;
    }
    public Value handleLoadArray(LoadArray loadArray) {
        Set<StoreArray> aliasStores = getAliasStoreArrays(loadArray);
        Value finalValue = Value.getUndef();
        for (StoreArray storeArray : aliasStores) {
            Var rhtVar = storeArray.getRValue();
            Value storedValue = solver.getResult().getInFact(storeArray).get(rhtVar);
            finalValue = cp.meetValue(finalValue, storedValue);
        }
        return finalValue;
    }
    public void handleStoreArray(StoreArray storeArray) {
        ArrayAccess arrayAccess = storeArray.getArrayAccess();
        Set<LoadArray> aliasLoads = getAliasLoadArrays(storeArray);
        solver.getWorkList().addAll(aliasLoads);
    }
    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        if (stmt instanceof StoreField storeField) {
            handleStoreField(storeField);
            return out.copyFrom(in);
        }
        else if (stmt instanceof LoadField loadField) {
            Value newValue = handleLoadField(loadField);
            CPFact newIn = in.copy();
            newIn.update(loadField.getLValue(), newValue);
            return out.copyFrom(newIn);
        }
        else if (stmt instanceof StoreArray storeArray) {
            handleStoreArray(storeArray);
            return out.copyFrom(in);
        }
        else if (stmt instanceof LoadArray loadArray) {
            Value newValue = handleLoadArray(loadArray);
            CPFact newIn = in.copy();
            newIn.update(loadArray.getLValue(), newValue);
            return out.copyFrom(newIn);
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
