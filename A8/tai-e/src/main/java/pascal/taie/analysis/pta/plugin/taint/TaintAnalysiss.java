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

package pascal.taie.analysis.pta.plugin.taint;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraph;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.HashSet;
import java.util.Set;
import java.util.TreeSet;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);
    }

    public Set<TaintTransfer> getTaintTransfers(CSMethod method) {
        Set<TaintTransfer> taintTransfers = new HashSet<>();
        for (TaintTransfer transfer : config.getTransfers()) {
            if (transfer.method().equals(method.getMethod())) {
                taintTransfers.add(transfer);
            }
        }
        return taintTransfers;
    }
    public Set<Type> getTaintTypes(CSMethod method) {
        Set<Type> taintTypes = new HashSet<>();
        for (Source source : config.getSources()) {
            if (source.method().equals(method.getMethod())) {
                taintTypes.add(source.type());
            }
        }
        return taintTypes;
    }

    public Set<Obj> initializeTaintObjs(Invoke callSite, CSMethod callee) {
        Set<Type> taintTypes = getTaintTypes(callee);
        Set<Obj> taintObjs = new HashSet<>();
        for (Type type : taintTypes) {
            taintObjs.add(manager.makeTaint(callSite, type));
        }
        return taintObjs;
    }

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }
    public boolean isSink(CSMethod method) {
        for (Sink sink : config.getSinks()) {
            if (sink.method().equals(method.getMethod())) {
                return true;
            }
        }
        return false;
    }
    public Set<Integer> getSensitiveIndices(CSMethod method) {
        Set<Integer> sensitiveIndices = new TreeSet<>();
        for (Sink sink : config.getSinks()) {
            if (sink.method().equals(method.getMethod())) {
                sensitiveIndices.add(sink.index());
            }
        }
        return sensitiveIndices;
    }
    public Set<Obj> getTaintObjsInPointsToSet(Pointer pointer) {
        if (pointer == null) {
            return new HashSet<>();
        }
        Set<Obj> taintObjs = new HashSet<>();
        for (CSObj csObj : pointer.getPointsToSet()) {
            Obj obj = csObj.getObject();
            if (manager.isTaint(obj)) {
                taintObjs.add(obj);
            }
        }
        return taintObjs;
    }
    public void handleTaintTransfer(Invoke invoke, CSMethod callee, CSVar recVar, CSVar lftVar) {
        Context curContext = recVar == null ? emptyContext : recVar.getContext();
        Set<TaintTransfer> taintTransfers = getTaintTransfers(callee);
        // Handle taint analysis
        if (lftVar != null) {
            Set<Obj> taintObjs = initializeTaintObjs(invoke, callee);
            for (Obj taintObj : taintObjs) {
                solver.addToWorkList(lftVar, taintObj);
            }
        }

        for (TaintTransfer transfer : taintTransfers) {
            int from = transfer.from();
            int to = transfer.to();
            Pointer fromVar;
            Pointer toVar;
            if (from == TaintTransfer.BASE) {
                fromVar = recVar;
            }
            else {
                fromVar = csManager.getCSVar(curContext, invoke.getInvokeExp().getArg(from));
            }
            if (to == TaintTransfer.RESULT) {
                toVar = csManager.getCSVar(curContext, invoke.getLValue());
            }
            else {
                toVar = recVar;
            }
            if (fromVar == null || toVar == null) {
                continue;
            }
            Set<Obj> taintSourceObjs = getTaintObjsInPointsToSet(fromVar);
            solver.addPFGEdge(fromVar, toVar);
            for (Obj taintSourceObj : taintSourceObjs) {
                if (manager.isTaint(taintSourceObj)) {
                    Invoke sourceCall = manager.getSourceCall(taintSourceObj);
                    Obj taintObj = manager.makeTaint(sourceCall, transfer.type());
                    solver.addToWorkList(toVar, taintObj);
                }
            }
        }
    }
    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();
        // TODO - finish me
        // You could query pointer analysis results you need via variable result.
        CallGraph<CSCallSite, CSMethod> callGraph = result.getCSCallGraph();
        for (CSMethod method : callGraph.getNodes()) {
            if (isSink(method)) {
                Set<CSCallSite> callSites = callGraph.getCallersOf(method);
                for (CSCallSite callSite : callSites) {
                    Context context = callSite.getContext();
                    JMethod caller = callSite.getCallSite().getContainer();
                    Set<Integer> sensitiveIndices = getSensitiveIndices(method);
                    for (int i : sensitiveIndices) {
                        Invoke invoke = callSite.getCallSite();
                        Var argument = invoke.getInvokeExp().getArg(i);
                        Set<CSObj> pts = result.getPointsToSet(csManager.getCSVar(context,argument));
                        for (CSObj csObj : pts) {
                            Obj obj = csObj.getObject();
                            if (manager.isTaint(obj)) {
                                Invoke sourceCall = manager.getSourceCall(obj);
                                taintFlows.add(new TaintFlow(sourceCall, invoke, i));
                            }
                        }
                    }
                }
            }
        }
        return taintFlows;
    }
    public boolean isTaint(CSObj csObj) {
        return manager.isTaint(csObj.getObject());
    }

}
