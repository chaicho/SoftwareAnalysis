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

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.plugin.taint.TaintAnalysiss;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.LValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.ArrayList;
import java.util.List;

public class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private TaintAnalysiss taintAnalysis;

    private PointerAnalysisResult result;

    private List<Stmt> reachableStmts = new ArrayList<>();

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    public AnalysisOptions getOptions() {
        return options;
    }

    public ContextSelector getContextSelector() {
        return contextSelector;
    }

    public CSManager getCSManager() {
        return csManager;
    }

    void solve() {
        initialize();
        analyze();
        taintAnalysis.onFinish();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        taintAnalysis = new TaintAnalysiss(this);
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        if (callGraph.addReachableMethod(csMethod)) {
            // add method to work-list
            List<Stmt> mtdStmts = csMethod.getMethod().getIR().getStmts();
            reachableStmts.addAll(mtdStmts);
//            for (Var var: method.getIR().getVars()) {
//                pointerFlowGraph.getVarPtr(var);
//            }
            StmtProcessor stmtProcessor = new StmtProcessor(csMethod);
            mtdStmts.forEach(
                    stmt -> stmt.accept(stmtProcessor)
            );
        }
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        @Override
        public Void visit(New stmt) {
            if (stmt.getDef().isPresent()) {
                LValue def = stmt.getDef().get();
                if (def instanceof Var defVar) {
                    // TODO - finish me
                    Obj newObj = heapModel.getObj(stmt);
                    Context heapContext = contextSelector.selectHeapContext(csMethod, newObj);
                    CSObj csObj = csManager.getCSObj(heapContext, newObj);
                    PointsToSet pts = PointsToSetFactory.make(csObj);
                    workList.addEntry(csManager.getCSVar(context,defVar), pts);
                }
                else {
                    System.out.println("def is not var");
                }
            }
            else {
                System.out.println("def is not present");
            }
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            if (stmt.isStatic()) {
                Var def = stmt.getLValue();
                JMethod callee = resolveCallee(null, stmt);
                Context newContext = contextSelector.selectContext(csManager.getCSCallSite(context, stmt), callee);
                CSCallSite csStmt = csManager.getCSCallSite(newContext, stmt);
                CSMethod csCalle = csManager.getCSMethod(newContext,callee);
                if (callGraph.hasEdge(csMethod, csManager.getCSMethod(newContext, callee))) {
                    return null;
                }
                addReachable(csManager.getCSMethod(newContext, callee));
                callGraph.addEdge(new Edge(CallKind.STATIC, csStmt, csCalle));
                if (def != null) {
                    for (Var retVar : callee.getIR().getReturnVars()) {
                        if (retVar != null) {
                            addPFGEdge(csManager.getCSVar(newContext, retVar), csManager.getCSVar(context, def));
                        }
                    }
                }
                List<Var> argumentVars = stmt.getInvokeExp().getArgs();
                List<Var> paramVars = callee.getIR().getParams();
                for (int i = 0; i < argumentVars.size(); i++) {
                    Var argVar = argumentVars.get(i);
                    Var paramVar = paramVars.get(i);
                    if (argVar != null && paramVar != null) {
                        addPFGEdge(csManager.getCSVar(context,argVar), csManager.getCSVar(newContext,paramVar));
                    }
                }
            }
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            if (stmt.getRValue() != null) {
                addPFGEdge(csManager.getCSVar(context,stmt.getRValue()), csManager.getCSVar(context,stmt.getLValue()));
            }
            return null;
        }


        @Override
        public Void visit(StoreField stmt) {
            JField field = stmt.getFieldRef().resolve();
            if (field == null) {
                System.out.println("field is null");
                return null;
            } else if (field.isStatic()) {
                if (stmt.getRValue() != null) {
                    addPFGEdge(csManager.getCSVar(context,stmt.getRValue()), csManager.getStaticField(field));
                }
            }
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            JField field = stmt.getFieldRef().resolve();
            if (field == null) {
                System.out.println("field is null");
                return null;
            } else if (field.isStatic()) {
                if (stmt.getRValue() != null) {
                    addPFGEdge(csManager.getStaticField(field), csManager.getCSVar(context,stmt.getLValue()));
                }
            }
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if (pointerFlowGraph.addEdge(source, target)) {
            if (!source.getPointsToSet().isEmpty()) {
                workList.addEntry(target, source.getPointsToSet());
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            Pointer pointer = entry.pointer();
            PointsToSet pointsToSet = entry.pointsToSet();
            PointsToSet diffPointsToSet = propagate(pointer, pointsToSet);
            if (pointer instanceof CSVar varPtr) {
                Var var = varPtr.getVar();
                Context varContext = varPtr.getContext();
                for (CSObj obj : diffPointsToSet) {
                    Context objContext = obj.getContext();
                    for (LoadField loadField : var.getLoadFields()) {
                        JField field = loadField.getFieldRef().resolve();
                        Var lftVar = loadField.getLValue();
                        if (field != null) {
                            addPFGEdge(csManager.getInstanceField(obj,field), csManager.getCSVar(varContext,lftVar));
                        }
                    }
                    for (StoreField storeField : var.getStoreFields()) {
                        JField field = storeField.getFieldRef().resolve();
                        Var rhtVar = storeField.getRValue();
                        if (field != null) {
                            addPFGEdge(csManager.getCSVar(varContext,rhtVar), csManager.getInstanceField(obj, field));
                        }
                    }
                    for (LoadArray loadArray : var.getLoadArrays()) {
                        Pointer arrayIndex = csManager.getArrayIndex(obj);
                        Var lftVar = loadArray.getLValue();
                        addPFGEdge(arrayIndex, csManager.getCSVar(varContext,lftVar));
                    }
                    for (StoreArray storeArray : var.getStoreArrays()) {
                        Pointer arrayIndex = csManager.getArrayIndex(obj);
                        Var rhtVar = storeArray.getRValue();
                        addPFGEdge(csManager.getCSVar(varContext,rhtVar), arrayIndex);
                    }

                    processCall(varPtr, obj);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        PointsToSet oldPointsToSet = pointer.getPointsToSet();
        PointsToSet diffPointsToSet = PointsToSetFactory.make();

        for (CSObj obj : pointsToSet) {
            // If the points-to set of pointer changes, add pointer to work-list.
            if (oldPointsToSet.addObject(obj)) {
                diffPointsToSet.addObject(obj);
            }
        }
        if (!diffPointsToSet.isEmpty()) {
            for (Pointer successor : pointerFlowGraph.getSuccsOf(pointer)) {
                workList.addEntry(successor, diffPointsToSet);
            }
        }
        return diffPointsToSet;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        for (Invoke callSite : recv.getVar().getInvokes()) {
            Context curContext = recv.getContext();
            JMethod callee = resolveCallee(recvObj, callSite);
            CSCallSite csCallSite = csManager.getCSCallSite(curContext, callSite);
            Context newContext = contextSelector.selectContext(csCallSite, recvObj, callee);
            if (callee == null) {
                continue;
            }
            CSCallSite csCaller = csManager.getCSCallSite(curContext, callSite);
            CSMethod csCallee = csManager.getCSMethod(newContext, callee);
            CSVar calleeVar = csManager.getCSVar(newContext, callee.getIR().getThis());
            workList.addEntry(calleeVar, PointsToSetFactory.make(recvObj));
            if (!callGraph.getCalleesOf(csCaller).contains(csCallee)) {
                Edge edge = new Edge(CallGraphs.getCallKind(callSite), csCallSite, csCallee);
                callGraph.addEdge(edge);
                addReachable(csCallee);
                if (callSite.getLValue() != null) {
                    for (Var retVar : callee.getIR().getReturnVars()) {
                        if (retVar != null) {
                            addPFGEdge(csManager.getCSVar(newContext, retVar), csManager.getCSVar(curContext, callSite.getLValue()));
                        }
                    }
                }
                for (int i = 0; i < callSite.getInvokeExp().getArgs().size(); i++) {
                    Var argVar = callSite.getInvokeExp().getArgs().get(i);
                    Var paramVar = callee.getIR().getParams().get(i);
                    if (argVar != null && paramVar != null) {
                        addPFGEdge(csManager.getCSVar(curContext, argVar), csManager.getCSVar(newContext, paramVar));
                    }
                }
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    public PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
