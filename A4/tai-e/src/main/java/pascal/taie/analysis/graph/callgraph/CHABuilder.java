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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.*;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }
    public Collection<JClass> getAllSubClasses(JClass clazz) {
        Set<JClass> subClasses = new HashSet<>();
        if (!clazz.isInterface()) {
            subClasses.add(clazz);
        }
        if (clazz.isInterface()) {
            for (JClass subClass : hierarchy.getDirectSubinterfacesOf(clazz)) {
                subClasses.addAll(getAllSubClasses(subClass));
            }
            for (JClass subClass : hierarchy.getDirectImplementorsOf(clazz)) {
                subClasses.addAll(getAllSubClasses(subClass));
            }
        }
        else {
            for (JClass subClass : hierarchy.getDirectSubclassesOf(clazz)) {
                subClasses.addAll(getAllSubClasses(subClass));
            }
        }
        return subClasses;
    }
    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        Queue<JMethod> worklist = new LinkedList<>();
        Set<JMethod> reachableMethods = new HashSet<>();

        while (!worklist.isEmpty()) {
            JMethod method = worklist.poll();
            if (callGraph.contains(method)) {
                continue;
            }
            callGraph.addReachableMethod(method);
            for (Invoke invoke : callGraph.getCallSitesIn(method)) {
                Set<JMethod> targets = resolve(invoke);
                for (JMethod target : targets) {
                    Edge<Invoke, JMethod> edge = new Edge<>(CallGraphs.getCallKind(invoke), invoke, target);
                    callGraph.addEdge(edge);
                    worklist.add(target);
                }
            }
        }

        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        Set<JMethod> targets = new HashSet<>();
        MethodRef caller = callSite.getMethodRef();
        JClass curClass = caller.getDeclaringClass();
        Subsignature curSubsignature = caller.getSubsignature();
        if (callSite.isStatic()) {
            JMethod curMethod = curClass.getDeclaredMethod(curSubsignature);
            if (curMethod == null) {
                throw new RuntimeException("Method not found: " + curClass.getName() + "." + curSubsignature);
            }
            targets.add(curMethod);
        }
        if (callSite.isSpecial()) {
            JMethod targetMethod = dispatch(curClass, curSubsignature);
            if (targetMethod != null) {
                targets.add(targetMethod);
            }
        }
        if (callSite.isVirtual()) {
            Set<JClass> toVisit = new HashSet<>();
            toVisit.add(curClass);
            toVisit.addAll(hierarchy.getDirectSubclassesOf(curClass));
            for (JClass clazz : toVisit) {
                JMethod method = dispatch(clazz, curSubsignature);
                if (method != null) {
                    targets.add(method);
                }
            }
        }
        return targets;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        if (jclass == null) {
            return null;
        }
        for (JMethod method : jclass.getDeclaredMethods()) {
            if (!method.isAbstract() && subsignature.equals(method.getSubsignature())) {
                return method;
            }
        }
        return dispatch(jclass.getSuperClass(), subsignature);
    }
}
