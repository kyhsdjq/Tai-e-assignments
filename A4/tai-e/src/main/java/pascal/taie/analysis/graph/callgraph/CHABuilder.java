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
import pascal.taie.language.classes.*;

import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.Queue;
import java.util.Set;

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

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        // TODO - finish me (finished)

        Set<JMethod> worklist = new HashSet<>();
        worklist.add(entry);

        while (!worklist.isEmpty()) {
            JMethod method = worklist.iterator().next();
            worklist.remove(method);
            if (!callGraph.contains(method)) {
                callGraph.addReachableMethod(method);
                callGraph.callSitesIn(method).forEach(callSite -> {
                    Set<JMethod> T = resolve(callSite);
                    for (JMethod toMethod: T) {
                        callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(callSite) , callSite, toMethod));
                        worklist.add(toMethod);
                    }
                });
            }
        }

        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me (finished)

        Set<JMethod> T = new HashSet<>();
        MethodRef methodRef = callSite.getMethodRef();
        JClass declaringClass = methodRef.getDeclaringClass();
        Subsignature subsignature = methodRef.getSubsignature();

        if (callSite.isStatic()) {
            T.add(declaringClass.getDeclaredMethod(subsignature));
        }
        else if (callSite.isSpecial()) {
            T.add(dispatch(declaringClass, subsignature));
        }
        else if (callSite.isVirtual() || callSite.isInterface()) {
            T.addAll(resolveFromClass(declaringClass, subsignature));
        }

        T.remove(null);

        return T;
    }

    private Set<JMethod> resolveFromClass(JClass rootClass, Subsignature subsignature) {
        Set<JMethod> T = new HashSet<>();
        T.add(dispatch(rootClass, subsignature));
        if (rootClass.isInterface()) {
            for (JClass subclass: hierarchy.getDirectSubinterfacesOf(rootClass)) {
                T.addAll(resolveFromClass(subclass, subsignature));
            }
            for (JClass subclass: hierarchy.getDirectImplementorsOf(rootClass)) {
                T.addAll(resolveFromClass(subclass, subsignature));
            }
        }
        else {
            for (JClass subclass: hierarchy.getDirectSubclassesOf(rootClass)) {
                T.addAll(resolveFromClass(subclass, subsignature));
            }
        }
        return T;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me (finished)

        if (jclass == null)
            return null;

        JMethod localMethod = jclass.getDeclaredMethod(subsignature);
        if (localMethod != null && !localMethod.isAbstract())
            return localMethod;
        else
            return dispatch(jclass.getSuperClass(), subsignature);
    }
}
