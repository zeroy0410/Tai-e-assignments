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

import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Stream;

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
        // TODO - finish me
        ArrayDeque<JMethod> worklist = new ArrayDeque<JMethod>();
        worklist.addLast(entry);
        while(!worklist.isEmpty()) {
            JMethod m = worklist.pollFirst();
            if(!callGraph.contains(m)) {
                callGraph.addReachableMethod(m);
                Stream<Invoke> call_sites = callGraph.callSitesIn(m);
                call_sites.forEach(cs -> {
                    for (JMethod targetMethod : resolve(cs)) {
                        if (targetMethod != null) {
                            callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(cs), cs, targetMethod));
                            worklist.addLast(targetMethod);
                        }
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
        // TODO - finish me
        Set<JMethod> answer = new HashSet<>();
        MethodRef method_ref = callSite.getMethodRef();
        CallKind call_kind = CallGraphs.getCallKind(callSite);
        Subsignature subsignature = method_ref.getSubsignature();
        JClass declaring_class = method_ref.getDeclaringClass();
        switch (call_kind) {
            case STATIC -> {
                answer.add(declaring_class.getDeclaredMethod(subsignature));
                break;
            }
            case SPECIAL -> {
                answer.add(dispatch(declaring_class, subsignature));
                break;
            }
            case VIRTUAL, INTERFACE -> {
                ArrayDeque<JClass> subclasses = new ArrayDeque<>();
                HashSet<JClass> set = new HashSet<>();
                subclasses.addLast(declaring_class);
                set.add(declaring_class);
                while (!subclasses.isEmpty()) {
                    JClass subclass = subclasses.pollFirst();
                    answer.add(dispatch(subclass, subsignature));
                    for (JClass jClass : (hierarchy.getDirectSubclassesOf(subclass))) {
                        if (!set.contains(jClass)) {
                            set.add(jClass);
                            subclasses.addLast(jClass);
                        }
                    }
                    for (JClass jClass : (hierarchy.getDirectSubinterfacesOf(subclass))) {
                        if (!set.contains(jClass)) {
                            set.add(jClass);
                            subclasses.addLast(jClass);
                        }
                    }
                    for (JClass jClass : (hierarchy.getDirectImplementorsOf(subclass))) {
                        if (!set.contains(jClass)) {
                            set.add(jClass);
                            subclasses.addLast(jClass);
                        }
                    }
                }
                break;
            }
        }
        return answer;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
        if(jclass == null)
            return null;
        if(jclass.getDeclaredMethod(subsignature) != null && !jclass.getDeclaredMethod(subsignature).isAbstract()) {
            return jclass.getDeclaredMethod(subsignature);
        }
        else {
            return dispatch(jclass.getSuperClass(), subsignature);
        }
    }
}
