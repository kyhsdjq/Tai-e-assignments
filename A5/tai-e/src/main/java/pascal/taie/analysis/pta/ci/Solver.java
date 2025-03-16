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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;

import java.util.List;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        // TODO - finish me
        if (callGraph.addReachableMethod(method)) {
            for (Stmt stmt: method.getIR().getStmts()) {
                stmt.accept(stmtProcessor);
            }
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me

        @Override
        public Void visit(New stmt) {
            workList.addEntry(pointerFlowGraph.getVarPtr(stmt.getLValue()), new PointsToSet(heapModel.getObj(stmt)));
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(Copy stmt) {
            addPFGEdge(pointerFlowGraph.getVarPtr(stmt.getRValue()), pointerFlowGraph.getVarPtr(stmt.getLValue()));
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(StoreField stmt) {
            if (stmt.isStatic()) {
                addPFGEdge(
                        pointerFlowGraph.getVarPtr(stmt.getRValue()),
                        pointerFlowGraph.getStaticField(stmt.getLValue().getFieldRef().resolve())
                );
            }
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(LoadField stmt) {
            if (stmt.isStatic()) {
                addPFGEdge(
                        pointerFlowGraph.getStaticField(stmt.getRValue().getFieldRef().resolve()),
                        pointerFlowGraph.getVarPtr(stmt.getLValue())
                );
            }
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(Invoke stmt) {
            if (stmt.isStatic()) {
                JMethod method = resolveCallee(null, stmt);
                if (callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(stmt), stmt, method))) {
                    addReachable(method);
                    for (int i = 0; i < stmt.getRValue().getArgCount(); i++) {
                        // addEdge(ai, pi)
                        addPFGEdge(
                                pointerFlowGraph.getVarPtr(stmt.getRValue().getArgs().get(i)),
                                pointerFlowGraph.getVarPtr(method.getIR().getParams().get(i))
                        );
                    }
                    for (Var ret : method.getIR().getReturnVars()) {
                        // addEdge(ret, r)
                        if (stmt.getLValue() != null)
                            addPFGEdge(
                                    pointerFlowGraph.getVarPtr(ret),
                                    pointerFlowGraph.getVarPtr(stmt.getLValue())
                            );
                    }
                }
            }
            return StmtVisitor.super.visit(stmt);
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
        // TODO - finish me
        while (!workList.isEmpty()) {
            WorkList.Entry entry =  workList.pollEntry();
            Pointer ptr = entry.pointer(); PointsToSet objSet = entry.pointsToSet();

            PointsToSet deltaSet = propagate(ptr, objSet);
            if (ptr instanceof VarPtr) {
                for (Obj obj: deltaSet) {
                    Var var = ((VarPtr) ptr).getVar();

                    // x.f = y
                    for (StoreField storeField: var.getStoreFields()) {
                        // addEdge(y, o.f)
                        addPFGEdge(
                                pointerFlowGraph.getVarPtr(storeField.getRValue()),
                                pointerFlowGraph.getInstanceField(obj, storeField.getLValue().getFieldRef().resolve())
                        );
                    }

                    // y = x.f
                    for (LoadField loadField: var.getLoadFields()) {
                        // addEdge(o.f, y)
                        addPFGEdge(
                                pointerFlowGraph.getInstanceField(obj, loadField.getRValue().getFieldRef().resolve()),
                                pointerFlowGraph.getVarPtr(loadField.getLValue())
                        );
                    }

                    // x[i] = y
                    for (StoreArray storeArray: var.getStoreArrays()) {
                        // addEdge(y, o.arr)
                        addPFGEdge(
                                pointerFlowGraph.getVarPtr(storeArray.getRValue()),
                                pointerFlowGraph.getArrayIndex(obj)
                        );
                    }

                    // y = x[i]
                    for (LoadArray loadArray: var.getLoadArrays()) {
                        // addEdge(o.arr, y)
                        addPFGEdge(
                                pointerFlowGraph.getArrayIndex(obj),
                                pointerFlowGraph.getVarPtr(loadArray.getLValue())
                        );
                    }

                    processCall(var, obj);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        // deltaSet = objSet – pts(n)
        PointsToSet deltaSet = new PointsToSet();
        for (Obj obj: pointsToSet)
            if (!pointer.getPointsToSet().contains(obj))
                deltaSet.addObject(obj);

        if (!deltaSet.isEmpty()) {
            // Union
            for (Obj obj: deltaSet)
                pointer.getPointsToSet().addObject(obj);
            // Propagate
            for (Pointer ptr: pointerFlowGraph.getSuccsOf(pointer))
                workList.addEntry(ptr, deltaSet);
        }

        return deltaSet;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO - finish me
        for (Invoke callSite: var.getInvokes()) {
            JMethod method = resolveCallee(recv, callSite);
            workList.addEntry(pointerFlowGraph.getVarPtr(method.getIR().getThis()), new PointsToSet(recv));
            if (callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(callSite), callSite, method))) {
                addReachable(method);
                for (int i = 0; i < callSite.getRValue().getArgCount(); i ++) {
                    // addEdge(ai, pi)
                    addPFGEdge(
                            pointerFlowGraph.getVarPtr(callSite.getRValue().getArgs().get(i)),
                            pointerFlowGraph.getVarPtr(method.getIR().getParams().get(i))
                    );
                }
                for (Var ret: method.getIR().getReturnVars()) {
                    // addEdge(ret, r)
                    if (callSite.getLValue() != null)
                        addPFGEdge(
                                pointerFlowGraph.getVarPtr(ret),
                                pointerFlowGraph.getVarPtr(callSite.getLValue())
                        );
                }
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
