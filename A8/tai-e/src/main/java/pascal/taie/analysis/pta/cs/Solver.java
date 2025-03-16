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
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.plugin.taint.TaintAnalysiss;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import pascal.taie.util.collection.Pair;

import java.util.*;

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

    private Map<CSVar, List<Pair<Integer, Invoke>>> argToCallSiteMap;

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
        argToCallSiteMap = new HashMap<>();
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
        // TODO - finish me
        if (callGraph.addReachableMethod(csMethod)) {
            StmtProcessor stmtProcessor = new StmtProcessor(csMethod);
            for (Stmt stmt: csMethod.getMethod().getIR().getStmts()) {
                stmt.accept(stmtProcessor);
            }
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
            Obj obj = heapModel.getObj(stmt);
            Context c = contextSelector.selectHeapContext(csMethod, obj);
            workList.addEntry(csManager.getCSVar(context, stmt.getLValue()), PointsToSetFactory.make(csManager.getCSObj(c, obj)));
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(Copy stmt) {
            addPFGEdge(
                    csManager.getCSVar(context, stmt.getRValue()),
                    csManager.getCSVar(context, stmt.getLValue())
            );
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(StoreField stmt) {
            if (stmt.isStatic()) {
                addPFGEdge(
                        csManager.getCSVar(context, stmt.getRValue()),
                        csManager.getStaticField(stmt.getLValue().getFieldRef().resolve())
                );
            }
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(LoadField stmt) {
            if (stmt.isStatic()) {
                addPFGEdge(
                        csManager.getStaticField(stmt.getRValue().getFieldRef().resolve()),
                        csManager.getCSVar(context, stmt.getLValue())
                );
            }
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(Invoke stmt) {
            Context c = context;
            if (stmt.isStatic()) {
                JMethod method = resolveCallee(null, stmt);
                CSCallSite csStmt = csManager.getCSCallSite(c, stmt);

                Context ct = contextSelector.selectContext(csStmt, method);

                CSMethod csMethod = csManager.getCSMethod(ct, method);
                if (callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(stmt), csStmt, csMethod))) {
                    addReachable(csMethod);
                    for (int i = 0; i < stmt.getRValue().getArgCount(); i ++) {
                        // addEdge(ai, pi)
                        addPFGEdge(
                                csManager.getCSVar(c, stmt.getRValue().getArgs().get(i)),
                                csManager.getCSVar(ct, method.getIR().getParams().get(i))
                        );
                    }
                    for (Var ret: method.getIR().getReturnVars()) {
                        // addEdge(ret, r)
                        if (stmt.getLValue() != null)
                            addPFGEdge(
                                    csManager.getCSVar(ct, ret),
                                    csManager.getCSVar(c, stmt.getLValue())
                            );
                    }
                }
            }

            // add new taint object
            Obj sourceObj = taintAnalysis.getSourceObj(stmt);
            if (sourceObj != null) {
                Context emptyContext = contextSelector.getEmptyContext();
                CSObj taintObj = csManager.getCSObj(emptyContext, sourceObj);
                workList.addEntry(csManager.getCSVar(context, stmt.getLValue()), PointsToSetFactory.make(taintObj));
            }

            // record map from arguments to call site
            for (int i = 0; i < stmt.getRValue().getArgCount(); i ++) {
                Var arg = stmt.getRValue().getArg(i);
                CSVar csArg = csManager.getCSVar(c, arg);
                List<Pair<Integer, Invoke>> list = argToCallSiteMap.getOrDefault(csArg, new ArrayList<>());
                list.add(new Pair<>(i, stmt));
                argToCallSiteMap.put(csArg, list);
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
            if (ptr instanceof CSVar) {
                Var var = ((CSVar) ptr).getVar();
                Context c = ((CSVar) ptr).getContext();
                for (CSObj obj: deltaSet) {

                    // x.f = y
                    for (StoreField storeField: var.getStoreFields()) {
                        // addEdge(y, o.f)
                        addPFGEdge(
                                csManager.getCSVar(c, storeField.getRValue()),
                                csManager.getInstanceField(obj, storeField.getLValue().getFieldRef().resolve())
                        );
                    }

                    // y = x.f
                    for (LoadField loadField: var.getLoadFields()) {
                        // addEdge(o.f, y)
                        addPFGEdge(
                                csManager.getInstanceField(obj, loadField.getRValue().getFieldRef().resolve()),
                                csManager.getCSVar(c, loadField.getLValue())
                        );
                    }

                    // x[i] = y
                    for (StoreArray storeArray: var.getStoreArrays()) {
                        // addEdge(y, o.arr)
                        addPFGEdge(
                                csManager.getCSVar(c, storeArray.getRValue()),
                                csManager.getArrayIndex(obj)
                        );
                    }

                    // y = x[i]
                    for (LoadArray loadArray: var.getLoadArrays()) {
                        // addEdge(o.arr, y)
                        addPFGEdge(
                                csManager.getArrayIndex(obj),
                                csManager.getCSVar(c, loadArray.getLValue())
                        );
                    }

                    processCall((CSVar) ptr, obj);
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
        PointsToSet deltaSet = PointsToSetFactory.make();
        for (CSObj obj: pointsToSet)
            if (!pointer.getPointsToSet().contains(obj))
                deltaSet.addObject(obj);

        if (!deltaSet.isEmpty()) {
            // Union
            for (CSObj obj: deltaSet)
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
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        // TODO - finish me
        Context c = recv.getContext();

        for (Invoke callSite : recv.getVar().getInvokes()) {
            JMethod method = resolveCallee(recvObj, callSite);
            CSCallSite csCallSite = csManager.getCSCallSite(c, callSite);

            Context ct = contextSelector.selectContext(csCallSite, recvObj, method);

            workList.addEntry(csManager.getCSVar(ct, method.getIR().getThis()), PointsToSetFactory.make(recvObj));

            CSMethod csMethod = csManager.getCSMethod(ct, method);
            if (callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(callSite), csCallSite, csMethod))) {
                addReachable(csMethod);
                for (int i = 0; i < callSite.getRValue().getArgCount(); i++) {
                    // addEdge(ai, pi)
                    addPFGEdge(
                            csManager.getCSVar(c, callSite.getRValue().getArgs().get(i)),
                            csManager.getCSVar(ct, method.getIR().getParams().get(i))
                    );
                }
                for (Var ret : method.getIR().getReturnVars()) {
                    // addEdge(ret, r)
                    if (callSite.getLValue() != null)
                        addPFGEdge(
                                csManager.getCSVar(ct, ret),
                                csManager.getCSVar(c, callSite.getLValue())
                        );
                }
            }
        }

        taintAnalysis.taintTransfer(recv, recvObj);
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

    public Set<CSCallSite> getCSCallSites() {
        Set<CSCallSite> result = new HashSet<>();
        for (CSMethod m: callGraph.getNodes()) {
            result.addAll(callGraph.getCallSitesIn(m));
        }
        return result;
    }

    public void addToWorkList(Pointer ptr, CSObj csObj) {
        workList.addEntry(ptr, PointsToSetFactory.make(csObj));
    }

    public Map<CSVar, List<Pair<Integer, Invoke>>> getArgToCallSiteMap() {
        return argToCallSiteMap;
    }
}
