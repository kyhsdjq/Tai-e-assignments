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
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.ir.exp.InvokeInstanceExp;
import pascal.taie.ir.exp.InvokeSpecial;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.collection.Pair;

import java.util.ArrayList;
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

    // TODO - finish me

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<Integer> getSinkIndexes(JMethod m) {
        Set<Integer> result = new HashSet<>();
        for (Sink sink: config.getSinks()) {
            if (sink.method().equals(m)) {
                result.add(sink.index());
            }
        }
        return result;
    }

    private Set<TaintFlow> getTaintFlows(CSCallSite csCallSite, PointerAnalysisResult PTAResult) {
        Set<TaintFlow> result = new TreeSet<>();
        Invoke callSite = csCallSite.getCallSite();
        JMethod m = callSite.getInvokeExp().getMethodRef().resolve();
        Set<Integer> indexes = getSinkIndexes(m);
        if (!indexes.isEmpty()) {
            for (Integer index: indexes) {
                Var var = callSite.getRValue().getArg(index);
                CSVar csVar = csManager.getCSVar(csCallSite.getContext(), var);
                for (CSObj csObj: PTAResult.getPointsToSet(csVar)) {
                    Obj obj = csObj.getObject();
                    if (manager.isTaint(obj)) {
                        Invoke sourceCallSite = manager.getSourceCall(obj);
                        result.add(new TaintFlow(sourceCallSite, callSite, index));
                    }
                }
            }
        }
        return result;
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();
        // TODO - finish me
        // You could query pointer analysis results you need via variable result.

        for (CSCallSite csCallSite: solver.getCSCallSites()) {
            taintFlows.addAll(getTaintFlows(csCallSite, result));
        }

        return taintFlows;
    }

    /**
     * @param callSite: callSite may be a source
     * @return null if callSite is not a source
     */
    public Obj getSourceObj(Invoke callSite) {
        JMethod m = callSite.getInvokeExp().getMethodRef().resolve();
        for (Source source: config.getSources()) {
            if (source.method().equals(m)) {
                return manager.makeTaint(callSite, source.type());
            }
        }
        return null;
    }

    /**
     * @return null if <callSite, from, to, ?> is not a transfer
     */
    private Obj getTransferObj(Invoke callSite, int from, int to, Invoke recvCallSite) {
        JMethod m = callSite.getInvokeExp().getMethodRef().resolve();
        for (TaintTransfer taintTransfer: config.getTransfers()) {
            if (taintTransfer.method().equals(m) &&
                taintTransfer.from() == from &&
                taintTransfer.to() == to
            ) {
                return manager.makeTaint(recvCallSite, taintTransfer.type());
            }
        }
        return null;
    }

    public void taintTransfer(CSVar recv, CSObj recvObj) {
        Context c = recv.getContext();

        if (manager.isTaint(recvObj.getObject())) {
            Invoke recvCallSite = manager.getSourceCall(recvObj.getObject());

            // base to result
            for (Invoke callSite: recv.getVar().getInvokes()) {
                Obj newTaintObj = getTransferObj(callSite, TaintTransfer.BASE, TaintTransfer.RESULT, recvCallSite);
                if (newTaintObj != null) {
                    Pointer ptr = csManager.getCSVar(c, callSite.getLValue());
                    CSObj csObj = csManager.getCSObj(emptyContext, newTaintObj);
                    solver.addToWorkList(ptr, csObj);
                }
            }

            // args to base / result
            for (Pair<Integer, Invoke> pair: solver.getArgToCallSiteMap().getOrDefault(recv, new ArrayList<>())) {
                Integer index = pair.first();
                Invoke callSite = pair.second();

                // args to base
                if (callSite.getRValue() instanceof InvokeInstanceExp) {
                    Obj newTaintObj = getTransferObj(callSite, index, TaintTransfer.BASE, recvCallSite);
                    if (newTaintObj != null) {
                        Pointer ptr = csManager.getCSVar(c, ((InvokeInstanceExp) callSite.getRValue()).getBase());
                        CSObj csObj = csManager.getCSObj(emptyContext, newTaintObj);
                        solver.addToWorkList(ptr, csObj);
                    }
                }

                // args to result
                Obj newTaintObj = getTransferObj(callSite, index, TaintTransfer.RESULT, recvCallSite);
                if (newTaintObj != null) {
                    Pointer ptr = csManager.getCSVar(c, callSite.getLValue());
                    CSObj csObj = csManager.getCSObj(emptyContext, newTaintObj);
                    solver.addToWorkList(ptr, csObj);
                }
            }
        }
    }
}
