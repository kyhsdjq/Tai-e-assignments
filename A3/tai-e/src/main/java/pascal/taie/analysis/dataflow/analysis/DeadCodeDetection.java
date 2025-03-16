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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.ArrayAccess;
import pascal.taie.ir.exp.CastExp;
import pascal.taie.ir.exp.FieldAccess;
import pascal.taie.ir.exp.NewExp;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;
import pascal.taie.util.collection.Pair;
import soot.jimple.IfStmt;

import java.util.Comparator;
import java.util.Set;
import java.util.TreeSet;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me
        // Your task is to recognize dead code in ir and add it to deadCode

        Set<Stmt> reachableCode  = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        dfsCfgForReachableCode(cfg, constants, reachableCode, cfg.getEntry());
        deadCode.addAll(cfg.getNodes());
        deadCode.removeAll(reachableCode);

        Set<Stmt> deadAssign = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        for (Stmt stmt: reachableCode) {
            if (stmt instanceof AssignStmt<?,?> &&
                    hasNoSideEffect(((AssignStmt<?, ?>) stmt).getRValue()) &&
                    ((AssignStmt<?, ?>) stmt).getLValue() instanceof Var &&
                    !liveVars.getOutFact(stmt).contains((Var) ((AssignStmt<?, ?>) stmt).getLValue())) {
                deadAssign.add(stmt);
            }
        }
        deadCode.addAll(deadAssign);

        deadCode.remove(cfg.getEntry());
        deadCode.remove(cfg.getExit());

        return deadCode;
    }

    private static void dfsCfgForReachableCode(CFG<Stmt> cfg,
                                                    DataflowResult<Stmt, CPFact> constants,
                                                    Set<Stmt> reachableCode,
                                                    Stmt node) {
        reachableCode.add(node);

        if (node == cfg.getExit())
            return;

        if (node instanceof If) {
            Value conditionVal = ConstantPropagation.evaluate(((If) node).getCondition(), constants.getInFact(node));
            if (conditionVal.isConstant()) {
                if (conditionVal.getConstant() == 0) {
                    dfsSpecialEdge(cfg, constants, reachableCode, node, Edge.Kind.IF_FALSE);
                }
                else {
                    dfsSpecialEdge(cfg, constants, reachableCode, node, Edge.Kind.IF_TRUE);
                }
                return;
            }
        }
        else if (node instanceof SwitchStmt) {
            Value varVal = ConstantPropagation.evaluate(((SwitchStmt) node).getVar(), constants.getInFact(node));
            if (varVal.isConstant()) {
                for (Pair<Integer, Stmt> pair: ((SwitchStmt) node).getCaseTargets()) {
                    if (pair.first() == varVal.getConstant()) {
                        dfsCfgForReachableCode(cfg, constants, reachableCode, pair.second());
                        return;
                    }
                }
                dfsCfgForReachableCode(cfg, constants, reachableCode, ((SwitchStmt) node).getDefaultTarget());
                return;
            }
        }

        for (Stmt succ: cfg.getSuccsOf(node))
            if (!reachableCode.contains(succ))
                dfsCfgForReachableCode(cfg, constants, reachableCode, succ);
    }

    private static void dfsSpecialEdge(CFG<Stmt> cfg,
                                 DataflowResult<Stmt, CPFact> constants,
                                 Set<Stmt> reachableCode,
                                 Stmt node,
                                 Edge.Kind kind) {
        for (Edge<Stmt> edge: cfg.getOutEdgesOf(node))
            if (edge.getKind() == kind)
                if (!reachableCode.contains(edge.getTarget()))
                    dfsCfgForReachableCode(cfg, constants, reachableCode, edge.getTarget());
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
