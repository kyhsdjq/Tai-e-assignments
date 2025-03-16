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

package pascal.taie.analysis.dataflow.solver;

import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;

import java.util.LinkedList;
import java.util.Queue;

class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {

    WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODO - finish me (finished)

        Queue<Node> worklist = new LinkedList<Node>(cfg.getNodes());
        worklist.remove(cfg.getEntry());
        for (Node succ: cfg.getSuccsOf(cfg.getEntry()))
            analysis.meetInto(result.getOutFact(cfg.getEntry()), result.getInFact(succ));

        while (!worklist.isEmpty()) {
            Node BB = worklist.poll();

            if (analysis.transferNode(BB, result.getInFact(BB), result.getOutFact(BB))) {
                // OUT changed
                for (Node succ: cfg.getSuccsOf(BB)) {
                    analysis.meetInto(result.getOutFact(BB), result.getInFact(succ));
                    worklist.add(succ);
                }
            }
        }
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODO - finish me

        Queue<Node> worklist = new LinkedList<Node>(cfg.getNodes());
        worklist.remove(cfg.getExit());
        for (Node pred: cfg.getPredsOf(cfg.getExit()))
            analysis.meetInto(result.getInFact(cfg.getExit()), result.getOutFact(pred));

        while (!worklist.isEmpty()) {
            Node BB = worklist.poll();

            if (analysis.transferNode(BB, result.getInFact(BB), result.getOutFact(BB))) {
                // In changed
                for (Node pred: cfg.getPredsOf(BB)) {
                    analysis.meetInto(result.getInFact(BB), result.getOutFact(pred));
                    worklist.add(pred);
                }
            }
        }
    }
}
