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

import java.util.ArrayList;

class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {

    WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODO - finish me
        ArrayList<Node> nodeArrayList = new ArrayList<Node>();
        for (Node node: cfg) {
            if (cfg.isEntry(node)) {
                continue;
            }
            nodeArrayList.add(node);
        }
        while(!nodeArrayList.isEmpty()) {
            Node node = nodeArrayList.remove(0);
            for (Node p: cfg.getPredsOf(node)) {
                analysis.meetInto(result.getOutFact(p), result.getInFact(node));
            }
            boolean changed = analysis.transferNode(node, result.getInFact(node), result.getOutFact(node));
            if (changed) {
                nodeArrayList.addAll(cfg.getSuccsOf(node));
            }
        }
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
//        boolean changesOccur = true;
//        while(changesOccur) {
//            boolean transferRes = false;
//            for (Node node: cfg) {
//                if (cfg.isExit(node)) {
//                    continue;
//                }
//                for (Node s: cfg.getSuccsOf(node)) {
//                    analysis.meetInto(result.getInFact(s), result.getOutFact(node));
//                }
//                boolean tmpRes = analysis.transferNode(node, result.getInFact(node), result.getOutFact(node));
//                if (!transferRes && tmpRes) {
//                    transferRes = true;
//                }
//            }
//            changesOccur = transferRes;
//        }
        // TODO - finish me
        ArrayList<Node> nodeArrayList = new ArrayList<Node>();
        for (Node node: cfg) {
            if (cfg.isExit(node)) {
                continue;
            }
            nodeArrayList.add(node);
        }
        while(!nodeArrayList.isEmpty()) {
            Node node = nodeArrayList.remove(0);
            for (Node p: cfg.getSuccsOf(node)) {
                analysis.meetInto(result.getInFact(p), result.getOutFact(node));
            }
            boolean changed = analysis.transferNode(node, result.getInFact(node), result.getOutFact(node));
            if (changed) {
                nodeArrayList.addAll(cfg.getPredsOf(node));
            }
        }
    }
}
