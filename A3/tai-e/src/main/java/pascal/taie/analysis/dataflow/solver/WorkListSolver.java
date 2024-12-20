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
        // TODO - finish me

        Queue<Node> worklist = new LinkedList<>();
        for (Node node : cfg){
            worklist.add(node);
        }
        while(!worklist.isEmpty()) {
            Node node = worklist.poll();
            for (Node pred : cfg.getPredsOf(node)) {
                this.analysis.meetInto(result.getOutFact(pred), result.getInFact(node));
            }

            var inFact = result.getInFact(node);
            var outFact = result.getOutFact(node);
            boolean isChanged = this.analysis.transferNode(node, inFact, outFact);
            if (isChanged) {
                worklist.addAll(cfg.getSuccsOf(node));
            }
        }
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODO - finish me
        boolean inFactAnyChange = true;
        while(inFactAnyChange) {
            //reset flag
            inFactAnyChange = false;

            for(Node node : cfg){
                for(Node succ :cfg.getSuccsOf(node)){

                    this.analysis.meetInto(result.getInFact(succ),result.getOutFact(node));
                }
                var inFact = result.getInFact(node);
                boolean isChanged = this.analysis.transferNode(node,inFact,result.getOutFact(node));
                inFactAnyChange = inFactAnyChange || isChanged;
            }
        }
    }
}
