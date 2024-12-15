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

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.icfg.ICFG;
import pascal.taie.analysis.graph.icfg.ICFGEdge;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.util.collection.SetQueue;

import java.util.LinkedList;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Solver for inter-procedural data-flow analysis.
 * The workload of inter-procedural analysis is heavy, thus we always
 * adopt work-list algorithm for efficiency.
 */
// InterSolver 包装了一个算法，包括这个算法的分析器，需要的相关的数据结构包括控制流图，工作队列啥的
class InterSolver<Method, Node, Fact> {

    private final InterDataflowAnalysis<Node, Fact> analysis;

    // 这个变量是过程间控制流图
    private final ICFG<Method, Node> icfg;

    private DataflowResult<Node, Fact> result;

    private Queue<Node> workList;

    InterSolver(InterDataflowAnalysis<Node, Fact> analysis,
                ICFG<Method, Node> icfg) {
        this.analysis = analysis;
        this.icfg = icfg;
    }
    //=================================================================================
    // add by myself
    //在interconsprops里面我们会加入worklist，但是interprops里面只传递了solver，所以这里加一个接口
    public boolean addIntoWorkList(Node n) {
        return workList.add(n);
    }

    // 获得一个语句的inFact方便我们在store的时候做meetValue
    public CPFact getInFact(Stmt stmt){
        return (CPFact) result.getInFact((Node) stmt);
    }
    // end by myself
    //=================================================================================
    // 外部的程序应该调用这个函数，里面先初始化，然后解析，最终返回结果
    DataflowResult<Node, Fact> solve() {
        result = new DataflowResult<>();
        initialize();
        doSolve();
        return result;
    }
    // 处理实例字段、静态字段和数组
    private void initialize() {
        //copy from before homework
        // TODO - finish me
        //add in A7 初始化worklist
        this.workList = new LinkedList<>();

        for (Node node : icfg){
            result.setInFact(node, this.analysis.newInitialFact());
            result.setOutFact(node, this.analysis.newInitialFact());
        }
        icfg.entryMethods().forEach((method)->{
            result.setOutFact(icfg.getEntryOf(method),this.analysis.newBoundaryFact(icfg.getEntryOf(method)));
        });

    }

    private void doSolve() {
        // TODO - finish me
        for (Node node : icfg){
            workList.add(node);
        }
        while(!workList.isEmpty()) {
            Node node = workList.poll();

            for(ICFGEdge<Node> edge :icfg.getInEdgesOf(node)){
                this.analysis.meetInto(
                        analysis.transferEdge(edge,result.getOutFact(edge.getSource())),
                        result.getInFact(node)
                );
            }
            var inFact = result.getInFact(node);
            var outFact = result.getOutFact(node);
            boolean isChanged = this.analysis.transferNode(node,inFact,outFact);
            if(isChanged) {
                workList.addAll(icfg.getSuccsOf(node));
            }
        }
        }
}

