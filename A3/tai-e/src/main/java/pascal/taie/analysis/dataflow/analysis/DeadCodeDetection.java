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
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }


    /*
      如果不在reach集合里面，说明没有分析过，就添加到queue里面
     */
    private final void addQueue(Set<Stmt> reach,Queue<Stmt> queue,Stmt stmt){
        if(!reach.contains(stmt)){
            queue.add(stmt);
        }
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

        /*
        ============================================================
            1. control-flow unreachable code
        ============================================================
        */
        //定义字典
        Map<Stmt, Boolean> dictionary = new HashMap<>();

        // 深度优先或者广度优先，我们选择广度优先，访问到的标记为True
        Set<Stmt> reach = new HashSet<>();
        Queue<Stmt> queue = new LinkedList<>();

        //初始化
        queue.add(cfg.getEntry());

        while (!queue.isEmpty()) {

            Stmt stmt = queue.remove();

            //表示这个节点已经被分析过了
            reach.add(stmt);

            if(stmt instanceof DefinitionStmt<?,?>){
                if (stmt instanceof AssignStmt<?,?>){
                    SetFact<Var> future = liveVars.getOutFact(stmt);
                    // 判断左值存不存在
                    if(stmt.getDef().isPresent() && stmt.getDef().get() instanceof Var leftvar){
                        //是活跃变量，则不删除，设置为True
                        if(future.contains(leftvar)){
                            dictionary.put(stmt, true);
                        }
                    }
                    else{
                        //没有左值，直接添加
                        dictionary.put(stmt, true);
                    }
                }
//                else if(stmt instanceof Invoke){
//                    RValue rvalue = ((Invoke) stmt).getRValue();
//                    LValue lvalue = ((Invoke) stmt).getLValue();
//                    SetFact<Var> future = liveVars.getOutFact(stmt);
//
//                    if(hasNoSideEffect(rvalue)){
//                        if(lvalue instanceof Var lvar && future.contains(lvar)){
//                            dictionary.put(stmt, true);
//                        }
//                    }
//                    else{
//                        dictionary.put(stmt, true);
//                    }
//                }
                else{
                    //其他DefinitionStmt不要消除
                    dictionary.put(stmt, true);
                }

                for(Stmt succStmt : cfg.getSuccsOf(stmt))
                    addQueue(reach,queue,succStmt);
            }
            else if(stmt instanceof If ){
                Set<Edge<Stmt>> succEdges = cfg.getOutEdgesOf(stmt);

                CPFact consHistory = constants.getInFact(stmt);

                ConditionExp condition = ((If)stmt).getCondition();

                Var ope1=condition.getOperand1();
                Var ope2=condition.getOperand2();
                ConditionExp.Op operator = condition.getOperator();

                if(consHistory.get(ope1).isConstant() && consHistory.get(ope2).isConstant()){

                    ConditionExp.Op op = condition.getOperator();
                    int leftNumber = consHistory.get(ope1).getConstant();
                    int rightNumber = consHistory.get(ope2).getConstant();
                    boolean flag =false;
                    switch(op){
                        case EQ:
                            flag = leftNumber==rightNumber;
                            break;
                        case NE:
                            flag = leftNumber!=rightNumber;
                            break;
                        case LT:
                            flag = leftNumber<rightNumber;
                            break;
                        case GT:
                            flag = leftNumber>rightNumber;
                            break;
                        case LE:
                            flag = leftNumber<=rightNumber;
                            break;
                        case GE:
                            flag = leftNumber>=rightNumber;
                            break;
                        default:
                            assert false;
                    }

                    // IF_TRUE、IF_FALSE
                    for(Edge edge : succEdges){
                        if (edge.getKind() == Edge.Kind.IF_TRUE && flag) {
                            addQueue(reach,queue,(Stmt) edge.getTarget());
                            dictionary.put(stmt, true);
                            break;
                        }
                        if(edge.getKind() == Edge.Kind.IF_FALSE && !flag){
                            addQueue(reach,queue,(Stmt) edge.getTarget());
                            dictionary.put(stmt, true);
                            break;
                        }
                    }
                }
                else{

                    dictionary.put(stmt, true);
                    for(Stmt succStmt : cfg.getSuccsOf(stmt)){
                        addQueue(reach,queue,succStmt);
                    }
                }
            }
            else if(stmt instanceof SwitchStmt){
                Var var = ((SwitchStmt) stmt).getVar();
                CPFact history = constants.getInFact(stmt);

                if(history.get(var).isConstant()){
                    int switchNumbetr = history.get(var).getConstant();
                    Set<Edge<Stmt>> succEdges = cfg.getOutEdgesOf(stmt);
                    boolean findCase = false;
                    for(Edge<Stmt> edge : succEdges){
                        if (edge.getKind() == Edge.Kind.SWITCH_CASE && switchNumbetr == edge.getCaseValue()){
                            dictionary.put(stmt, true);
                            findCase=true;
                            addQueue(reach,queue,(Stmt) edge.getTarget());
                            if(stmt.canFallThrough()){
                                for(Stmt succStmt: cfg.getSuccsOf(edge.getTarget())){
                                    addQueue(reach,queue,succStmt);
                                }
                            }
                            break;
                        }
                    }
                    //走default
                    if(!findCase){
                        Stmt defaultTarget = ((SwitchStmt) stmt).getDefaultTarget();
                        addQueue(reach,queue,defaultTarget);
                        dictionary.put(stmt, true);
                    }
                }
                else{
                    //不是常量，全部添加
                    dictionary.put(stmt, true);
                    //这里感觉遍历switchcase和直接遍历所有的后继是一样的
                    for(Stmt succStmt : cfg.getSuccsOf(stmt)){
                        addQueue(reach,queue,succStmt);
                    }
                }
            }
            else{
                //表示普通的语句，设置为True并且添加所有后继
                dictionary.put(stmt, true);
                for(Stmt succStmt : cfg.getSuccsOf(stmt)){
                    addQueue(reach,queue,succStmt);
                }
            }
        }
        for(Stmt stmt : ir.getStmts()){
            if(!dictionary.containsKey(stmt)){
                deadCode.add(stmt);
            }
        }
        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    // 给定一个右值，判断右值有没有副作用
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
