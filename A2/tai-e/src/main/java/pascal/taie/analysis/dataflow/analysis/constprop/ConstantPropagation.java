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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;
import polyglot.ast.Assign;

import java.util.List;
import java.util.Optional;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        // 空就是undefine
        List<Var> params = cfg.getIR().getParams();
        CPFact fact = new CPFact();
        for(Var item: params)
            if(ConstantPropagation.canHoldInt(item))
                fact.update(item,Value.getNAC());
        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        // 空就是undefine
        return new CPFact();
    }


    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        fact.forEach((var,value)->{
            //  如果是int我在进行meet
            if(ConstantPropagation.canHoldInt(var)) {
                Value target_value = target.get(var);
                if (target_value.isNAC())
                    target.update(var, Value.getNAC());
                if (target_value.isUndef())
                    target.update(var, value);
                if (target_value.isConstant()) {
                    int targetConstant = target_value.getConstant();
                    if (targetConstant != value.getConstant())
                        target.update(var, Value.getNAC());

                }
            }
        });
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        return null;
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        //判断是不是赋值语句
        if (stmt instanceof DefinitionStmt defStmt) {
            //判断左值是不是空的
            if (defStmt.getLValue()!=null){
                Var def_var = (Var)defStmt.getLValue();
                //判断左值是不是承载int的
                if(ConstantPropagation.canHoldInt(def_var)) {
                    // kill
                    CPFact inCopy = in.copy();
                    in.remove(def_var);

                    // gen
                    CPFact gen = new CPFact();
                    RValue rvalue = defStmt.getRValue();

                    // 分情况讨论

                    // 右值是常量
                    if (rvalue instanceof IntLiteral intliteral) {
                            gen.update(def_var, Value.makeConstant(intliteral.getValue()));
                    }
                    //右值是函数调用
                    else if (rvalue instanceof InvokeExp) {
                            gen.update(def_var,Value.getNAC());
                    }
                    //右值是一个变量
                    else if (rvalue instanceof Var var) {
                            Value temp = in.get(var);
                            gen.update(def_var,temp);
                    }
                    //右值是二元表达式
                    else if (rvalue instanceof BinaryExp bexp) {
                        Value value = evaluate(bexp, inCopy);
                        gen.update(def_var, value);
                    }
                    //其他任何情况，safe估计为NAC
                    else {
                        gen.update(def_var, Value.getNAC());
                    }

                    gen.copyFrom(in);
                    // 更新out
                    return out.copyFrom(gen);
                }
            }
        }
        return out.copyFrom(in);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // TODO - finish me
        BinaryExp bexp = (BinaryExp) exp;
        BinaryExp.Op op= bexp.getOperator();
        Var left = bexp.getOperand1();
        Var right = bexp.getOperand2();

        Value leftValue = in.get(left);
        Value rightValue = in.get(right);

        // if val(y) and val(z) are constants
        if(leftValue.isConstant() && rightValue.isConstant()){
                int leftNumber = leftValue.getConstant();
                int rightNumber = rightValue.getConstant();

                //条件运算符
                if(op instanceof ConditionExp.Op){
                    boolean flag = false;
                    if(op==ConditionExp.Op.EQ){
                        flag = leftNumber==rightNumber;
                    }
                    else if(op==ConditionExp.Op.NE){
                        flag = leftNumber!=rightNumber;
                    }
                    else if(op==ConditionExp.Op.LT){
                        flag = leftNumber<rightNumber;
                    }
                    else if(op==ConditionExp.Op.GT){
                        flag = leftNumber>rightNumber;
                    }
                    else if(op==ConditionExp.Op.LE){
                        flag = leftNumber<=rightNumber;
                    }
                    else if(op==ConditionExp.Op.GE){
                        flag = leftNumber>=rightNumber;
                    }

                    int flagInt=-1;
                    if (flag) {flagInt = 1;}
                    else{
                        flagInt=0;
                    }
                    return Value.makeConstant(flagInt);
                }

                //常规操作
                //+ - * / %
                if(op instanceof  ArithmeticExp.Op){
                    //除以0的错误
                    if((op == ArithmeticExp.Op.DIV || op == ArithmeticExp.Op.REM) && rightValue.getConstant()==0){
                        return Value.getUndef();
                    }
                    int number =-1;
                    if(op == ArithmeticExp.Op.ADD){
                        number=leftNumber+rightNumber;
                    }
                    else if(op == ArithmeticExp.Op.SUB){
                        number=leftNumber-rightNumber;
                    }
                    else if(op == ArithmeticExp.Op.MUL){
                        number=leftNumber*rightNumber;
                    }
                    else if(op == ArithmeticExp.Op.DIV){
                        number=leftNumber/rightNumber;
                    }
                    else if (op == ArithmeticExp.Op.REM){
                        number=leftNumber%rightNumber;
                    }
                    return Value.makeConstant(number);
                }

                // Shift << >> >>>
                if(op instanceof ShiftExp.Op){
                    int number = -1;
                    if (op == ShiftExp.Op.SHL){
                            number=leftNumber<<rightNumber;
                    }
                    else if(op == ShiftExp.Op.SHR){
                        number=leftNumber>>rightNumber;
                    }
                    else if(op== ShiftExp.Op.USHR){
                        number=leftNumber>>>rightNumber;
                    }
                    return Value.makeConstant(number);
                }

                // Bitwise	| & ^
                if(op instanceof BitwiseExp.Op){
                    int number = -1;
                    if (op == BitwiseExp.Op.AND){
                        number=leftNumber&rightNumber;
                    }
                    else if(op == BitwiseExp.Op.OR){
                        number=leftNumber|rightNumber;
                    }
                    else if(op == BitwiseExp.Op.XOR){
                        number=leftNumber^rightNumber;
                    }
                    return Value.makeConstant(number);
                }
            }
        // NAC / 0
        else if(rightValue.isConstant() && rightValue.getConstant()==0){
            return Value.getUndef();
        }
        // if val(y) or val(z) is NAC
        else if (leftValue.isNAC() || rightValue.isNAC()) {
            return Value.getNAC();
        }
        else{
            return Value.getUndef();
        }
        return Value.getUndef();
    }
}
