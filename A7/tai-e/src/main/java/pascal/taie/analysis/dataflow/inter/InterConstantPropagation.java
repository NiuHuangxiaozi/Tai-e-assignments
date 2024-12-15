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

import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JMethod;

import java.util.*;

import pascal.taie.language.classes.JField;
/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;


    //add by myself
    PointerAnalysisResult pta = null;
    Map<Obj,Value> objJFieldMap = null;

    // ===============================================================================
    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        this.pta = World.get().getResult(ptaId);
        // You can do initialization work here

        // 初始化一个map存储Obj到领域Field的映射
        objJFieldMap = new HashMap<>();
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        return out.copyFrom(in);
    }
    //==================================================================================================================
    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        // 为了不破坏原来过程内常量分析的封装，
        // 我们这里判断一下这个语句是不是 实例字段和静态字段；还有数组
        // 如果不是我们这次实验处理的语句就交给原来的常量分析

        // 实例字段
        if (stmt instanceof StoreField storeField){
            StoreField_transferNonCallNode(storeField, in, out);
        }
        else if(stmt instanceof LoadField loadField){
            return LoadField_transferNonCallNode(loadField, in, out);
        }
        //数组
        else if(stmt instanceof StoreArray storeArray){
            StoreArray_transferNonCallNode(storeArray, in, out);
        }
        else if(stmt instanceof LoadArray loadArray){
            return LoadArray_transferNonCallNode(loadArray, in, out);
        }
        return cp.transferNode(stmt, in, out);
    }


    // 判断是不是别名 ====================================================================================================
    //判断静态字段是否是别名，直接看是不是一类的
    boolean staticIsAlias(FieldAccess s1, FieldAccess s2) {
        return s1.getFieldRef().equals(s2.getFieldRef());
    }
    //判断实例字段是否是别名。
    boolean isAlias(InstanceFieldAccess s1, InstanceFieldAccess s2) {
        Var base1 = s1.getBase();
        Set<Obj> s1ObjSet = this.pta.getPointsToSet(base1);
        JField s1_f = s1.getFieldRef().resolve();

        Var base2 = s2.getBase();
        Set<Obj> s2ObjSet = this.pta.getPointsToSet(base2);
        JField s2_f = s2.getFieldRef().resolve();

        // 两个互为别名，就是指针集有交集以及field是一样的
        Set<Obj> intersection = new HashSet<>(s1ObjSet);
        intersection.retainAll(s2ObjSet);

        return (!intersection.isEmpty()) && s1_f.equals(s2_f);
    }
    boolean ArrayIsAlias(ArrayAccess a1, ArrayAccess a2, Value index1value, Value index2value) {
        // a1 是 m[i] , a2 是 n[j]

        // 查看m和n的指针集合是否有交集
        Var m = a1.getBase();
        Var n = a2.getBase();

        Set<Obj> mObjs = this.pta.getPointsToSet(m);
        Set<Obj> nObjs = this.pta.getPointsToSet(n);

        Set<Obj> intersection = new HashSet<>(mObjs);
        intersection.retainAll(nObjs);
        if (intersection.isEmpty()) return false;

        //查看index是不是一样的，使用常量分析

        if(index1value.isUndef() || index2value.isUndef()){
            return false;
        }
        else if(index1value.isConstant() &&
                index2value.isConstant() &&
                index1value.getConstant() == index2value.getConstant() ){
            return true;
        }
        else if(index1value.isNAC() || index2value.isNAC()){
            return true;
        }
        else
            return false;
    }
    // 判断是不是别名 ====================================================================================================

    // 下面处理本次实验的四种语句 ==========================================================================================
    // LoadField : y = x.f
    private boolean LoadField_transferNonCallNode(LoadField loadField, CPFact in, CPFact out){
        // 分为静态和动态
        //y = T.f
        if(loadField.isStatic()){
            Value targetValue = Value.getUndef();
            CPFact newOut = in.copy();
            for(Stmt stmt : icfg){
                if(stmt instanceof StoreField storeField && storeField.isStatic()){
                    FieldAccess loadFieldAccess = loadField.getFieldAccess();
                    FieldAccess storeFieldAccess = storeField.getFieldAccess();

                    if(staticIsAlias(loadFieldAccess,storeFieldAccess)){

                        RValue rvalue = storeField.getRValue();
                        CPFact storeIn = this.solver.getInFact(storeField);
                        //求出 T.f的值
                        Value currentValue = storeIn.get((Var) rvalue);
                        targetValue = cp.meetValue(targetValue,currentValue);
                    }
                }
            }

            Var lvar = loadField.getLValue();
            newOut.update(lvar,targetValue);
            return out.copyFrom(newOut);
        }
        // y = t.f
        else
        {
            //TODO : finish the
            Value targetValue = Value.getUndef();
            CPFact newOut = in.copy();
            // 找出所有的store语句(o.f = k)
            for (Stmt stmt : icfg){
                if(stmt instanceof StoreField storeField && (!storeField.isStatic())){
                    InstanceFieldAccess loadFieldAccess = (InstanceFieldAccess) loadField.getFieldAccess();
                    InstanceFieldAccess storeFieldAccess = (InstanceFieldAccess) storeField.getFieldAccess();

                    // 判断是不是互为别名
                    if(isAlias(loadFieldAccess,storeFieldAccess)){

                        //store语句上下文的in
                        CPFact storeIn = this.solver.getInFact(storeField);
                        //k
                        RValue rvalue = storeField.getRValue();
                        Value currentValue = storeIn.get((Var) rvalue);
                        targetValue = cp.meetValue(targetValue,currentValue);
                    }
                }
            }

            Var lvar = loadField.getLValue();
            newOut.update(lvar,targetValue);
            return out.copyFrom(newOut);
        }
    }

    // StoreField :  x.f = y;
    private void StoreField_transferNonCallNode(StoreField storeFieldStmt, CPFact in, CPFact out) {
        // 分为静态的store和动态的store
        // T.f = y
        //如果改变了T.f的值，那么我们就要寻找x = T.f的表达式, store 找 load
        if (storeFieldStmt.isStatic()) {
            FieldAccess curField = storeFieldStmt.getFieldAccess();
            for (Stmt stmt : icfg) {
                if (stmt instanceof LoadField loadField &&
                        loadField.isStatic() &&
                        staticIsAlias(curField, loadField.getFieldAccess())) {
                    this.solver.addIntoWorkList(stmt);
                }
            }
        }

        // t.f = y
        // 我们将t.f的load语句全部加入worklist，因为右边是y所以我们不需要指针分析
        //同时将evaluate(y) 加入 objJFieldMap字典，方便loadstmt的时候处理
        else if (storeFieldStmt.getFieldAccess() instanceof InstanceFieldAccess instanceFieldAccess) {

            // 找出所有与t.f是别名的load语句加入到worklist当中去(z = t.f)
            for (Stmt stmt : icfg) {
                if (stmt instanceof LoadField loadField && (!loadField.isStatic()) &&
                        loadField.getFieldAccess() instanceof InstanceFieldAccess otherInstanceFieldAccess) {
                    //判断是不是别名
                    if (isAlias(instanceFieldAccess, otherInstanceFieldAccess)) {
                        this.solver.addIntoWorkList(stmt);
                    }
                }
            }
        }
        else
            assert false;
    }
    // k = a[i]
    public boolean LoadArray_transferNonCallNode(LoadArray loadArray, CPFact in, CPFact out) {
        //找到所有storeArray的句子，求出右值，然后meet出新的值，最终传给k

        ArrayAccess curArray = loadArray.getArrayAccess();
        Var curIndex = curArray.getIndex();
        Value curIndexValue = in.get(curIndex);

        Value targetValue = Value.getUndef();
        CPFact newOut = in.copy();
        for(Stmt stmt : icfg){
            if(stmt instanceof StoreArray storeArray){
                CPFact storeIn = this.solver.getInFact(storeArray);
                ArrayAccess otherArray = storeArray.getArrayAccess();
                Var otherIndex = otherArray.getIndex();

                Value otherIndexValue = storeIn.get(otherIndex);

                //判断是不是别名 o[i] =m
                if(ArrayIsAlias(curArray,otherArray,curIndexValue,otherIndexValue)){
                    //求出m的值，然后meet
                    RValue rvalue = storeArray.getRValue();
                    Value currentValue = storeIn.get((Var) rvalue);
                    targetValue = cp.meetValue(targetValue,currentValue);
                }

            }
        }

        Var lvar = loadArray.getLValue();
        newOut.update(lvar,targetValue);
        return out.copyFrom(newOut);

    }
    // a[i] = k
    public void StoreArray_transferNonCallNode(StoreArray storeArray, CPFact in, CPFact out){
        ArrayAccess curArray = storeArray.getArrayAccess();
        Var curIndex = curArray.getIndex();
        Value curIndexValue = in.get(curIndex);

        for (Stmt stmt : icfg) {
            if (stmt instanceof LoadArray loadArray ){
                CPFact otherIn = this.solver.getInFact(loadArray);

                ArrayAccess otherArray = loadArray.getArrayAccess();
                Var otherIndex = otherArray.getIndex();

                Value otherIndexValue = otherIn.get(otherIndex);

                // 判断是不是别名
                if(ArrayIsAlias(curArray,otherArray,curIndexValue,otherIndexValue)){
                    this.solver.addIntoWorkList(stmt);
                }
            }
        }
    }

    // 下面处理本次实验的四种语句 ==========================================================================================



    boolean fieldmeet(Obj obj, Value value){
        if(objJFieldMap.containsKey(obj)){
            //已经存在这个obj
            Value newValue = cp.meetValue(value, objJFieldMap.get(obj));
            objJFieldMap.put(obj, newValue);
            return newValue.equals(value);
        }
        else{
            //这个obj不存在
            objJFieldMap.put(obj, value);
            return true;
        }
    }
    // end add by myself
    //==================================================================================================================



    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        return out.copy();
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        //首先我们得拿到调用点那一处的调用语句，拿到左值
        if(edge.getSource().getDef().isPresent()){
            Var lvalue = (Var) edge.getSource().getDef().get();
            out.remove(lvalue);
            return out.copy();
        }
        else {
            // 没有左值，直接传播
            return out.copy();
        }
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me
        //获取这个函数的参数名字列表
        List<Var> methodParams = edge.getCallee().getIR().getParams();
        List<RValue> rvalueList =edge.getSource().getUses();

        //创建一个空的CPFact
        CPFact methodInputFact = new CPFact();

        for(RValue rvalue : rvalueList) {
            if (rvalue instanceof InvokeExp invokeExp) {
                List<Var> methodArguments = invokeExp.getArgs();
                for (int index = 0; index < methodArguments.size(); index++) {
                    methodInputFact.update(methodParams.get(index), callSiteOut.get(methodArguments.get(index)));
                }
            }
        }
        return methodInputFact;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // TODO - finish me
        //创建一个空的CPFact
        CPFact methodInputFact = new CPFact();
        //
        if(edge.getCallSite().getDef().isPresent()){

            // 拿到对应的左值
            Optional<LValue> lvalue = edge.getCallSite().getDef();
            Var lvar = (Var)lvalue.get();
            Iterator<Var> iterator = edge.getReturnVars().iterator();

            // 但是有可能returnOut有很多的值，我们调用过程内常量传播进行合并,把调用的这个函数看作过程内
            assert iterator.hasNext();
            Var finalVar = iterator.next();
            Value finalValue=returnOut.get(finalVar);
            for(Var newVar : edge.getReturnVars()) {
                finalValue = cp.meetValue(returnOut.get(newVar), finalValue);
            }

            //
            methodInputFact.update(lvar, finalValue);
            return methodInputFact;
        }
        else{
            //没有左值，所以传一个空的回来
            return methodInputFact;
        }
    }
}
