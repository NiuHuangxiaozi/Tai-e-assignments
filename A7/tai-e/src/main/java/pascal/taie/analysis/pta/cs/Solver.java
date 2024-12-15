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
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.List;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    void solve() {
        initialize();
        analyze();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
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
        /*
        1. 不要忘记在该方法中处理静态字段 loads/stores 和静态方法调用。
        2. 使用Solver.resolveCallee来解析被调用者
        3. 使用访问者模式处理不同种类的语句
         */
        if(!callGraph.contains(csMethod)){

            callGraph.addReachableMethod(csMethod);

            List<Stmt> S_m = csMethod.getMethod().getIR().getStmts();
            //构建 StmtProcessor
            StmtProcessor stmtProcessor = new StmtProcessor(csMethod);

            //遍历新的代码块S_m
            for(Stmt s : S_m){
                s.accept(stmtProcessor);
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

        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me

        // x = new T()
        @Override
        public Void visit(New stmt) {
            Var x = stmt.getLValue();
            CSVar c_x = csManager.getCSVar(this.context,x);

            Obj oi = heapModel.getObj(stmt);
            Context newcontext = contextSelector.selectHeapContext(csMethod,oi);
            CSObj c_oi = csManager.getCSObj(newcontext,oi);

            PointsToSet ptr_set = PointsToSetFactory.make(c_oi);
            workList.addEntry(c_x, ptr_set);
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {

            if (stmt.isStatic()) {
                JMethod m = resolveCallee(null, stmt);
                CSCallSite csCallsite =  csManager.getCSCallSite(this.context,stmt);

                Context c_t = contextSelector.selectContext(csCallsite,m);


                // 开始连接一条边，我们写出source和target看一下它在不在
                CSMethod source = csManager.getCSMethod(this.context, stmt.getContainer());
                CSMethod target = csManager.getCSMethod(c_t,m);
                CallKind invokeKind = CallGraphs.getCallKind(stmt);

                if(callGraph.addEdge(new Edge<>(invokeKind,csCallsite,target))){
                    //调用图需要多个种类
                    // INTERFACE、VIRTUAL、SPECIAL 和 STATIC
                    addReachable(target);

                    List<Var> args = stmt.getRValue().getArgs();
                    List<Var> params = m.getIR().getParams();

                    for(int index = 0; index < params.size(); index++){
                        CSVar arg = csManager.getCSVar(this.context,args.get(index));
                        CSVar param = csManager.getCSVar(c_t, params.get(index));
                        addPFGEdge(arg, param);
                    }

                    // 返回值的add edge
                    if(stmt.getLValue() != null) {
                        //返回值接受
                        CSVar receiver = csManager.getCSVar(this.context,stmt.getLValue());

                        //返回值送出
                        List<Var> returnables = m.getIR().getReturnVars();
                        for(Var returnvar: returnables){
                            CSVar sender = csManager.getCSVar(c_t,returnvar);
                            addPFGEdge(sender, receiver);
                        }
                    }

                }
            }
            return null;
        }




        // 处理 a = b
        @Override
        public Void visit(Copy stmt) {
            Pointer source = csManager.getCSVar(this.context,stmt.getRValue());
            Pointer target = csManager.getCSVar(this.context,stmt.getLValue());
            addPFGEdge(source, target);
            return null;
        }


        @Override
        public Void visit(LoadField stmt) {
            //分为静态和非静态
            if (stmt.isStatic()) {
                //y = T.f
                CSVar y = csManager.getCSVar(this.context,stmt.getLValue());
                JField f = stmt.getFieldRef().resolve();
                StaticField T_f = csManager.getStaticField(f);
                addPFGEdge(T_f, y);
            } else {
                // 在analyze里面已经处理过了
                return null;
            }
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            if (stmt.isStatic()) {
                //T.f = y
                CSVar y = csManager.getCSVar(this.context,stmt.getRValue());
                JField f = stmt.getFieldRef().resolve();
                StaticField T_f = csManager.getStaticField(f);
                addPFGEdge(y, T_f);
            } else {
                // 在analyze里面已经处理过了
                return null;
            }
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    // 完成
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if(pointerFlowGraph.addEdge(source, target)) {
            if (!source.getPointsToSet().isEmpty()){
                workList.addEntry(target,source.getPointsToSet());
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    // 完成
    private void analyze() {
        // TODO - finish me
        while (!workList.isEmpty()) {
            // 返回指针和调用点集合
            WorkList.Entry curPair=workList.pollEntry();
            Pointer n = curPair.pointer();
            PointsToSet pts = curPair.pointsToSet();

            // combine two steps ：diff and 将pts传播到pt(n)中
            PointsToSet delta = propagate(n, pts);

            // if n represent a variable x then
            if(n instanceof CSVar csvar){
                assert delta != null;
                for(CSObj cs_obj : delta){

                    // 1 . store and load stmts
                    List<StoreField> storeStmts = csvar.getVar().getStoreFields();
                    List<LoadField> loadStmts = csvar.getVar().getLoadFields();
                    List<StoreArray> storeArrays = csvar.getVar().getStoreArrays();
                    List<LoadArray> loadArrays = csvar.getVar().getLoadArrays();


                    // 2. x.f = y process store
                    for(StoreField storeStmt : storeStmts){
                        CSVar y = csManager.getCSVar(csvar.getContext(),storeStmt.getRValue());
                        JField f = storeStmt.getFieldRef().resolve();
                        InstanceField x_f = csManager.getInstanceField(cs_obj,f);
                        addPFGEdge(y,x_f);
                    }

                    // 3. y = x.f process load
                    for(LoadField loadStmt : loadStmts){
                        CSVar y = csManager.getCSVar(csvar.getContext(),loadStmt.getLValue());
                        JField f = loadStmt.getFieldRef().resolve();
                        InstanceField x_f = csManager.getInstanceField(cs_obj,f);
                        addPFGEdge(x_f,y);
                    }

                    // 4. 数组的store x[i] = y
                    for(StoreArray storeArray :storeArrays){
                        CSVar y = csManager.getCSVar(csvar.getContext(),storeArray.getRValue());
                        ArrayIndex xi =csManager.getArrayIndex(cs_obj);
                        addPFGEdge(y,xi);
                    }

                    // 5. 数组的load y = x[i]
                    for(LoadArray loadArray :loadArrays){
                        CSVar y = csManager.getCSVar(csvar.getContext(),loadArray.getLValue());
                        ArrayIndex xi = csManager.getArrayIndex(cs_obj);
                        addPFGEdge(xi,y);
                    }

                    // processCall
                    processCall(csvar,cs_obj);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    // 完成
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
         /*
            pointer ：n
            pointsToSet ：pts
         */
        // delta = pts-pt(n)
        PointsToSet delta = PointsToSetFactory.make();
        for(var pt: pointsToSet){
            if(!pointer.getPointsToSet().contains(pt)){
                delta.addObject(pt);
            }
        }
        if(!delta.isEmpty()){
            // pt(n) U= pts
            for(var pt: delta){
                pointer.getPointsToSet().addObject(pt);
            }
            for(var succ_point : pointerFlowGraph.getSuccsOf(pointer)) {
                workList.addEntry(succ_point, delta);
            }
        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    // 完成
    private void processCall(CSVar recv, CSObj recvObj) {
        // TODO - finish me
        /*
            这里理解recv是一个带有上下文标签的变量，我们先要找到它所有的调用
            recvObj相当于我们目前这个，recv新添加的指针的对象，就是delta中的一份子

         */
        List<Invoke> invokeStmts = recv.getVar().getInvokes();
        for( Invoke invokeStmt : invokeStmts){
            JMethod m = resolveCallee(recvObj,invokeStmt);
            CSCallSite csCallsite =  csManager.getCSCallSite(recv.getContext(),invokeStmt);
            Context c_t = contextSelector.selectContext(csCallsite,recvObj,m);

            Pointer c_t_mthis = csManager.getCSVar(c_t,m.getIR().getThis());
            PointsToSet pointSet = PointsToSetFactory.make(recvObj);
            workList.addEntry(c_t_mthis,pointSet);

            // 开始连接一条边，我们写出source和target看一下它在不在
            CSMethod source = csManager.getCSMethod(recv.getContext(),invokeStmt.getContainer());
            CSMethod target = csManager.getCSMethod(c_t,m);
            CallKind invokeKind = CallGraphs.getCallKind(invokeStmt);

            if(callGraph.addEdge(new Edge<>(invokeKind,csCallsite,target))){

                //调用图需要多个种类
                // INTERFACE、VIRTUAL、SPECIAL 和 STATIC

                addReachable(target);

                List<Var> args = invokeStmt.getRValue().getArgs();
                List<Var> params = m.getIR().getParams();

                for(int index = 0; index < params.size(); index++){
                    CSVar arg = csManager.getCSVar(recv.getContext(),args.get(index));
                    CSVar param = csManager.getCSVar(c_t, params.get(index));
                    addPFGEdge(arg, param);
                }

                // 返回值的add edge
                if(invokeStmt.getLValue() != null) {
                    //返回值接受
                    CSVar receiver = csManager.getCSVar(recv.getContext(),invokeStmt.getLValue());

                    //返回值送出
                    List<Var> returnables = m.getIR().getReturnVars();
                    for(Var returnvar: returnables){
                        CSVar sender = csManager.getCSVar(c_t,returnvar);
                        addPFGEdge(sender, receiver);
                    }
                }

            }
        }
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

    PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
