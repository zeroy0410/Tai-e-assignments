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
        ArrayDeque<Stmt> queue = new ArrayDeque<>();
        Set<Stmt> reachable = new HashSet<>();
        Set<Stmt> visited = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        queue.add(cfg.getEntry());
        visited.add(cfg.getEntry());
        while(!queue.isEmpty()) {
            Stmt head = queue.pollFirst();
            reachable.add(head);
            boolean add_all = false;
            if(head instanceof If if_stmt) {
                Var v1 = if_stmt.getCondition().getOperand1();
                Var v2 = if_stmt.getCondition().getOperand2();
                if(constants.getOutFact(head).get(v1).isConstant() && constants.getOutFact(head).get(v2).isConstant()) {
                    Value val = ConstantPropagation.evaluate(((If) head).getCondition(),constants.getOutFact(head));
                    if(val.getConstant() == 1) {
                        for(Edge<Stmt> edge: cfg.getOutEdgesOf(head)) {
                            if(edge.getKind() == Edge.Kind.IF_TRUE) {
                                if(!visited.contains(edge.getTarget())){
                                    queue.add(edge.getTarget());
                                    visited.add(edge.getTarget());
                                }
                            }
                        }
                    } else {
                        for (Edge<Stmt> edge : cfg.getOutEdgesOf(head)) {
                            if (edge.getKind() == Edge.Kind.IF_FALSE) {
                                if (!visited.contains(edge.getTarget())) {
                                    queue.add(edge.getTarget());
                                    visited.add(edge.getTarget());
                                }
                            }
                        }
                    }
                } else {
                    add_all = true;
                }
            }
            else if(head instanceof SwitchStmt switch_stmt) {
                Var v1 = switch_stmt.getVar();
                if(constants.getOutFact(head).get(v1).isConstant()) {
                    boolean matched = false;
                    for(Edge<Stmt> edge: cfg.getOutEdgesOf(head)) {
                        if(edge.isSwitchCase() && edge.getCaseValue() == constants.getOutFact(head).get(v1).getConstant()) {
                            matched = true;
                            if(!visited.contains(edge.getTarget())) {
                                queue.add(edge.getTarget());
                                visited.add(edge.getTarget());
                            }
                        }
                    }
                    if(!matched) {
                        Stmt defaultTarget = switch_stmt.getDefaultTarget();  // 获取default对应的目标语句
                        if(!visited.contains(defaultTarget)) {
                            queue.add(defaultTarget);
                            visited.add(defaultTarget);
                        }
                    }
                } else {
                    add_all = true;
                }
            }
            else if(head instanceof AssignStmt assign_stmt) {
                add_all = true;
                LValue v = assign_stmt.getLValue();
                RValue r = assign_stmt.getRValue();
                if(v instanceof Var val) {
                    if(!liveVars.getResult(head).contains(val) && hasNoSideEffect(r)) {
                        reachable.remove(head);
                    }
                }
            }
            else {
                add_all = true;
            }
            if(add_all) {
                for(Edge<Stmt> edge: cfg.getOutEdgesOf(head)) {
                    if(!visited.contains(edge.getTarget())){
                        queue.add(edge.getTarget());
                        visited.add(edge.getTarget());
                    }
                }
            }
        }
        for(Stmt stmt: ir) {
            if(!reachable.contains(stmt)) {
                deadCode.add(stmt);
            }
        }
        return deadCode;
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
