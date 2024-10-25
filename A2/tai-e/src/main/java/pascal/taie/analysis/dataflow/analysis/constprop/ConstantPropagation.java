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
import pascal.taie.ir.exp.*;
import pascal.taie.ir.exp.BinaryExp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;

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
        CPFact cpf = new CPFact();
        for (Var var: cfg.getIR().getParams()) {
            if (canHoldInt(var)) {
                cpf.update(var, Value.getNAC());
            }
        }
        return cpf;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        for(Var var: fact.keySet()) {
            target.update(var, meetValue(fact.get(var),target.get(var)));
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        if(v1.isNAC()) return Value.getNAC();
        if(v1.isUndef()) return v2;
        if(v2.isNAC()) return Value.getNAC();
        if(v2.isUndef()) return v1;
        if(v1.isConstant() && v2.isConstant() && v1.getConstant() == v2.getConstant())
            return v1;
        else
            return Value.getNAC();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        CPFact old_out = out.copy();
        if(!in.equals(out)) {
            for(Var var: in.keySet()) {
                out.update(var, in.get(var));
            }
        }
        if(stmt instanceof DefinitionStmt<?, ?> definition_stmt) {
            if (stmt.getDef().isPresent()) {
                LValue lValue = definition_stmt.getLValue();
                if((lValue instanceof Var x) && canHoldInt(x)) {
                    Value y = (Value)(evaluate(definition_stmt.getRValue(),in));
                    out.update(x, y);
                }
            }
        }
        return !old_out.equals(out);
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
        if(exp instanceof Var x) {
            return in.get(x);
        }
        if(exp instanceof IntLiteral x) {
            return Value.makeConstant(x.getValue());
        }
        if(exp instanceof BinaryExp binary_exp) {
            Var v1 = binary_exp.getOperand1();
            Var v2 = binary_exp.getOperand2();
            if(in.get(v1).isUndef() || in.get(v2).isUndef()) {
                return Value.getUndef();
            }
            if(binary_exp instanceof ArithmeticExp arithmetic_exp) {
                Var x = arithmetic_exp.getOperand1();
                Var y = arithmetic_exp.getOperand2();
                Op op = arithmetic_exp.getOperator();
                if(op == ArithmeticExp.Op.ADD) {
                    if(in.get(x).isConstant() && in.get(y).isConstant()) {
                        return Value.makeConstant(in.get(x).getConstant() + in.get(y).getConstant());
                    }
                    return Value.getNAC();
                }
                if(op == ArithmeticExp.Op.SUB) {
                    if(in.get(x).isConstant() && in.get(y).isConstant()) {
                        return Value.makeConstant(in.get(x).getConstant() - in.get(y).getConstant());
                    }
                    return Value.getNAC();
                }
                if(op == ArithmeticExp.Op.MUL) {
                    if(in.get(x).isConstant() && in.get(y).isConstant()) {
                        return Value.makeConstant(in.get(x).getConstant() * in.get(y).getConstant());
                    }
                    return Value.getNAC();
                }
                if(op == ArithmeticExp.Op.DIV) {
                    if(in.get(y).isConstant() && in.get(y).getConstant() == 0) {
                        return Value.getUndef();
                    }
                    if(in.get(y).isConstant() && in.get(x).isConstant()) {
                        return Value.makeConstant(in.get(x).getConstant() / in.get(y).getConstant());
                    }
                    return Value.getNAC();
                }
                if(op == ArithmeticExp.Op.REM) {
                    if(in.get(y).isConstant() && in.get(y).getConstant() == 0) {
                        return Value.getUndef();
                    }
                    if(in.get(x).isConstant() && in.get(y).isConstant()) {
                        return Value.makeConstant(in.get(x).getConstant() % in.get(y).getConstant());
                    }
                    return Value.getNAC();
                }
            }
            if(binary_exp instanceof BitwiseExp bitwise_exp) {
                Var x = bitwise_exp.getOperand1();
                Var y = bitwise_exp.getOperand2();
                Op op = bitwise_exp.getOperator();
                if(op == BitwiseExp.Op.OR) {
                    if(in.get(x).isConstant() && in.get(y).isConstant()) {
                        return Value.makeConstant(in.get(x).getConstant() | in.get(y).getConstant());
                    }
                    return Value.getNAC();
                }
                if(op == BitwiseExp.Op.AND) {
                    if(in.get(x).isConstant() && in.get(y).isConstant()) {
                        return Value.makeConstant(in.get(x).getConstant() & in.get(y).getConstant());
                    }
                    return Value.getNAC();
                }
                if(op == BitwiseExp.Op.XOR) {
                    if(in.get(x).isConstant() && in.get(y).isConstant()) {
                        return Value.makeConstant(in.get(x).getConstant() ^ in.get(y).getConstant());
                    }
                    return Value.getNAC();
                }
            }
            if(binary_exp instanceof ConditionExp condition_exp) {
                Var x = condition_exp.getOperand1();
                Var y = condition_exp.getOperand2();
                Op op = condition_exp.getOperator();
                if(op == ConditionExp.Op.EQ) {
                    if(in.get(x).isConstant() && in.get(y).isConstant()) {
                        return Value.makeConstant(in.get(x).getConstant() == in.get(y).getConstant() ? 1 : 0);
                    }
                    return Value.getNAC();
                }
                if(op == ConditionExp.Op.GE) {
                    if(in.get(x).isConstant() && in.get(y).isConstant()) {
                        return Value.makeConstant(in.get(x).getConstant() >= in.get(y).getConstant() ? 1 : 0);
                    }
                    return Value.getNAC();
                }
                if(op == ConditionExp.Op.LT) {
                    if(in.get(x).isConstant() && in.get(y).isConstant()) {
                        return Value.makeConstant(in.get(x).getConstant() < in.get(y).getConstant() ? 1 : 0);
                    }
                    return Value.getNAC();
                }
                if(op == ConditionExp.Op.GT) {
                    if(in.get(x).isConstant() && in.get(y).isConstant()) {
                        return Value.makeConstant(in.get(x).getConstant() > in.get(y).getConstant() ? 1 : 0);
                    }
                    return Value.getNAC();
                }
                if(op == ConditionExp.Op.LE) {
                    if(in.get(x).isConstant() && in.get(y).isConstant()) {
                        return Value.makeConstant(in.get(x).getConstant() <= in.get(y).getConstant() ? 1 : 0);
                    }
                    return Value.getNAC();
                }
                if(op == ConditionExp.Op.NE) {
                    if(in.get(x).isConstant() && in.get(y).isConstant()) {
                        return Value.makeConstant(in.get(x).getConstant() != in.get(y).getConstant() ? 1 : 0);
                    }
                    return Value.getNAC();
                }
            }
            if(binary_exp instanceof  ShiftExp shift_exp) {
                Var x = shift_exp.getOperand1();
                Var y = shift_exp.getOperand2();
                Op op = shift_exp.getOperator();
                if(op == ShiftExp.Op.SHL) {
                    if(in.get(x).isConstant() && in.get(y).isConstant()) {
                        return Value.makeConstant(in.get(x).getConstant() << in.get(y).getConstant());
                    }
                    return Value.getNAC();
                }
                if(op == ShiftExp.Op.SHR) {
                    if(in.get(x).isConstant() && in.get(y).isConstant()) {
                        return Value.makeConstant(in.get(x).getConstant() >> in.get(y).getConstant());
                    }
                    return Value.getNAC();
                }
                if(op == ShiftExp.Op.USHR) {
                    if(in.get(x).isConstant() && in.get(y).isConstant()) {
                        return Value.makeConstant(in.get(x).getConstant() >>> in.get(y).getConstant());
                    }
                    return Value.getNAC();
                }
            }
        }
        return Value.getNAC();
    }
}
