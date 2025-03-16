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
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

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
        // TODO - finish me (finished)

        CPFact newFact = new CPFact();
        for (Var var: cfg.getIR().getParams())
            if (canHoldInt(var))
                newFact.update(var, Value.getNAC());

        return newFact;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me (finished)

        // (var, UnDef) has no need to update
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me

        for (Var key: fact.keySet()) {
            if (target.keySet().contains(key))
                target.update(key, meetValue(fact.get(key), target.get(key)));
            else
                target.update(key, fact.get(key));
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me (finished) (finished)

        if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        }
        else if (v1.isUndef() && v2.isUndef()) {
            return Value.getUndef();
        }
        else if (v1.isUndef() && v2.isConstant()) {
            int val2 = v2.getConstant();
            return Value.makeConstant(val2);
        }
        else if (v1.isConstant() && v2.isUndef()) {
            int val1 = v1.getConstant();
            return Value.makeConstant(val1);
        }
        else if (v1.isConstant() && v2.isConstant()) {
            int val1 = v1.getConstant(), val2 = v2.getConstant();
            if (val1 == val2)
                return Value.makeConstant((val1));
            else
                return Value.getNAC();
        }

        return null;
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me (finished)

        CPFact oldOut = out.copy();
        // copy in to out
        out.clear();
        for (Var key: in.keySet())
            out.update(key, in.get(key));

        if (stmt instanceof DefinitionStmt<?, ?>) {
            LValue lval = ((DefinitionStmt<?, ?>) stmt).getLValue();
            if (lval instanceof Var && canHoldInt((Var) lval))
                out.update((Var) lval, evaluate(((DefinitionStmt<?, ?>) stmt).getRValue(), in));
        }

        return !out.equals(oldOut);
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
        // TODO - finish me (finished)

        if (exp instanceof Var) {
            if(!canHoldInt((Var) exp))
                return  Value.getNAC();

            Value val = in.get((Var) exp);
            if (val.isNAC())
                return Value.getNAC();
            else if (val.isConstant())
                return Value.makeConstant(val.getConstant());
            else if (val.isUndef())
                return Value.getUndef();
        }
        else if (exp instanceof IntLiteral) {
            return Value.makeConstant(((IntLiteral) exp).getValue());
        }
        else if (exp instanceof BinaryExp) {
            Var operand1 = ((BinaryExp) exp).getOperand1(), operand2 = ((BinaryExp) exp).getOperand2();
            // check operands can hold integers
            if (!canHoldInt(operand1) || !canHoldInt(operand2))
                return Value.getNAC();

            Value val1 = in.get(operand1), val2 = in.get(operand2);

            if (val1.isNAC())
                if (val2.isConstant() &&
                    val2.getConstant() == 0 &&
                    (((BinaryExp) exp).getOperator() == ArithmeticExp.Op.DIV ||
                    ((BinaryExp) exp).getOperator() == ArithmeticExp.Op.REM)
                    )
                    return Value.getUndef();
                else
                    return Value.getNAC();
            else if (val2.isNAC())
                return Value.getNAC();
            else if (val1.isUndef() || val2.isUndef())
                return Value.getUndef();
            else if (val1.isConstant() && val2.isConstant())
                return evaluateInts(val1.getConstant(), val2.getConstant(), ((BinaryExp) exp).getOperator());
        }

        return Value.getNAC();
    }
    
    private static Value evaluateInts(int operand1, int operand2, BinaryExp.Op operator) {
        if (operator == ArithmeticExp.Op.ADD)
            return Value.makeConstant(operand1 + operand2);
        else if (operator == ArithmeticExp.Op.SUB)
            return Value.makeConstant(operand1 - operand2);
        else if (operator == ArithmeticExp.Op.MUL)
            return Value.makeConstant(operand1 * operand2);
        else if (operator == ArithmeticExp.Op.DIV)
            if (operand2 == 0)
                return Value.getUndef();
            else
                return Value.makeConstant(operand1 / operand2);
        else if (operator == ArithmeticExp.Op.REM)
            if (operand2 == 0)
                return Value.getUndef();
            else
                return Value.makeConstant(operand1 % operand2);
        else if (operator == ConditionExp.Op.EQ)
            if (operand1 == operand2)
                return Value.makeConstant(1);
            else
                return Value.makeConstant(0);
        else if (operator == ConditionExp.Op.NE)
            if (operand1 != operand2)
                return Value.makeConstant(1);
            else
                return Value.makeConstant(0);
        else if (operator == ConditionExp.Op.LT)
            if (operand1 < operand2)
                return Value.makeConstant(1);
            else
                return Value.makeConstant(0);
        else if (operator == ConditionExp.Op.GT)
            if (operand1 > operand2)
                return Value.makeConstant(1);
            else
                return Value.makeConstant(0);
        else if (operator == ConditionExp.Op.LE)
            if (operand1 <= operand2)
                return Value.makeConstant(1);
            else
                return Value.makeConstant(0);
        else if (operator == ConditionExp.Op.GE)
            if (operand1 >= operand2)
                return Value.makeConstant(1);
            else
                return Value.makeConstant(0);
        else if (operator == ShiftExp.Op.SHL)
            return Value.makeConstant(operand1 << operand2);
        else if (operator == ShiftExp.Op.SHR)
            return Value.makeConstant(operand1 >> operand2);
        else if (operator == ShiftExp.Op.USHR)
            return Value.makeConstant(operand1 >>> operand2);
        else if (operator == BitwiseExp.Op.OR)
            return  Value.makeConstant(operand1 | operand2);
        else if (operator == BitwiseExp.Op.AND)
            return  Value.makeConstant(operand1 & operand2);
        else if (operator == BitwiseExp.Op.XOR)
            return  Value.makeConstant(operand1 ^ operand2);

        return Value.getNAC();
    }
}
