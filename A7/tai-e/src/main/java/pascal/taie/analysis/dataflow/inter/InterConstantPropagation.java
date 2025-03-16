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
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.proginfo.FieldRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.collection.Pair;
import soot.baf.Inst;

import java.util.*;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    private final PointerAnalysisResult pta;

    private final Map<Obj, List<Var>> objToVar;

    private final Map<FieldRef, List<LoadField>> fieldRefToLoadField;

    private final Map<Pair<Obj, JField>, Value> instanceFieldValueMap;

    private final Map<FieldRef, Value> staticFieldValueMap;

    private final Map<Pair<Obj, Integer>, Value> arrayValueMap;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
        String ptaId = getOptions().getString("pta");
        pta = World.get().getResult(ptaId);
        objToVar = new HashMap<>();
        fieldRefToLoadField = new HashMap<>();
        instanceFieldValueMap = new HashMap<>();
        staticFieldValueMap = new HashMap<>();
        arrayValueMap = new HashMap<>();
    }

    @Override
    protected void initialize() {
        // initialize objToVar
        for (Var var: pta.getVars()) {
            for (Obj obj: pta.getPointsToSet(var)) {
                List<Var> varList = objToVar.getOrDefault(obj, new ArrayList<>());
                varList.add(var);
                objToVar.put(obj, varList);
            }
        }

        // initialize fieldRefToStmt
        for (Stmt stmt: icfg) {
            if (stmt instanceof LoadField) {
                FieldAccess fieldAccess = ((LoadField) stmt).getRValue();
                if (fieldAccess instanceof StaticFieldAccess) {
                    FieldRef fieldRef = ((StaticFieldAccess) fieldAccess).getFieldRef();
                    List<LoadField> loadFieldList = fieldRefToLoadField.getOrDefault(fieldRef, new ArrayList<>());
                    loadFieldList.add((LoadField) stmt);
                    fieldRefToLoadField.put(fieldRef, loadFieldList);
                }
            }
        }
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
        // TODO - finish me (finished)
        boolean changed = !in.equals(out);
        // copy in to out
        out.clear();
        for (Var key: in.keySet())
            out.update(key, in.get(key));
        return changed;
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me (finished)
        if (stmt instanceof StoreField)
            return transferStoreFieldNode((StoreField) stmt, in, out);
        else if (stmt instanceof LoadField)
            return transferLoadFieldNode((LoadField) stmt, in, out);
        else if (stmt instanceof StoreArray)
            return transferStoreArrayNode((StoreArray) stmt, in, out);
        else if (stmt instanceof LoadArray)
            return transferLoadArrayNode((LoadArray) stmt, in, out);
        else
            return cp.transferNode(stmt, in, out);
    }

    private boolean transferStoreFieldNode(StoreField stmt, CPFact in, CPFact out) {
        boolean changed = !in.equals(out);
        if (changed) {
            // copy in to out
            out.clear();
            for (Var key: in.keySet())
                out.update(key, in.get(key));

            if (!ConstantPropagation.canHoldInt(stmt.getRValue()))
                return true;

            // propagate changes to alias
            FieldAccess fieldAccess = stmt.getLValue();
            if (fieldAccess instanceof InstanceFieldAccess) {
                Var base = ((InstanceFieldAccess) fieldAccess).getBase();
                for (Obj obj: pta.getPointsToSet(base)) {
                    Value oldValue = instanceFieldValueMap.getOrDefault(
                            new Pair<>(obj, fieldAccess.getFieldRef().resolve()),
                            Value.getUndef()
                    );
                    Value newValue = cp.meetValue(oldValue, in.get(stmt.getRValue()));
                    if (!oldValue.equals(newValue)) {
                        instanceFieldValueMap.put(
                                new Pair<>(obj, fieldAccess.getFieldRef().resolve()),
                                newValue
                        );

                        for (Var alia: objToVar.getOrDefault(obj, new ArrayList<>())) {
                            for (LoadField loadField: alia.getLoadFields()) {
                                solver.addNodeToWorklist(loadField);
                            }
                        }
                    }
                }
            }
            else if (fieldAccess instanceof StaticFieldAccess) {
                FieldRef fieldRef = ((StaticFieldAccess) fieldAccess).getFieldRef();
                Value oldValue = staticFieldValueMap.getOrDefault(fieldRef, Value.getUndef());
                Value newValue = cp.meetValue(oldValue, in.get(stmt.getRValue()));
                if (!oldValue.equals(newValue)) {
                    staticFieldValueMap.put(fieldRef, newValue);
                    for (LoadField loadField: fieldRefToLoadField.getOrDefault(fieldRef, new ArrayList<>()))
                        solver.addNodeToWorklist(loadField);
                }
            }
        }
        return changed;
    }

    private boolean transferStoreArrayNode(StoreArray stmt, CPFact in, CPFact out) {
        boolean changed = !in.equals(out);
        if (changed) {
            // copy in to out
            out.clear();
            for (Var key: in.keySet())
                out.update(key, in.get(key));

            if (!ConstantPropagation.canHoldInt(stmt.getRValue()))
                return true;

            // propagate changes to alias
            ArrayAccess arrayAccess = stmt.getLValue();
            Var base = arrayAccess.getBase();
            Var index = arrayAccess.getIndex();
            Value indexValue = in.get(index);
            for (Obj obj: pta.getPointsToSet(base)) {
                Value oldValue = getArrayValue(obj, indexValue, false);
                Value newValue = cp.meetValue(oldValue, in.get(stmt.getRValue()));
                if (!oldValue.equals(newValue)) {
                    setArrayValue(obj, indexValue, newValue);
                    for (Var alia: objToVar.getOrDefault(obj, new ArrayList<>())) {
                        for (LoadArray loadArray: alia.getLoadArrays()) {
                            solver.addNodeToWorklist(loadArray);
                        }
                    }
                }
            }
        }
        return changed;
    }

    private Value getArrayValue(Obj array, Value indexValue, boolean load) {
        if (indexValue.isUndef()) {
            return Value.getUndef();
        }
        else if (indexValue.isConstant()) {
            return arrayValueMap.getOrDefault(
                    new Pair<>(array, indexValue.getConstant()),
                    arrayValueMap.getOrDefault(
                            new Pair<>(array, -1),
                            Value.getUndef()
                    )
            );
        }
        else if (indexValue.isNAC()) {
            if (load) {
                Value result = Value.getUndef();
                for (Pair<Obj, Integer> pair: arrayValueMap.keySet()) {
                    if (pair.first().equals(array)) {
                        result = cp.meetValue(arrayValueMap.getOrDefault(pair, Value.getUndef()), result);
                    }
                }
                return result;
            }
            else {
                return arrayValueMap.getOrDefault(
                        new Pair<>(array, -1),
                        Value.getUndef()
                );
            }
        }
        return Value.getUndef();
    }

    private void setArrayValue(Obj array, Value indexValue, Value val) {
        if (indexValue.isConstant()) {
            arrayValueMap.put(new Pair<>(array, indexValue.getConstant()), val);
        }
        else if (indexValue.isNAC()) {
            arrayValueMap.put(new Pair<>(array, -1), val);
            for (Pair<Obj, Integer> pair: arrayValueMap.keySet()) {
                if (pair.first().equals(array)) {
                    Value newVal = cp.meetValue(val, arrayValueMap.getOrDefault(pair, Value.getUndef()));
                    arrayValueMap.put(pair, newVal);
                }
            }
        }
    }

    private boolean transferLoadFieldNode(LoadField stmt, CPFact in, CPFact out) {
        CPFact oldOut = out.copy();

        // copy in to out
        out.clear();
        for (Var key: in.keySet())
            out.update(key, in.get(key));

        if (ConstantPropagation.canHoldInt(stmt.getLValue())) {
            // update var
            FieldAccess fieldAccess = stmt.getRValue();
            if (fieldAccess instanceof InstanceFieldAccess) {
                Var base = ((InstanceFieldAccess) fieldAccess).getBase();
                Value val = Value.getUndef();
                for (Obj obj: pta.getPointsToSet(base)) {
                    Value objVal = instanceFieldValueMap.getOrDefault(
                            new Pair<>(obj, fieldAccess.getFieldRef().resolve()),
                            Value.getUndef()
                    );
                    val = cp.meetValue(objVal, val);
                }
                out.update(stmt.getLValue(), val);
            }
            else if (fieldAccess instanceof StaticFieldAccess) {
                FieldRef fieldRef = ((StaticFieldAccess) fieldAccess).getFieldRef();
                out.update(stmt.getLValue(), staticFieldValueMap.getOrDefault(fieldRef, Value.getUndef()));
            }
        }

        return !out.equals(oldOut);
    }

    private boolean transferLoadArrayNode(LoadArray stmt, CPFact in, CPFact out) {
        CPFact oldOut = out.copy();

        // copy in to out
        out.clear();
        for (Var key: in.keySet())
            out.update(key, in.get(key));

        if (ConstantPropagation.canHoldInt(stmt.getLValue())) {
            // update var
            ArrayAccess arrayAccess = stmt.getRValue();
            Var base = arrayAccess.getBase();
            Var index = arrayAccess.getIndex();
            Value indexValue = in.get(index);
            Value val = Value.getUndef();
            for (Obj obj: pta.getPointsToSet(base)) {
                Value objVal = getArrayValue(obj, indexValue, true);
                val = cp.meetValue(objVal, val);
            }
            out.update(stmt.getLValue(), val);
        }

        return !out.equals(oldOut);
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me (finished)
        return out.copy();
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me (finished)
        CPFact result = out.copy();

        // x = m()
        // x -> Undef
        Stmt stmt = edge.getSource();
        if (stmt instanceof Invoke) {
            Var lvalue = ((Invoke) stmt).getLValue();
            if (lvalue != null && ConstantPropagation.canHoldInt(lvalue)) {
                result.update(lvalue, Value.getUndef());
            }
        }

        return result;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me (finished)

        Invoke stmt = (Invoke) edge.getSource();
        List<Var> arguments = stmt.getInvokeExp().getArgs();

        JMethod toMethod = icfg.getContainingMethodOf(edge.getTarget());
        List<Var> parameters = toMethod.getIR().getParams();

        CPFact result = new CPFact();
        // convert variables one by one
        for (int i = 0; i < arguments.size(); i ++) {
            result.update(parameters.get(i), callSiteOut.get(arguments.get(i)));
        }

        return result;
    }


    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // TODO - finish me (finished)

        CPFact result = new CPFact();
        Var var = ((Invoke) edge.getCallSite()).getLValue();
        Value indexValue = Value.getUndef();
        for (Var returnVar: edge.getReturnVars()) {
            indexValue = cp.meetValue(returnOut.get(returnVar), indexValue);
        }

        if (var != null)
            result.update(var, indexValue);

        return result;
    }
}
