package pascal.taie.analysis.pta.core.solver;

import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.graph.flowgraph.FlowKind;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.plugin.CompositePlugin;
import pascal.taie.analysis.pta.plugin.Plugin;
import pascal.taie.analysis.pta.plugin.cutshortcut.container.ContainerAccessHandler;
import pascal.taie.analysis.pta.plugin.cutshortcut.container.ContainerConfig;
import pascal.taie.analysis.pta.plugin.cutshortcut.container.HostMap.HostList;
import pascal.taie.analysis.pta.plugin.cutshortcut.container.HostMap.HostSet;
import pascal.taie.analysis.pta.plugin.cutshortcut.container.HostMap.HostSetFactory;
import pascal.taie.analysis.pta.plugin.cutshortcut.field.FieldAccessHandler;
import pascal.taie.analysis.pta.plugin.cutshortcut.field.ParameterIndex;
import pascal.taie.analysis.pta.plugin.reflection.ReflectiveCallEdge;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.Exp;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.FieldRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.NullType;
import pascal.taie.language.type.ReferenceType;
import pascal.taie.language.type.Type;
import pascal.taie.util.collection.Sets;

import java.util.Set;

import static pascal.taie.analysis.pta.plugin.cutshortcut.ReflectiveEdgeProperty.setVirtualArg;
import static pascal.taie.analysis.pta.plugin.cutshortcut.SpecialVariables.isNonRelay;
import static pascal.taie.analysis.pta.plugin.cutshortcut.container.ClassAndTypeClassifier.isHashtableClass;
import static pascal.taie.analysis.pta.plugin.cutshortcut.container.ClassAndTypeClassifier.isVectorClass;

public class CutShortcutSolver extends DefaultSolver {
    private ContainerConfig containerConfig;

    private HostSetFactory hostSetFactory;

    private FieldAccessHandler fieldAccessHandler = null;

    private ContainerAccessHandler containerAccessHandler = null;

    private final Set<Var> specialHandledReturnVars = Sets.newSet();

    private final Set<StoreField> ignoredStoreFields = Sets.newSet();

    private final Set<Invoke> recoveredCallSites = Sets.newSet();

    private final Set<JMethod> selectedMethods = Sets.newSet();

    public CutShortcutSolver(AnalysisOptions options, HeapModel heapModel,
                             ContextSelector contextSelector, CSManager csManager) {
        super(options, heapModel, contextSelector, csManager);
    }

    @Override
    public void setPlugin(Plugin plugin) {
        super.setPlugin(plugin);
        assert plugin instanceof CompositePlugin;
        CompositePlugin compositePlugin = (CompositePlugin) plugin;
        for (Plugin p : compositePlugin.getAllPlugins()) {
            if (p instanceof FieldAccessHandler fah)
                fieldAccessHandler = fah;
            else if (p instanceof ContainerAccessHandler cah)
                containerAccessHandler = cah;
        }
        assert fieldAccessHandler != null;
        assert containerAccessHandler != null;
    }

    // ---------- solver logic starts ----------
    /**
     * Initializes pointer analysis.
     */
    @Override
    protected void initialize() {
        containerConfig = ContainerConfig.config;
        hostSetFactory = new HostSetFactory(containerConfig.getHostIndexer());
        super.initialize();
    }

    /**
     * Processes worklist entries until the worklist is empty.
     */
    @Override
    protected void analyze() {
        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            if (entry instanceof WorkList.PointerEntry pEntry) {
                Pointer p = pEntry.pointer();
                PointsToSet pts = pEntry.pointsToSet();
                PointsToSet diff = propagate(p, pts);
                if (!diff.isEmpty() && p instanceof CSVar v) {
                    processInstanceStore(v, diff);
                    processInstanceLoad(v, diff);
                    processArrayStore(v, diff);
                    processArrayLoad(v, diff);
                    processCall(v, diff);
                    plugin.onNewPointsToSet(v, diff);
                }
            }
            else if (entry instanceof WorkList.CallEdgeEntry eEntry)
                processCallEdge(eEntry.edge());
            else if (entry instanceof WorkList.SetStmtEntry sEntry)
                fieldAccessHandler.onNewSetStatement(sEntry.method(), sEntry.fieldRef(), sEntry.baseIndex(), sEntry.rhsIndex());
            else if (entry instanceof WorkList.GetStmtEntry gEntry)
                fieldAccessHandler.onNewGetStatement(gEntry.method(), gEntry.lhsIndex(), gEntry.baseIndex(), gEntry.fieldRef());
            else if (entry instanceof WorkList.HostEntry hEntry) {
                Pointer p = hEntry.pointer();
                HostSet diff = processHostEntry(hEntry);
                if (p instanceof CSVar csVar && !diff.isEmpty())
                    containerAccessHandler.onNewHostEntry(csVar, hEntry.kind(), diff);
            }
        }
        plugin.onFinish();
    }

    String[] stopSigns = new String[]{"iterator(", "entrySet()", "keySet()", "values()", "Entry(", "Iterator("};

    public boolean needPropagateHost(Pointer source, FlowKind kind) {
        if (kind == FlowKind.RETURN) {
            CSVar csSource = (CSVar) source;
            Var sourceVar = csSource.getVar();
            JClass container = sourceVar.getMethod().getDeclaringClass();
            String methodString = sourceVar.getMethod().toString();
            if (containerConfig.isRealHostClass(container)) {
                for (String stopSign : stopSigns) {
                    if (methodString.contains(stopSign))
                        return false;
                }
                if (isHashtableClass(container) && (methodString.contains("elements()") || methodString.contains("keys()")))
                    return false;
                return !isVectorClass(container) || !methodString.contains("elements()");
            }
            return true;
        }
        return true;
    }

    /**
     * @return true if the type of given expression is concerned in
     * pointer analysis, otherwise false.
     */
    public static boolean isConcerned(Exp exp) {
        Type type = exp.getType();
        return type instanceof ReferenceType && !(type instanceof NullType);
    }

    public void addIgnoredStoreField(StoreField set) { // 需要跳过的StoreField，位于最内层（你应该知道最内层的含义）的set方法
        ignoredStoreFields.add(set);
    }

    private HostSet processHostEntry(WorkList.HostEntry entry) {
        Pointer pointer = entry.pointer();
        HostSet hostSet = entry.hostSet();
        HostList.Kind kind = entry.kind();
        HostSet diff = containerAccessHandler.getHostListOf(pointer).addAllDiff(kind, hostSet);
        if (!diff.isEmpty()) {
            pointerFlowGraph.getOutEdgesOf(pointer).forEach(edge -> {
                if (needPropagateHost(edge.source(), edge.kind())) {
                    Pointer target = edge.target();
                    workList.addHostEntry(target, kind, diff);
                }
            });
        }
        return diff;
    }

    private void processInstanceStore(CSVar baseVar, PointsToSet pts) {
        Context context = baseVar.getContext();
        Var var = baseVar.getVar();
        for (StoreField store : var.getStoreFields()) {
            // for StoreFields that are recognized as a setStatement, we skip the process
            if (ignoredStoreFields.contains(store))
                continue;
            Var fromVar = store.getRValue();
            if (isConcerned(fromVar)) {
                CSVar from = getCSManager().getCSVar(context, fromVar);
                pts.forEach(baseObj -> {
                    JField field = store.getFieldRef().resolve();
                    InstanceField instField = getCSManager().getInstanceField(
                            baseObj, field);
                    addPFGEdge(from, instField, FlowKind.INSTANCE_STORE, field.getType()
                    );
                });
            }
        }
    }

    private void processInstanceLoad(CSVar baseVar, PointsToSet pts) {
        Context context = baseVar.getContext();
        Var var = baseVar.getVar();
        for (LoadField load : var.getLoadFields()) {
            Var toVar = load.getLValue();
            JField field = load.getFieldRef().resolveNullable();
            if (isConcerned(toVar) && field != null) {
                CSVar to = getCSManager().getCSVar(context, toVar);
                pts.forEach(baseObj -> {
                    InstanceField instField = getCSManager().getInstanceField(
                            baseObj, field);
                    addPFGEdge(instField, to, //toVar.getType(),
                            isNonRelay(load) ? FlowKind.NON_RELAY_GET : FlowKind.INSTANCE_LOAD);
                });
            }
        }
    }

    public void processCallEdge(Edge<CSCallSite, CSMethod> edge) {
        if (callGraph.addEdge(edge)) {
            if (edge instanceof ReflectiveCallEdge reflEdge)
                setVirtualArg(reflEdge);
            // process new call edge
            CSMethod csCallee = edge.getCallee();
            addCSMethod(csCallee);
            if (edge.getKind() != CallKind.OTHER && !isIgnored(csCallee.getMethod())) {
                Context callerCtx = edge.getCallSite().getContext();
                Invoke callSite = edge.getCallSite().getCallSite();
                Context calleeCtx = csCallee.getContext();
                JMethod callee = csCallee.getMethod();
                InvokeExp invokeExp = callSite.getInvokeExp();
                // pass arguments to parameters
                for (int i = 0; i < invokeExp.getArgCount(); ++i) {
                    Var arg = invokeExp.getArg(i);
                    if (isConcerned(arg)) {
                        Var param = callee.getIR().getParam(i);
                        CSVar argVar = getCSManager().getCSVar(callerCtx, arg);
                        CSVar paramVar = getCSManager().getCSVar(calleeCtx, param);
                        addPFGEdge(argVar, paramVar, FlowKind.PARAMETER_PASSING);
                    }
                }
                // pass results to LHS variable
                if (!ContainerAccessHandler.CutReturnEdge(callSite, callee) || recoveredCallSites.contains(callSite)) {
                    Var lhs = callSite.getResult();
                    if (lhs != null && isConcerned(lhs)) {
                        CSVar csLHS = getCSManager().getCSVar(callerCtx, lhs);
                        for (Var ret : callee.getIR().getReturnVars()) {
                            if (isConcerned(ret) && !specialHandledReturnVars.contains(ret)) {
                                CSVar csRet = getCSManager().getCSVar(calleeCtx, ret);
                                addPFGEdge(csRet, csLHS, FlowKind.RETURN);
                            }
                        }
                    }
                }
            }
            plugin.onNewCallEdge(edge);
        }
    }

    public boolean addRecoveredCallSite(Invoke callSite) {
        return recoveredCallSites.add(callSite);
    }

    public boolean isRecoveredCallSite(Invoke callSite) {
        return recoveredCallSites.contains(callSite);
    }

    public void addPFGEdge(Pointer source, Pointer target, FlowKind kind, Set<Transfer> transfers) {
        PointerFlowEdge edge = new PointerFlowEdge(kind, source, target);
        transfers.forEach(edge::addTransfer);
        if (pointerFlowGraph.addEdge(edge) != null) {
            PointsToSet sourceSet = getPointsToSetOf(source);
            PointsToSet targetSet = makePointsToSet();
            transfers.forEach(transfer -> {
                if (edge.addTransfer(transfer)) {
                    PointsToSet transferSet = transfer.apply(edge, sourceSet);
                    targetSet.addAll(transferSet);
                }
            });
            if (!targetSet.isEmpty())
                addPointsTo(target, targetSet);
            plugin.onNewPFGEdge(edge);
        }
    }

    public void addSetStmtEntry(JMethod method, FieldRef fieldRef, ParameterIndex baseIndex, ParameterIndex rhsIndex) {
        workList.addSetStmtEntry(method, fieldRef, baseIndex, rhsIndex);
    }

    public void addGetStmtEntry(JMethod method, int lhsIndex, ParameterIndex baseIndex, FieldRef fieldRef) {
        workList.addGetStmtEntry(method, lhsIndex, baseIndex, fieldRef);
    }

    public void addHostEntry(Pointer pointer, HostList.Kind kind, HostSet hostSet) {
        workList.addHostEntry(pointer, kind, hostSet);
    }

    public void addSpecialHandledRetVar(Var ret) {
        specialHandledReturnVars.add(ret);
    }

    public void addSelectedMethod(JMethod method) { selectedMethods.add(method); }

    public Set<JMethod> getInvolvedMethods() {
        return selectedMethods;
    }

    public HostSet getEmptyHostSet() {
        return hostSetFactory.make();
    }
}
