package pascal.taie.analysis.pta.plugin.cutshortcut;

import pascal.taie.analysis.pta.plugin.cutshortcut.field.ParameterIndex;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.LoadField;

import java.util.Map;
import java.util.Set;

public class SpecialVariables {
    private static Set<Var> definedVars;

    private static Set<Var> virtualVars;

    private static Map<Var, ParameterIndex> definedParameterIndexes;

    private static Set<LoadField> relayedLoadFields;

    public static void setDefined(Var var) {
        definedVars.add(var);
    }

    public static boolean isDefined(Var var) {
        return definedVars.contains(var);
    }

    public static void setVirtualVar(Var var) {
        virtualVars.add(var);
    }

    public static boolean isVirtualVar(Var var) {
        return virtualVars.contains(var);
    }

    public static void setParameterIndex(Var param, ParameterIndex index) {
        definedParameterIndexes.put(param, index);
    }

    public static ParameterIndex getParameterIndex(Var param) {
        return definedParameterIndexes.get(param);
    }

    public static void disableRelay(LoadField loadField) {
        relayedLoadFields.add(loadField);
    }

    public static boolean isNonRelay(LoadField loadField) {
        return relayedLoadFields.contains(loadField);
    }
}
