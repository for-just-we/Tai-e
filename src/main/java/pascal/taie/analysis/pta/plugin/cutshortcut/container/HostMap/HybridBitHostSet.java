package pascal.taie.analysis.pta.plugin.cutshortcut.container.HostMap;

import pascal.taie.analysis.pta.plugin.cutshortcut.container.Host;
import pascal.taie.util.Indexer;
import pascal.taie.util.collection.HybridBitSet;
import pascal.taie.util.collection.SetEx;

public class HybridBitHostSet extends DelegateHostSet {
    public HybridBitHostSet(Indexer<Host> indexer) {
        this(new HybridBitSet<>(indexer, true));
    }

    public HybridBitHostSet(SetEx<Host> set) {
        super(set);
    }

    @Override
    protected HostSet newSet(SetEx<Host> set) {
        return new HybridBitHostSet(set);
    }
}
