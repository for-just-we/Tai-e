package pascal.taie.analysis.pta.plugin.cutshortcut.container.HostMap;

import pascal.taie.analysis.pta.plugin.cutshortcut.container.Host;
import pascal.taie.util.Indexer;

public class HostSetFactory {
    private final Indexer<Host> hostIndexer;

    public HostSetFactory(Indexer<Host> hostIndexer) {
        this.hostIndexer = hostIndexer;
    }

    public HostSet make() {
        return new HybridBitHostSet(hostIndexer);
    }

    public HostSet make(Host host) {
        HostSet set = make();
        set.addHost(host);
        return set;
    }
}
