"""Cross-check bitmask invariants against independent networkx computations."""
import itertools, random
import networkx as nx
import numpy as np
from inv import invariants, NAMES

I = {k: i for i, k in enumerate(NAMES)}


def to_adj(G, n):
    adj = [0] * n
    for u, v in G.edges():
        adj[u] |= 1 << v
        adj[v] |= 1 << u
    return np.array(adj, dtype=np.int64)


def brute(G):
    n = G.number_of_nodes()
    V = list(G.nodes())
    best = dict(alpha=0, tree=0, forest=0, b=0, path=0)
    for k in range(n + 1):
        for S in itertools.combinations(V, k):
            H = G.subgraph(S)
            if k == 0:
                continue
            if H.number_of_edges() == 0:
                best["alpha"] = max(best["alpha"], k)
            if nx.is_forest(H):
                best["forest"] = max(best["forest"], k)
                if nx.is_connected(H):
                    best["tree"] = max(best["tree"], k)
                    if max(dict(H.degree()).values()) <= 2:
                        best["path"] = max(best["path"], k)
            if nx.is_bipartite(H):
                best["b"] = max(best["b"], k)
    ecc = nx.eccentricity(G)
    best["rad"] = min(ecc.values())
    best["diam"] = max(ecc.values())
    best["avgEcc"] = sum(ecc.values()) / n
    # hamiltonian path
    ham = any(all(G.has_edge(p[i], p[i + 1]) for i in range(n - 1))
              for p in itertools.permutations(V))
    best["ham"] = 1.0 if ham else 0.0
    best["kappa"] = nx.node_connectivity(G) if n > 1 else 0
    return best


random.seed(1)
bad = 0
for trial in range(300):
    n = random.randint(2, 7)
    p = random.choice([0.3, 0.5, 0.7])
    G = nx.gnp_random_graph(n, p, seed=random.randint(0, 10**9))
    if not nx.is_connected(G):
        continue
    out = invariants(to_adj(G, n), n)
    ref = brute(G)
    for k, v in ref.items():
        if abs(out[I[k]] - v) > 1e-9:
            bad += 1
            print("MISMATCH", k, out[I[k]], v, list(G.edges()))
print("mismatches:", bad)
