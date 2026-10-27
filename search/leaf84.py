"""For graphs with a leaf v (neighbour u): is there an induced path in G - v through u
with at least 2*rad(G) - 1 vertices?  (That would prove WOWII #84.)"""
import numpy as np
from numba import njit
from inv import dist_matrix, subset_info, popcount


@njit(cache=True)
def check_graph(adj, n):
    D = dist_matrix(adj, n)
    rad = 10**6
    for x in range(n):
        e = D[x].max()
        if e < rad:
            rad = e
    edges, comps, bip, maxdeg = subset_info(adj, n)
    worst = -10**6
    found_leaf = False
    for v in range(n):
        if popcount(adj[v]) != 1:
            continue
        found_leaf = True
        u = 0
        while not (adj[v] >> u) & 1:
            u += 1
        best = 0
        for S in range(1 << n):
            if (S >> v) & 1 or not (S >> u) & 1:
                continue
            k = popcount(S)
            if k <= best:
                continue
            if comps[S] == 1 and edges[S] == k - 1 and maxdeg[S] <= 2:
                best = k
        slack = best - (2 * rad - 1)
        if slack > worst:
            worst = slack
    if not found_leaf:
        return 10**6
    return worst


@njit(cache=True)
def run(G, n):
    out = np.zeros(G.shape[0], dtype=np.int64)
    for i in range(G.shape[0]):
        out[i] = check_graph(G[i].astype(np.int64), n)
    return out


if __name__ == "__main__":
    import sys
    for n in range(3, int(sys.argv[1]) + 1):
        G = np.load(f"graphs/conn{n}.npy")
        r = run(G, n)
        bad = np.nonzero(r < 0)[0]
        print(n, "min slack", r.min(), "failures", len(bad), flush=True)
        for i in bad[:3]:
            adj = G[i]
            print("   ", [(a, b) for a in range(n) for b in range(a + 1, n) if adj[a] >> b & 1])
