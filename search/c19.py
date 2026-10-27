"""WOWII #19: b(G) >= floor(avg ecc + max_v l(v)).
Compare with provable lower bounds:
  B1 = max_v (ecc(v) + l(v))
  B2 = max_v sum_i alpha(layer_i(v))   (BFS layers from v; union of max independent sets per layer
                                       induces a bipartite subgraph)
"""
import sys
import numpy as np
from numba import njit
from inv import dist_matrix, subset_info, popcount


@njit(cache=True)
def mis_within(edges, T):
    best = 0
    sub = T
    while True:
        if edges[sub] == 0:
            c = popcount(sub)
            if c > best:
                best = c
        if sub == 0:
            break
        sub = (sub - 1) & T
    return best


@njit(cache=True)
def check(adj, n):
    D = dist_matrix(adj, n)
    edges, comps, bip, maxdeg = subset_info(adj, n)
    b = 0
    for S in range(1 << n):
        if bip[S]:
            c = popcount(S)
            if c > b:
                b = c
    ecc = np.zeros(n, dtype=np.int64)
    lv = np.zeros(n, dtype=np.int64)
    for v in range(n):
        ecc[v] = D[v].max()
        lv[v] = mis_within(edges, adj[v])
    avg = ecc.sum() / n
    target = np.floor(avg + lv.max() + 1e-9)
    B1 = 0
    B2 = 0
    for v in range(n):
        if ecc[v] + lv[v] > B1:
            B1 = ecc[v] + lv[v]
        s = 0
        for d in range(ecc[v] + 1):
            T = 0
            for w in range(n):
                if D[v, w] == d:
                    T |= 1 << w
            s += mis_within(edges, T)
        if s > B2:
            B2 = s
    return b - target, B1 - target, B2 - target


@njit(cache=True)
def run(G, n):
    out = np.zeros((G.shape[0], 3), dtype=np.float64)
    for i in range(G.shape[0]):
        a, b1, b2 = check(G[i].astype(np.int64), n)
        out[i, 0] = a
        out[i, 1] = b1
        out[i, 2] = b2
    return out


if __name__ == "__main__":
    for n in range(2, int(sys.argv[1]) + 1):
        G = np.load(f"graphs/conn{n}.npy")
        r = run(G, n)
        print(n, "b-target min", r[:, 0].min(), "| B1 fails", int((r[:, 1] < 0).sum()),
              "| B2 fails", int((r[:, 2] < 0).sum()), "B2 min", r[:, 2].min(), flush=True)
        for i in np.nonzero(r[:, 2] < 0)[0][:2]:
            adj = G[i]
            print("   B2 fail:", [(a, b) for a in range(n) for b in range(a + 1, n) if adj[a] >> b & 1])
