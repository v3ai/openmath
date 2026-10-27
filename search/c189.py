"""WOWII #189: if max_v distEven(v) <= 1 + sigma (2nd smallest degree) then G has a Ham path.
Among graphs satisfying the hypothesis, which classical sufficient conditions hold?
  diam<=2, Ore-path (deg u + deg w >= n-1 for non-adjacent u != w), Chvatal-Erdos-path (alpha <= kappa+1)
"""
import sys
import numpy as np
from numba import njit
from inv import dist_matrix, subset_info, popcount, vertex_connectivity


@njit(cache=True)
def check(adj, n):
    D = dist_matrix(adj, n)
    deg = np.zeros(n, dtype=np.int64)
    for v in range(n):
        deg[v] = popcount(adj[v])
    sd = np.sort(deg)
    sigma = sd[1]
    mx = 0
    for v in range(n):
        c = 0
        for w in range(n):
            if D[v, w] % 2 == 0:
                c += 1
        if c > mx:
            mx = c
    if mx > 1 + sigma:
        return -1, 0, 0, 0
    diam = D.max()
    ore = 1
    for u in range(n):
        for w in range(u + 1, n):
            if not (adj[u] >> w) & 1 and deg[u] + deg[w] < n - 1:
                ore = 0
    edges, comps, bip, maxdeg = subset_info(adj, n)
    alpha = 0
    for S in range(1 << n):
        if edges[S] == 0 and popcount(S) > alpha:
            alpha = popcount(S)
    kappa = vertex_connectivity(adj, n, edges, comps)
    ce = 1 if alpha <= kappa + 1 else 0
    return diam, ore, ce, 1


@njit(cache=True)
def run(G, n):
    out = np.zeros((G.shape[0], 4), dtype=np.int64)
    for i in range(G.shape[0]):
        a, b2, c, d = check(G[i].astype(np.int64), n)
        out[i, 0] = a
        out[i, 1] = b2
        out[i, 2] = c
        out[i, 3] = d
    return out


if __name__ == "__main__":
    for n in range(3, int(sys.argv[1]) + 1):
        G = np.load(f"graphs/conn{n}.npy")
        r = run(G, n)
        hyp = r[:, 3] == 1
        print(n, "hyp graphs", int(hyp.sum()), "diam dist", np.bincount(r[hyp, 0]),
              "Ore fails", int((hyp & (r[:, 1] == 0)).sum()),
              "CE fails", int((hyp & (r[:, 2] == 0)).sum()),
              "both fail", int((hyp & (r[:, 1] == 0) & (r[:, 2] == 0)).sum()), flush=True)
        for i in np.nonzero(hyp & (r[:, 1] == 0) & (r[:, 2] == 0))[0][:2]:
            adj = G[i]
            print("   ", [(a, b) for a in range(n) for b in range(a + 1, n) if adj[a] >> b & 1])
