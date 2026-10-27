"""Test candidate lemmas for WOWII #84 on all connected graphs up to n vertices.

L1: every vertex u lies in an induced tree with >= 2 rad(G) - 1 vertices.
L2: for every leaf v with neighbour u, G - v has an induced tree containing u with
    >= 2 rad(G) - 1 vertices  (then adding v gives an induced tree on 2 rad(G) vertices).
"""
import sys
import numpy as np
from numba import njit
from inv import dist_matrix, subset_info, popcount


@njit(cache=True)
def check(adj, n):
    D = dist_matrix(adj, n)
    rad = 10**6
    for x in range(n):
        e = D[x].max()
        if e < rad:
            rad = e
    edges, comps, bip, maxdeg = subset_info(adj, n)
    need = 2 * rad - 1
    # best tree containing each vertex (L1), and avoiding each vertex (for L2)
    bestWith = np.zeros(n, dtype=np.int64)
    bestWithAvoid = np.zeros((n, n), dtype=np.int64)  # [u, v]: contains u, avoids v
    for S in range(1, 1 << n):
        k = popcount(S)
        if comps[S] == 1 and edges[S] == k - 1:
            for u in range(n):
                if (S >> u) & 1:
                    if k > bestWith[u]:
                        bestWith[u] = k
                    for v in range(n):
                        if not (S >> v) & 1 and k > bestWithAvoid[u, v]:
                            bestWithAvoid[u, v] = k
    s1 = 10**6
    for u in range(n):
        if bestWith[u] - need < s1:
            s1 = bestWith[u] - need
    s2 = 10**6
    for v in range(n):
        if popcount(adj[v]) == 1 and n >= 3:
            u = 0
            while not (adj[v] >> u) & 1:
                u += 1
            if bestWithAvoid[u, v] - need < s2:
                s2 = bestWithAvoid[u, v] - need
    return s1, s2


@njit(cache=True)
def run(G, n):
    out = np.zeros((G.shape[0], 2), dtype=np.int64)
    for i in range(G.shape[0]):
        a, b = check(G[i].astype(np.int64), n)
        out[i, 0] = a
        out[i, 1] = b
    return out


if __name__ == "__main__":
    for n in range(3, int(sys.argv[1]) + 1):
        G = np.load(f"graphs/conn{n}.npy")
        r = run(G, n)
        print(n, "L1 min slack", r[:, 0].min(), "fails", int((r[:, 0] < 0).sum()),
              "| L2 min slack", r[:, 1].min(), "fails", int((r[:, 1] < 0).sum()), flush=True)
        for i in np.nonzero(r[:, 1] < 0)[0][:2]:
            adj = G[i]
            print("   L2 fail:", [(a, b) for a in range(n) for b in range(a + 1, n) if adj[a] >> b & 1])
