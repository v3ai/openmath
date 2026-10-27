"""WOWII #72: tree(G) >= ceil(avgEcc + maxL/3).
Diagnostics: for v* maximising l (choose the one with largest ecc), e* = ecc(v*).
  * how often avgEcc > e* (hard case);
  * candidate lemma T3: tree >= e* + 1 + ceil((L-1)/3)  (three-tree averaging);
  * whether T3 together with tree >= diam+1 already implies the conjecture.
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
    tree = 0
    for S in range(1, 1 << n):
        k = popcount(S)
        if comps[S] == 1 and edges[S] == k - 1 and k > tree:
            tree = k
    ecc = np.zeros(n, dtype=np.int64)
    lv = np.zeros(n, dtype=np.int64)
    for v in range(n):
        ecc[v] = D[v].max()
        lv[v] = mis_within(edges, adj[v])
    L = lv.max()
    avg = ecc.sum() / n
    diam = ecc.max()
    estar = 0
    for v in range(n):
        if lv[v] == L and ecc[v] > estar:
            estar = ecc[v]
    target = np.ceil(avg + L / 3 - 1e-9)
    t3 = estar + 1 + (L - 1 + 2) // 3
    hard = 1 if avg > estar + 1e-9 else 0
    t3ok = 1 if tree >= t3 else 0
    implied = 1 if max(t3, diam + 1) >= target else 0
    return hard, t3ok, implied, tree - target


@njit(cache=True)
def run(G, n):
    out = np.zeros((G.shape[0], 4), dtype=np.float64)
    for i in range(G.shape[0]):
        a, b2, c, d = check(G[i].astype(np.int64), n)
        out[i, 0] = a
        out[i, 1] = b2
        out[i, 2] = c
        out[i, 3] = d
    return out


if __name__ == "__main__":
    for n in range(2, int(sys.argv[1]) + 1):
        G = np.load(f"graphs/conn{n}.npy")
        r = run(G, n)
        print(n, "graphs", len(G), "| avgEcc > e*:", int(r[:, 0].sum()),
              "| T3 lemma fails:", int((r[:, 1] == 0).sum()),
              "| max(T3, diam+1) misses target:", int((r[:, 2] == 0).sum()),
              "| conj min slack", r[:, 3].min(), flush=True)
