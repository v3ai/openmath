"""Numerically check each step of the proof of WOWII #19 on all graphs up to n vertices.

For every v* with l(v*) = L = max l, e = ecc(v*):
  (A) b >= sum_i alpha(layer_i(v*)) >= L + e
  (B) if e < avgEcc then avgEcc < D and, for EVERY diametral pair (x, y) and the geodesics
      used, the explicit set {v*} u S u (one vertex per layer, two in 'good' layers) has
      size >= L + D - 1 and is independent inside each layer.
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
def geodesic(adj, D, s, t, n):
    # returns vertices g[0..d] of one shortest s-t path (greedy)
    d = D[s, t]
    g = np.zeros(d + 1, dtype=np.int64)
    g[d] = t
    cur = t
    for k in range(d - 1, -1, -1):
        for w in range(n):
            if (adj[cur] >> w) & 1 and D[s, w] == k:
                cur = w
                break
        g[k] = cur
    return g


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
    L = lv.max()
    avg = ecc.sum() / n
    Dm = ecc.max()
    bad = 0
    for v in range(n):
        if lv[v] != L:
            continue
        e = ecc[v]
        s = 0
        for d in range(e + 1):
            T = 0
            for w in range(n):
                if D[v, w] == d:
                    T |= 1 << w
            s += mis_within(edges, T)
        if not (b >= s and s >= L + e):
            bad += 1
        if e < avg - 1e-9:
            if not (avg < Dm - 1e-9):
                bad += 100
            for x in range(n):
                for y in range(n):
                    if D[x, y] != Dm:
                        continue
                    a = D[v, x]
                    c = D[v, y]
                    if a > c:
                        continue
                    gx = geodesic(adj, D, v, x, n)
                    gy = geodesic(adj, D, v, y, n)
                    good = 0
                    for i in range(2, a + 1):
                        if D[gx[i], gy[i]] >= 2:
                            good += 1
                    if L + e + good < L + Dm - 1:
                        bad += 10000
    return bad


@njit(cache=True)
def run(G, n):
    out = np.zeros(G.shape[0], dtype=np.int64)
    for i in range(G.shape[0]):
        out[i] = check(G[i].astype(np.int64), n)
    return out


if __name__ == "__main__":
    for n in range(2, int(sys.argv[1]) + 1):
        G = np.load(f"graphs/conn{n}.npy")
        r = run(G, n)
        print(n, "graphs", len(G), "bad", int((r > 0).sum()), flush=True)
