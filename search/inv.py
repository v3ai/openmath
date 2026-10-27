"""Exact graph invariants for small graphs (n <= 10) using bitmask brute force.

Every invariant mirrors the definition used in DeepMind's formal-conjectures
statement of the corresponding WOWII conjecture.
"""
import numpy as np
from numba import njit

INF = 10**6


@njit(cache=True)
def popcount(x):
    c = 0
    while x:
        x &= x - 1
        c += 1
    return c


@njit(cache=True)
def dist_matrix(adj, n):
    D = np.full((n, n), INF, dtype=np.int64)
    for s in range(n):
        D[s, s] = 0
        frontier = 1 << s
        seen = frontier
        d = 0
        while frontier:
            d += 1
            nxt = 0
            f = frontier
            while f:
                v = 0
                b = f & -f
                while (b >> v) != 1:
                    v += 1
                f &= f - 1
                nxt |= adj[v]
            nxt &= ~seen
            seen |= nxt
            f = nxt
            while f:
                b = f & -f
                v = 0
                while (b >> v) != 1:
                    v += 1
                f &= f - 1
                D[s, v] = d
            frontier = nxt
    return D


@njit(cache=True)
def lowbit_index(x):
    v = 0
    while not (x >> v) & 1:
        v += 1
    return v


@njit(cache=True)
def subset_info(adj, n):
    """For every subset S: edge count, #components, bipartite flag, max degree."""
    N = 1 << n
    edges = np.zeros(N, dtype=np.int64)
    comps = np.zeros(N, dtype=np.int64)
    bip = np.zeros(N, dtype=np.bool_)
    maxdeg = np.zeros(N, dtype=np.int64)
    for S in range(N):
        e = 0
        md = 0
        T = S
        while T:
            v = lowbit_index(T)
            T &= T - 1
            dv = popcount(adj[v] & S)
            e += dv
            if dv > md:
                md = dv
        edges[S] = e // 2
        maxdeg[S] = md
        # components + bipartite via BFS 2-colouring
        rem = S
        c = 0
        ok = True
        while rem:
            c += 1
            s = lowbit_index(rem)
            side0 = 1 << s
            side1 = 0
            frontier = side0
            col = 0
            visited = side0
            while frontier:
                nb = 0
                f = frontier
                while f:
                    v = lowbit_index(f)
                    f &= f - 1
                    nb |= adj[v] & S
                # vertices in nb must get colour 1-col
                if col == 0:
                    if nb & side0:
                        ok = False
                    new = nb & ~visited
                    side1 |= new
                else:
                    if nb & side1:
                        ok = False
                    new = nb & ~visited
                    side0 |= new
                visited |= new
                frontier = new
                col = 1 - col
            rem &= ~visited
        comps[S] = c
        bip[S] = ok
    return edges, comps, bip, maxdeg


@njit(cache=True)
def ham_and_pathcover(adj, n):
    """Return (has Hamiltonian path, path cover number)."""
    N = 1 << n
    big = 1000
    g = np.full((N, n), big, dtype=np.int64)
    for v in range(n):
        g[1 << v, v] = 1
    for S in range(1, N):
        for v in range(n):
            cur = g[S, v]
            if cur >= big:
                continue
            for u in range(n):
                if (S >> u) & 1:
                    continue
                T = S | (1 << u)
                val = cur if (adj[v] >> u) & 1 else cur + 1
                if val < g[T, u]:
                    g[T, u] = val
    best = big
    for v in range(n):
        if g[N - 1, v] < best:
            best = g[N - 1, v]
    return best == 1, best


@njit(cache=True)
def vertex_connectivity(adj, n, edges, comps):
    # min |S| with G - S disconnected or empty; capped at n-1
    if n <= 1:
        return 0
    N = 1 << n
    full = N - 1
    best = n - 1
    for S in range(N):
        k = popcount(S)
        if k >= best:
            continue
        R = full & ~S
        if R == 0 or comps[R] >= 2:
            best = k
    return best


@njit(cache=True)
def residue(degs):
    s = np.sort(degs)[::-1].copy()
    m = len(s)
    while m > 0:
        if s[0] == 0:
            return m
        d = s[0]
        rest = s[1:m].copy()
        for i in range(min(d, m - 1)):
            rest[i] -= 1
        # Lean's natural-number subtraction truncates at 0
        for i in range(len(rest)):
            if rest[i] < 0:
                rest[i] = 0
        rest = np.sort(rest)[::-1].copy()
        m -= 1
        s = rest
    return 0


@njit(cache=True)
def invariants(adj, n):
    """Returns a float64 vector of invariants for a connected graph."""
    D = dist_matrix(adj, n)
    edges, comps, bip, maxdeg = subset_info(adj, n)
    N = 1 << n
    alpha = 0
    tree = 0
    forest = 0
    bsize = 0
    pathnum = 0
    for S in range(N):
        k = popcount(S)
        if edges[S] == 0 and k > alpha:
            alpha = k
        if edges[S] == k - comps[S]:  # acyclic
            if k > forest:
                forest = k
            if comps[S] == 1:
                if k > tree:
                    tree = k
                if maxdeg[S] <= 2 and k > pathnum:
                    pathnum = k
        if bip[S] and k > bsize:
            bsize = k
    # local independence numbers
    lv = np.zeros(n, dtype=np.int64)
    for v in range(n):
        Nv = adj[v]
        T = Nv
        best = 0
        # enumerate subsets of Nv
        sub = Nv
        while True:
            if edges[sub] == 0:
                c = popcount(sub)
                if c > best:
                    best = c
            if sub == 0:
                break
            sub = (sub - 1) & Nv
        lv[v] = best
    ecc = np.zeros(n, dtype=np.int64)
    for v in range(n):
        ecc[v] = D[v].max()
    rad = ecc.min()
    diam = ecc.max()
    degs = np.zeros(n, dtype=np.int64)
    for v in range(n):
        degs[v] = popcount(adj[v])
    sdeg = np.sort(degs)
    sigma2 = sdeg[1] if n >= 2 else 0
    dmin = sdeg[0]
    distEven = np.zeros(n, dtype=np.int64)
    for v in range(n):
        c = 0
        for w in range(n):
            if D[v, w] % 2 == 0:
                c += 1
        distEven[v] = c
    ham, pc = ham_and_pathcover(adj, n)
    kappa = vertex_connectivity(adj, n, edges, comps)
    res = residue(degs)
    # C4 (not necessarily induced)
    hasC4 = False
    for a in range(n):
        for c in range(a + 1, n):
            if popcount(adj[a] & adj[c]) >= 2:
                hasC4 = True
    out = np.zeros(20, dtype=np.float64)
    out[0] = n
    out[1] = alpha
    out[2] = tree
    out[3] = forest
    out[4] = bsize
    out[5] = pathnum
    out[6] = lv.max()
    out[7] = lv.sum() / n
    out[8] = ecc.sum() / n
    out[9] = rad
    out[10] = diam
    out[11] = dmin
    out[12] = sigma2
    out[13] = distEven.min()
    out[14] = distEven.max()
    out[15] = 1.0 if ham else 0.0
    out[16] = pc
    out[17] = kappa
    out[18] = res
    out[19] = 1.0 if hasC4 else 0.0
    return out


NAMES = ["n", "alpha", "tree", "forest", "b", "path", "maxL", "avgL", "avgEcc",
         "rad", "diam", "delta", "sigma2", "minDistEven", "maxDistEven", "ham",
         "pathCover", "kappa", "residue", "hasC4"]


@njit(cache=True)
def all_invariants(G, n):
    m = G.shape[0]
    out = np.zeros((m, 20), dtype=np.float64)
    for i in range(m):
        out[i] = invariants(G[i].astype(np.int64), n)
    return out
