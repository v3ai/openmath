"""Independent numerical check of the statement proved for WOWII #96, in its stronger form:
for EVERY vertex v of a connected graph on n >= 2 vertices,
    alpha(G) <= 1 + disteven(v) * (L - 1),   L = max_u alpha(G[N(u)]).
Exhaustive over all connected graphs up to 9 vertices (bitmask brute force), plus random
connected graphs on 10-40 vertices with alpha computed exactly by MILP (HiGHS).
Also records how often equality holds (sharpness).
"""
import random
import numpy as np
import networkx as nx
from numba import njit
from scipy.optimize import milp, LinearConstraint, Bounds
from inv import dist_matrix, subset_info, popcount


@njit(cache=True)
def check_small(adj, n):
    D = dist_matrix(adj, n)
    edges, comps, bip, maxdeg = subset_info(adj, n)
    alpha = 0
    for S in range(1 << n):
        if edges[S] == 0 and popcount(S) > alpha:
            alpha = popcount(S)
    L = 0
    for v in range(n):
        Nv = adj[v]
        sub = Nv
        while True:
            if edges[sub] == 0 and popcount(sub) > L:
                L = popcount(sub)
            if sub == 0:
                break
            sub = (sub - 1) & Nv
    worst = 10**9
    for v in range(n):
        de = 0
        for w in range(n):
            if D[v, w] % 2 == 0:
                de += 1
        slack = 1 + de * (L - 1) - alpha
        if slack < worst:
            worst = slack
    return worst


@njit(cache=True)
def run_small(G, n):
    out = np.zeros(G.shape[0], dtype=np.int64)
    for i in range(G.shape[0]):
        out[i] = check_small(G[i].astype(np.int64), n)
    return out


def alpha_exact(H):
    V = list(H)
    if H.number_of_edges() == 0:
        return len(V)
    idx = {v: k for k, v in enumerate(V)}
    A = np.zeros((H.number_of_edges(), len(V)))
    for r, (a, b) in enumerate(H.edges()):
        A[r, idx[a]] = 1
        A[r, idx[b]] = 1
    res = milp(-np.ones(len(V)), constraints=[LinearConstraint(A, -np.inf, 1)],
               integrality=np.ones(len(V)), bounds=Bounds(0, 1))
    assert res.status == 0
    return int(round(-res.fun))


if __name__ == "__main__":
    total = eq = bad = 0
    for n in range(2, 10):
        G = np.load(f"graphs/conn{n}.npy")
        r = run_small(G, n)
        total += len(r)
        bad += int((r < 0).sum())
        eq += int((r == 0).sum())
        print(f"n={n}: graphs {len(r)}, violations {int((r < 0).sum())}, min slack {r.min()}", flush=True)
    rng = random.Random(96)
    rb = 0
    for t in range(400):
        n = rng.randrange(10, 41)
        p = rng.choice([0.08, 0.15, 0.3, 0.5])
        H = nx.gnp_random_graph(n, p, seed=rng.randrange(10**9))
        if not nx.is_connected(H):
            continue
        a = alpha_exact(H)
        L = max(alpha_exact(H.subgraph(H[v])) for v in H)
        dist = dict(nx.all_pairs_shortest_path_length(H))
        worst = min(1 + sum(1 for w in H if dist[v][w] % 2 == 0) * (L - 1) - a for v in H)
        rb += 1
        if worst < 0:
            bad += 1
            print("VIOLATION", n, p, list(H.edges()))
    print(f"exhaustive graphs {total} (graphs where some vertex attains equality: {eq}); "
          f"random graphs {rb}; total violations {bad}")
