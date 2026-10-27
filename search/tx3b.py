"""TxGraffiti Conjecture 3 (open since 2020): r-regular G (r >= 1)  =>  i(G) <= mu*(G).

Exact values by MILP (HiGHS via scipy):
  i(G)   : min |X|, X independent and dominating.
  mu*(G) : minimum maximal matching = edge domination number gamma'(G)
           (Yannakakis-Gavril 1980), i.e. min |F| with every edge sharing an endpoint with F.
Reports, per run, the number of graphs solved to proven optimality and max(i - mu*).
A counterexample is only reported when certified: lower bound of i > upper bound of mu*.
"""
import sys, random, itertools, time
import numpy as np
import networkx as nx
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse import lil_matrix

TL = 120


def _solve(c, A, lo, hi):
    res = milp(c, constraints=[LinearConstraint(A.tocsr(), lo, hi)], integrality=np.ones(len(c)),
               bounds=Bounds(0, 1), options={"time_limit": TL, "mip_rel_gap": 0})
    if res.x is None:
        return None
    ub = res.fun
    lb = getattr(res, "mip_dual_bound", None)
    if lb is None or res.status == 0:
        lb = ub if res.status == 0 else 0
    return int(np.ceil(lb - 1e-6)), int(round(ub)), res.status == 0


def indep_dom(G):
    V = list(G); idx = {v: k for k, v in enumerate(V)}; E = list(G.edges())
    A = lil_matrix((len(E) + len(V), len(V)))
    for r_, (u, v) in enumerate(E):
        A[r_, idx[u]] = 1; A[r_, idx[v]] = 1
    for k, v in enumerate(V):
        A[len(E) + k, idx[v]] = 1
        for w in G[v]:
            A[len(E) + k, idx[w]] = 1
    lo = np.r_[np.full(len(E), -np.inf), np.ones(len(V))]
    hi = np.r_[np.ones(len(E)), np.full(len(V), np.inf)]
    return _solve(np.ones(len(V)), A, lo, hi)


def edge_dom(G):
    E = [tuple(sorted(e)) for e in G.edges()]; idx = {e: k for k, e in enumerate(E)}
    inc = {v: [] for v in G}
    for e in E:
        inc[e[0]].append(idx[e]); inc[e[1]].append(idx[e])
    A = lil_matrix((len(E), len(E)))
    for k, (u, v) in enumerate(E):
        for j in set(inc[u]) | set(inc[v]):
            A[k, j] = 1
    return _solve(np.ones(len(E)), A, np.ones(len(E)), np.full(len(E), np.inf))


stats = {"tested": 0, "exact": 0, "max_gap": -10**9, "argmax": None, "certified_cex": 0}


def test(name, G):
    if G.number_of_edges() == 0 or len({d for _, d in G.degree()}) != 1:
        return
    a = indep_dom(G); b = edge_dom(G)
    if a is None or b is None:
        return
    (ilo, ihi, iex), (mlo, mhi, mex) = a, b
    stats["tested"] += 1
    if iex and mex:
        stats["exact"] += 1
        gap = ihi - mhi
        if gap > stats["max_gap"]:
            stats["max_gap"] = gap
            stats["argmax"] = (name, G.number_of_nodes(), ihi, mhi)
    if ilo > mhi:
        stats["certified_cex"] += 1
        print("CERTIFIED COUNTEREXAMPLE", name, "i>=", ilo, "mu*<=", mhi, list(G.edges()), flush=True)


def families():
    for n in range(5, 31):
        for k in range(1, 4):
            for jumps in itertools.combinations(range(1, n // 2 + 1), k):
                yield f"C{n}{jumps}", nx.circulant_graph(n, jumps)
    for n in range(3, 16):
        for k in range(1, (n + 1) // 2):
            yield f"GP({n},{k})", nx.generalized_petersen_graph(n, k) if hasattr(nx, "generalized_petersen_graph") else nx.Graph()
    for n in range(5, 9):
        for k in range(2, n // 2 + 1):
            if n > 2 * k:
                yield f"Kneser({n},{k})", nx.kneser_graph(n, k)
    for a in range(3, 8):
        for b in range(3, 8):
            yield f"C{a}xC{b}", nx.cartesian_product(nx.cycle_graph(a), nx.cycle_graph(b))
            yield f"K{a}xK{b}", nx.cartesian_product(nx.complete_graph(a), nx.complete_graph(b))
    for d in range(2, 7):
        yield f"Q{d}", nx.hypercube_graph(d)
    for name in ["petersen_graph", "heawood_graph", "pappus_graph", "desargues_graph",
                 "dodecahedral_graph", "moebius_kantor_graph", "icosahedral_graph",
                 "octahedral_graph", "truncated_cube_graph", "truncated_tetrahedron_graph",
                 "hoffman_singleton_graph", "tutte_graph", "chvatal_graph", "cubical_graph",
                 "tetrahedral_graph", "frucht_graph"]:
        if hasattr(nx, name):
            yield name, getattr(nx, name)()
    for n in range(4, 15, 2):
        for r in (3, 4):
            if n > r:
                for t in range(4):
                    yield f"L(rr{r},{n})#{t}", nx.line_graph(nx.random_regular_graph(r, n, seed=1000 * n + 10 * r + t))


if __name__ == "__main__":
    mode = sys.argv[1]; t0 = time.time()
    if mode == "families":
        for name, G in families():
            if G.number_of_nodes():
                test(name, nx.convert_node_labels_to_integers(G))
    else:
        rng = random.Random(int(sys.argv[2])); budget = float(sys.argv[3])
        while time.time() - t0 < budget:
            r = rng.choice([3, 3, 3, 4, 4, 5, 6]); n = rng.randrange(r + 1, 41)
            if n * r % 2:
                n += 1
            test(f"rr({r},{n})", nx.random_regular_graph(r, n, seed=rng.randrange(10**9)))
    print(mode, stats, f"{time.time() - t0:.0f}s", flush=True)
