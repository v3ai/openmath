"""TxGraffiti Conjecture 3 (open since 2020): for every r-regular graph (r >= 1),
    i(G) <= mu*(G),
i = independent domination number (min maximal independent set),
mu* = saturation number (min maximal matching).

Exact values via CP-SAT. Reports max of i - mu* found and any counterexample.
"""
import sys, random, itertools, time
import networkx as nx
import numpy as np
from ortools.sat.python import cp_model


def solve_i(G):
    m = cp_model.CpModel()
    x = {v: m.NewBoolVar(f"x{v}") for v in G}
    for u, v in G.edges():
        m.Add(x[u] + x[v] <= 1)
    for v in G:
        m.Add(x[v] + sum(x[u] for u in G[v]) >= 1)
    m.Minimize(sum(x.values()))
    s = cp_model.CpSolver()
    s.parameters.max_time_in_seconds = 60
    s.parameters.num_workers = 1
    st = s.Solve(m)
    assert st in (cp_model.OPTIMAL, cp_model.FEASIBLE), st
    # (lower bound, upper bound)
    return (int(round(s.BestObjectiveBound())), int(round(s.ObjectiveValue()))), None


def solve_mustar(G):
    m = cp_model.CpModel()
    E = [tuple(sorted(e)) for e in G.edges()]
    y = {e: m.NewBoolVar(f"y{e}") for e in E}
    inc = {v: [] for v in G}
    for e in E:
        inc[e[0]].append(y[e])
        inc[e[1]].append(y[e])
    for v in G:
        m.Add(sum(inc[v]) <= 1)
    for (u, v) in E:
        m.Add(sum(inc[u]) + sum(inc[v]) >= 1)
    m.Minimize(sum(y.values()))
    s = cp_model.CpSolver()
    s.parameters.max_time_in_seconds = 60
    s.parameters.num_workers = 1
    st = s.Solve(m)
    assert st in (cp_model.OPTIMAL, cp_model.FEASIBLE), st
    return (int(round(s.BestObjectiveBound())), int(round(s.ObjectiveValue()))), None


best = [-10**9, None]
stats = {'tested': 0, 'inexact': 0}


def test(name, G, verbose=False):
    if G.number_of_edges() == 0:
        return
    degs = {d for _, d in G.degree()}
    if len(degs) != 1:
        return
    (ilo, ihi), _ = solve_i(G)
    (mlo, mhi), _ = solve_mustar(G)
    stats["tested"] += 1
    if ilo != ihi or mlo != mhi:
        stats["inexact"] += 1
    if ilo > mhi:
        print("CERTIFIED COUNTEREXAMPLE", name, ilo, mhi, list(G.edges()), flush=True)
    i, mu = ihi, mlo
    gap = i - mu
    if gap > best[0]:
        best[0] = gap
        best[1] = (name, G.number_of_nodes(), degs.pop(), i, mu)
    if gap > 0 and not (ilo > mhi):
        print("POSSIBLE (unproven) gap", end=" ")
    if gap > 0:
        print("COUNTEREXAMPLE?", name, "n", G.number_of_nodes(), "i", i, "mu*", mu,
              list(G.edges()), flush=True)
    elif verbose:
        print(name, "n", G.number_of_nodes(), "i", i, "mu*", mu, flush=True)
    return gap


def families():
    # circulants
    for n in range(5, 31):
        for k in range(1, 4):
            for jumps in itertools.combinations(range(1, n // 2 + 1), k):
                yield f"C{n}{jumps}", nx.circulant_graph(n, jumps)
    for n in range(3, 16):
        for k in range(1, n):
            if 2 * k < n:
                yield f"GP({n},{k})", nx.generalized_petersen_graph(n, k) if hasattr(nx, "generalized_petersen_graph") else nx.Graph()
    for n in range(5, 9):
        for k in range(2, n // 2 + 1):
            if n > 2 * k - 1:
                yield f"Kneser({n},{k})", nx.kneser_graph(n, k)
    for a in range(2, 7):
        for b in range(2, 7):
            yield f"C{a}xC{b}", nx.cartesian_product(nx.cycle_graph(a + 1), nx.cycle_graph(b + 1))
            yield f"K{a}xK{b}", nx.cartesian_product(nx.complete_graph(a), nx.complete_graph(b))
    for d in range(2, 6):
        yield f"Q{d}", nx.hypercube_graph(d)
    for name in ["petersen_graph", "heawood_graph", "pappus_graph", "desargues_graph",
                 "dodecahedral_graph", "moebius_kantor_graph", "icosahedral_graph",
                 "octahedral_graph", "truncated_cube_graph", "truncated_tetrahedron_graph",
                 "hoffman_singleton_graph", "tutte_graph", "frucht_graph", "chvatal_graph",
                 "cubical_graph", "tetrahedral_graph"]:
        if hasattr(nx, name):
            yield name, getattr(nx, name)()
    # line graphs of regular graphs are regular
    for n in range(4, 13, 2):
        for r in (3, 4):
            if n * r % 2 == 0 and n > r:
                for t in range(5):
                    H = nx.random_regular_graph(r, n, seed=1000 * n + 10 * r + t)
                    yield f"L(rr{r},{n})#{t}", nx.line_graph(H)


if __name__ == "__main__":
    mode = sys.argv[1]
    t0 = time.time()
    if mode == "small":
        for n in range(2, 10):
            G9 = np.load(f"graphs/conn{n}.npy")
            cnt = 0
            for row in G9:
                adj = [int(a) for a in row]
                degs = {bin(a).count("1") for a in adj}
                if len(degs) != 1:
                    continue
                G = nx.Graph()
                G.add_nodes_from(range(n))
                G.add_edges_from((a, b) for a in range(n) for b in range(a + 1, n) if adj[a] >> b & 1)
                test(f"conn{n}", G)
                cnt += 1
            print("n", n, "regular connected graphs", cnt, "best gap so far", best, flush=True)
    elif mode == "families":
        k = 0
        for name, G in families():
            if G.number_of_nodes() == 0:
                continue
            G = nx.convert_node_labels_to_integers(G)
            test(name, G)
            k += 1
        print("family graphs tested", k, stats, "best", best, f"{time.time()-t0:.0f}s")
    elif mode == "random":
        rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 0)
        k = 0
        while time.time() - t0 < float(sys.argv[3]) if len(sys.argv) > 3 else 600:
            r = rng.choice([3, 3, 3, 4, 4, 5, 6])
            n = rng.randrange(r + 1, 41)
            if n * r % 2:
                n += 1
            G = nx.random_regular_graph(r, n, seed=rng.randrange(10**9))
            test(f"rr({r},{n})", G)
            k += 1
        print("random graphs tested", k, stats, "best", best)
