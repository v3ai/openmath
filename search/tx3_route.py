"""Test a proof route for TxGraffiti #3 on small regular graphs.

For a minimum maximal matching M (|M| = m), S = V(M), U = V \\ S (independent).
For J a maximal independent set of G[S], I = J u (U \\ N(J)) is an independent dominating set.
Route A: for EVERY min maximal matching M some J gives |I| <= m.
Route B: for SOME min maximal matching M some J gives |I| <= m.
"""
import itertools, random
import networkx as nx
import numpy as np


def maximal_matchings(G):
    E = list(G.edges())
    res = []

    def rec(i, used, chosen):
        if i == len(E):
            # maximal?
            for (u, v) in E:
                if u not in used and v not in used:
                    return
            res.append(list(chosen))
            return
        u, v = E[i]
        if u not in used and v not in used:
            used.add(u); used.add(v); chosen.append((u, v))
            rec(i + 1, used, chosen)
            chosen.pop(); used.discard(u); used.discard(v)
        rec(i + 1, used, chosen)

    rec(0, set(), [])
    return res


def maximal_independent_sets(H):
    # Bron-Kerbosch on complement
    return [set(c) for c in nx.find_cliques(nx.complement(H))] if H.number_of_nodes() else [set()]


def check(G):
    MM = maximal_matchings(G)
    m = min(len(M) for M in MM)
    mins = [M for M in MM if len(M) == m]
    okA, okB = True, False
    for M in mins:
        S = {x for e in M for x in e}
        U = set(G) - S
        best = 10**9
        for J in maximal_independent_sets(G.subgraph(S)):
            NJ = set().union(*[set(G[j]) for j in J]) if J else set()
            best = min(best, len(J) + len(U - NJ))
        if best <= m:
            okB = True
        else:
            okA = False
    return m, okA, okB


if __name__ == "__main__":
    failsA = failsB = tot = 0
    for n in range(4, 10):
        for row in np.load(f"graphs/conn{n}.npy"):
            adj = [int(a) for a in row]
            if len({bin(a).count('1') for a in adj}) != 1:
                continue
            G = nx.Graph([(a, b) for a in range(n) for b in range(a + 1, n) if adj[a] >> b & 1])
            m, a, b2 = check(G)
            tot += 1
            failsA += not a
            failsB += not b2
            if not b2:
                print("route B fails:", n, list(G.edges()))
    rng = random.Random(5)
    for t in range(150):
        r = rng.choice([3, 3, 4])
        n = rng.randrange(r + 1, 15)
        if n * r % 2:
            n += 1
        G = nx.random_regular_graph(r, n, seed=rng.randrange(10**9))
        m, a, b2 = check(G)
        tot += 1
        failsA += not a
        failsB += not b2
        if not b2:
            print("route B fails:", r, n, list(G.edges()))
    print("graphs", tot, "route A fails", failsA, "route B fails", failsB)
