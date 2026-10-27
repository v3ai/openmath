"""Route C: for EVERY maximal matching M of a regular graph, some maximal independent set J of
G[V(M)] has |J| + |U - N(J)| <= |M|."""
import random
import networkx as nx
import numpy as np
from tx3_route import maximal_matchings, maximal_independent_sets

def worst(G):
    w = -10**9
    for M in maximal_matchings(G):
        S = {x for e in M for x in e}; U = set(G) - S
        best = min(len(J) + len(U - set().union(*[set(G[j]) for j in J]) if J else len(U))
                   for J in maximal_independent_sets(G.subgraph(S)))
        w = max(w, best - len(M))
    return w

tot = bad = 0
for n in range(4, 10):
    for row in np.load(f"graphs/conn{n}.npy"):
        adj = [int(a) for a in row]
        if len({bin(a).count('1') for a in adj}) != 1: continue
        G = nx.Graph([(a, b) for a in range(n) for b in range(a+1, n) if adj[a] >> b & 1])
        w = worst(G); tot += 1
        if w > 0:
            bad += 1
            if bad <= 3: print("route C fails:", n, w, list(G.edges()))
rng = random.Random(7)
for t in range(80):
    r = rng.choice([3, 3, 4]); n = rng.randrange(r + 1, 13)
    if n * r % 2: n += 1
    G = nx.random_regular_graph(r, n, seed=rng.randrange(10**9))
    w = worst(G); tot += 1
    if w > 0:
        bad += 1
        if bad <= 3: print("route C fails:", r, n, w, list(G.edges()))
print("graphs", tot, "route C fails", bad)
