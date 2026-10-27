"""Does a simple greedy rule realize route C for TxGraffiti #3?
For every maximal matching M of a regular graph: J = greedy maximal independent set of G[V(M)]
taking vertices in decreasing order of #uncovered neighbours (ties: by label);
I = J u (U - N(J)). Check |I| <= |M|."""
import random
import networkx as nx
import numpy as np
from tx3_route import maximal_matchings

def rule(G, M):
    S = {x for e in M for x in e}; U = set(G) - S
    order = sorted(S, key=lambda x: (-len(set(G[x]) & U), x))
    J = set()
    for x in order:
        if not (set(G[x]) & J):
            J.add(x)
    NJ = set().union(*[set(G[j]) for j in J]) if J else set()
    return len(J) + len(U - NJ) - len(M)

tot = bad = 0; worst = -99
for n in range(4, 10):
    for row in np.load(f"graphs/conn{n}.npy"):
        adj = [int(a) for a in row]
        if len({bin(a).count('1') for a in adj}) != 1: continue
        G = nx.Graph([(a, b) for a in range(n) for b in range(a+1, n) if adj[a] >> b & 1])
        for M in maximal_matchings(G):
            g = rule(G, M); tot += 1; worst = max(worst, g)
            if g > 0:
                bad += 1
                if bad <= 3: print("rule fails:", list(G.edges()), M, g)
print("(graph, matching) pairs", tot, "rule failures", bad, "worst excess", worst)
