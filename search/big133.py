"""Conjecture 133 on larger C4-free graphs: path(G) >= rad(G) + avg_v l(v).

path(G) = max #vertices of an induced path (exact DFS with pruning).
"""
import itertools, sys, time
import networkx as nx


def polarity_graph(q):
    # Erdos-Renyi polarity graph ER_q over GF(q), q prime
    pts = []
    for x in range(q):
        for y in range(q):
            pts.append((x, y, 1))
    for x in range(q):
        pts.append((x, 1, 0))
    pts.append((1, 0, 0))
    G = nx.Graph()
    G.add_nodes_from(range(len(pts)))
    for i, a in enumerate(pts):
        for j in range(i + 1, len(pts)):
            b = pts[j]
            if (a[0] * b[0] + a[1] * b[1] + a[2] * b[2]) % q == 0:
                G.add_edge(i, j)
    return G


def local_indep(G, v):
    H = G.subgraph(G[v])
    # neighbourhoods in C4-free graphs are matchings + isolated vertices
    return len(nx.maximal_independent_set(H, seed=0)) if H.number_of_edges() == 0 else \
        max(len(c) for c in nx.find_cliques(nx.complement(H)))


def longest_induced_path(G, target=None, time_limit=60):
    """Exact (or until time limit) longest induced path, by DFS."""
    nodes = list(G.nodes())
    adj = {v: set(G[v]) for v in nodes}
    best = [0, None]
    t0 = time.time()

    def extend(path, blocked):
        # blocked = vertices adjacent to some internal (non-endpoint) vertex or in path
        if len(path) > best[0]:
            best[0] = len(path)
            best[1] = list(path)
        if target and best[0] >= target:
            return True
        if time.time() - t0 > time_limit:
            return True
        end = path[-1]
        for w in adj[end]:
            if w in blocked:
                continue
            # w must not be adjacent to any path vertex other than end
            if len(path) >= 2 and any(w in adj[p] for p in path[:-1]):
                continue
            path.append(w)
            nb = blocked | {w}
            if extend(path, nb):
                return True
            path.pop()
        return False

    for s in nodes:
        if extend([s], {s}):
            break
    return best[0], best[1]


def report(name, G, tl=60):
    if not nx.is_connected(G):
        print(name, "disconnected")
        return
    ecc = nx.eccentricity(G)
    rad = min(ecc.values())
    c4 = any(len(set(G[a]) & set(G[b])) >= 2 for a in G for b in G if a < b)
    avgl = sum(local_indep(G, v) for v in G) / G.number_of_nodes()
    need = rad + (1 if c4 else avgl)
    import math
    p, path = longest_induced_path(G, target=math.ceil(need - 1e-9), time_limit=tl)
    status = "OK" if p >= need - 1e-9 else "VIOLATION?"
    print(f"{name}: n={G.number_of_nodes()} C4={c4} rad={rad} avg_l={avgl:.3f} need>={need:.3f} found_path={p} {status}", flush=True)


if __name__ == "__main__":
    for q in [2, 3, 5, 7, 11, 13]:
        report(f"ER_{q}", polarity_graph(q))
    report("Petersen", nx.petersen_graph())
    report("Heawood", nx.heawood_graph())
    report("Hoffman-Singleton", nx.hoffman_singleton_graph())
    report("Tutte-Coxeter(8-cage)", nx.LCF_graph(30, [-13, -9, 7, -7, 9, 13], 5))
    report("McGee", nx.LCF_graph(24, [12, 7, -7], 8))
    report("dodecahedron", nx.dodecahedral_graph())
