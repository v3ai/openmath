"""Generate all connected simple graphs on n vertices (up to isomorphism).

Every connected graph on n vertices has a non-cut vertex, so it arises from a
connected graph on n-1 vertices by adding one vertex with a nonempty
neighbourhood. Isomorphic duplicates are removed with nauty's canonical
certificate (via pynauty).

Output: search/graphs/conn{n}.npy, an int32 array of shape (count, n) whose
row i holds the adjacency bitmasks of graph i.
"""
import sys, os
import numpy as np
import pynauty

OUT = os.path.join(os.path.dirname(__file__), "graphs")
os.makedirs(OUT, exist_ok=True)


def cert(n, adj):
    d = {v: [u for u in range(n) if adj[v] >> u & 1] for v in range(n)}
    return pynauty.certificate(pynauty.Graph(n, adjacency_dict=d))


def main(nmax):
    prev = np.array([[0]], dtype=np.int32)
    np.save(os.path.join(OUT, "conn1.npy"), prev)
    for n in range(2, nmax + 1):
        path = os.path.join(OUT, f"conn{n}.npy")
        if os.path.exists(path):
            prev = np.load(path)
            continue
        seen = set()
        out = []
        for row in prev:
            base = [int(x) for x in row]
            for mask in range(1, 1 << (n - 1)):
                adj = [base[v] | ((mask >> v & 1) << (n - 1)) for v in range(n - 1)]
                adj.append(mask)
                c = cert(n, adj)
                if c not in seen:
                    seen.add(c)
                    out.append(adj)
        prev = np.array(out, dtype=np.int32)
        np.save(path, prev)
        print(n, len(prev), flush=True)


if __name__ == "__main__":
    main(int(sys.argv[1]))
