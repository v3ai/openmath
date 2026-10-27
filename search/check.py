import sys, os, math, time
import numpy as np
from inv import all_invariants, NAMES

HERE = os.path.dirname(os.path.abspath(__file__))
I = {k: i for i, k in enumerate(NAMES)}
EPS = 1e-9


def conj_violations(X):
    g = lambda k: X[:, I[k]]
    n = g("n")
    res = {}
    # 19: b >= floor(avgEcc + maxL)
    res[19] = g("b") < np.floor(g("avgEcc") + g("maxL") + EPS)
    # 40: f >= ceil((pc + b + 1)/2), n >= 2
    res[40] = (n >= 2) & (g("forest") < np.ceil((g("pathCover") + g("b") + 1) / 2 - EPS))
    # 61: f >= residue + ceil(diam/3)
    res[61] = g("forest") < g("residue") + np.ceil(g("diam") / 3 - EPS)
    # 72: tree >= ceil(avgEcc + maxL/3)
    res[72] = g("tree") < np.ceil(g("avgEcc") + g("maxL") / 3 - EPS)
    # 84: tree >= 2 rad / delta  (delta > 0)
    res[84] = (g("delta") > 0) & (g("tree") < 2 * g("rad") / np.maximum(g("delta"), 1) - EPS)
    # 96: alpha <= 1 + minDistEven * (maxL - 1), n >= 2
    res[96] = (n >= 2) & (g("alpha") > 1 + g("minDistEven") * (g("maxL") - 1) + EPS)
    # 133: path >= rad + avgL^{[C4-free]}
    expo = np.where(g("hasC4") > 0, 0.0, 1.0)
    res[133] = g("path") < g("rad") + np.power(g("avgL"), expo) - EPS
    # 189: maxDistEven <= 1 + sigma2  ->  Hamiltonian path  (n >= 2)
    res[189] = (n >= 2) & (g("maxDistEven") <= 1 + g("sigma2")) & (g("ham") == 0)
    # 199: tree - 2 <= kappa -> Hamiltonian path (n >= 2); Lean uses ℕ subtraction
    res[199] = (n >= 2) & (np.maximum(g("tree") - 2, 0) <= g("kappa")) & (g("ham") == 0)
    return res


def main(ns):
    for n in ns:
        G = np.load(os.path.join(HERE, "graphs", f"conn{n}.npy"))
        t = time.time()
        X = all_invariants(G, n)
        np.save(os.path.join(HERE, "graphs", f"inv{n}.npy"), X)
        V = conj_violations(X)
        summary = ", ".join(f"{c}:{int(v.sum())}" for c, v in V.items())
        print(f"n={n} graphs={len(G)} ({time.time()-t:.1f}s)  violations {summary}", flush=True)
        for c, v in V.items():
            idx = np.nonzero(v)[0]
            for i in idx[:3]:
                print(f"   conj {c} counterexample adj={list(G[i])}", flush=True)


if __name__ == "__main__":
    main([int(a) for a in sys.argv[1:]])
