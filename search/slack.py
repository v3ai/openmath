import os, sys
import numpy as np
from inv import NAMES

HERE = os.path.dirname(os.path.abspath(__file__))
I = {k: i for i, k in enumerate(NAMES)}


def slacks(X):
    g = lambda k: X[:, I[k]]
    n = g("n")
    S = {}
    S[19] = g("b") - np.floor(g("avgEcc") + g("maxL") + 1e-9)
    S[40] = np.where(n >= 2, g("forest") - np.ceil((g("pathCover") + g("b") + 1) / 2 - 1e-9), 99)
    S[61] = g("forest") - (g("residue") + np.ceil(g("diam") / 3 - 1e-9))
    S[72] = g("tree") - np.ceil(g("avgEcc") + g("maxL") / 3 - 1e-9)
    S[84] = np.where(g("delta") > 0, g("tree") - 2 * g("rad") / np.maximum(g("delta"), 1), 99)
    S[96] = 1 + g("minDistEven") * (g("maxL") - 1) - g("alpha")
    expo = np.where(g("hasC4") > 0, 0.0, 1.0)
    S[133] = g("path") - (g("rad") + np.power(g("avgL"), expo))
    # implications: slack = how far hypothesis is from failing, only meaningful if non-Ham
    S[189] = np.where(g("ham") == 0, (g("maxDistEven") - 1 - g("sigma2")), 99)  # must be > 0
    S[199] = np.where(g("ham") == 0, (np.maximum(g("tree") - 2, 0) - g("kappa")), 99)  # must be > 0
    return S


for n in [int(a) for a in sys.argv[1:]]:
    X = np.load(os.path.join(HERE, "graphs", f"inv{n}.npy"))
    S = slacks(X)
    parts = []
    for c, s in S.items():
        m = s.min()
        parts.append(f"{c}: min={m:.3g} #eq={(np.abs(s - m) < 1e-9).sum()}")
    print(f"n={n}: " + " | ".join(parts))
