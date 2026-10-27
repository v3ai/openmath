# openmath — attacking small open problems with Lean 4 + Mathlib

By Rhett ([@v3ai](https://github.com/v3ai)), working with Anthropic's Claude. The arguments here
came out of an AI-assisted search and have not been peer reviewed. The Lean files are
machine-checked, but we may still have misread a problem's intended meaning or missed
earlier work. Corrections are very welcome; please open an issue.

Lean 4.35.0, Mathlib v4.35.0. Every theorem named `conjectureNN` below is stated **verbatim**
as in [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
(Apache-2.0), where it is tagged `@[category research open]`. The auxiliary definitions
those statements use are copied into `OpenMath/Common.lean` with attribution (definition bodies verbatim; one helper
proof adjusted for Mathlib v4.35), so the files here compile against plain Mathlib.
Upstream pins Lean/Mathlib v4.33.1; the Mathlib definitions these statements depend on are
unchanged between the two versions.

## Results

| Problem | Status before | Result here | File |
|---|---|---|---|
| WOWII (Graffiti.pc) #96: α ≤ 1 + min disteven(v)·(max l(v) − 1) | marked "O" on the WOWII page since 2004; we found no prior proof (WOWII pages, formal-conjectures, arXiv, Preprints.org checked Oct 2026), but one may exist | proof (we believe correct), Lean-checked against the formal-conjectures statement | `OpenMath/WOWII96.lean` |
| WOWII (Graffiti.pc) #19: b ≥ ⌊avg ecc + max l(v)⌋ | listed open (WOWII, formal-conjectures), but **already proved** by Chen–Wang–Feng, Preprints.org, 2 Jul 2026 | independent short proof, Lean-checked (its key step is WOWII #13, DeLaVina–Waller 2004) | `OpenMath/WOWII19.lean` |
| WOWII #84: tree ≥ 2 rad/δ | open | reduced to graphs with a leaf; checked ≤ 9 vertices | — |
| WOWII #189: max disteven ≤ 1 + σ ⇒ Hamiltonian path | open | diameter ≤ 2 case follows from Ore; checked ≤ 9 vertices | — |
| WOWII #40, #61, #72, #133, #199 | open | no counterexample among all 273,192 connected graphs on ≤ 9 vertices | — |
| TxGraffiti #3: i(G) ≤ μ*(G) for regular G | open since 2020 | no counterexample: all connected regular graphs ≤ 9 vertices, 1,891 random regular graphs (degree 3–6, ≤ 40 vertices, exact MILP) | — |
| OEIS A135508 (McEachen 2025) | open | reduction proved on paper; verified for all primes ≤ 10⁷ | — |

## Layout

* `PROOFS.md` — the two proofs in ordinary mathematical prose, plus the partial results.
* `OpenMath/Common.lean` — copied definitions (`distEven`, `indepNeighborsCard`, `b`, …) and
  shared lemmas (BFS parents, distances along geodesics, eccentricity as a natural number).
* `OpenMath/WOWII96.lean`, `OpenMath/WOWII19.lean` — the two proofs.
* `OpenMath/Upstream.lean` — formal-conjectures' own definitions and statements, pasted verbatim
  in their original namespaces and proved in one line from the files above.
* `search/` — the exhaustive and randomized searches (Python + numba + nauty canonical forms + CP-SAT/HiGHS).

## Building

```
lake build OpenMath
```

## License

Apache-2.0 (see `LICENSE`), the same licence as formal-conjectures, from which the definitions
and statements in `OpenMath/Common.lean` and `OpenMath/Upstream.lean` are copied.
