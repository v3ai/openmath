# Proofs (human-readable)

Throughout, `G` is a finite simple connected graph on `n ≥ 2` vertices, `d(·,·)` is graph
distance, `L_i(v) = {w : d(v,w) = i}` is the `i`-th distance layer from `v`, `ecc(v)` the
eccentricity, `l(v) = α(G[N(v)])` the local independence number, and `L = max_v l(v)`.

The only fact about layers used repeatedly: if `xy` is an edge then `|d(v,x) − d(v,y)| ≤ 1`.

---

## WOWII Conjecture 96 (DeLaVina, 2004) — no prior proof found

> `α(G) ≤ 1 + min_v disteven(v) · (L − 1)`, where `disteven(v) = |{w : d(v,w) even}|`.

We prove the stronger statement that `α(G) ≤ 1 + disteven(v)·(L − 1)` for **every** vertex `v`.
The bound is sharp: for a star `K_{1,k}` and its centre `v`, `α = k`, `disteven(v) = 1`, `L = k`.

**Proof.** Since `n ≥ 2` and `G` is connected, some vertex has a neighbour, so `L ≥ 1`.

If `L = 1`, every neighbourhood is a clique, and then `G` is complete. Otherwise take two
non-adjacent vertices and the first three vertices `a, x, y` of a shortest path between them:
`a` and `y` are distinct non-adjacent neighbours of `x`, giving `l(x) ≥ 2`. So `α = 1` and the
claim holds. Assume `L ≥ 2`.

Fix any vertex `v`, write `E` for the set of vertices at even distance from `v` (`|E| = D`), and
let `I` be a maximum independent set. Every `w ∈ I` at odd distance from `v` has a *parent*
`p(w)`: a neighbour with `d(v,p(w)) = d(v,w) − 1`. Parents lie in `E` and, being adjacent to
`w ∈ I`, lie outside `I`. Let `P` be the set of parents.

*Fibre bound.* Fix `u ∈ P` and let `F = p⁻¹(u)`. `F` is an independent subset of `N(u)`, so
`|F| ≤ l(u) ≤ L`. If `u ≠ v`, then `u` has its own parent `x` with `d(v,x) = d(v,u) − 1`, while
every `w ∈ F` has `d(v,w) = d(v,u) + 1`. The distances differ by 2, so `x` is adjacent to no
member of `F`, and `F ∪ {x}` is an independent subset of `N(u)`. Hence `|F| ≤ L − 1`.

*Counting.* Summing the fibres gives `|I ∩ odd| + |P| ≤ L·|P| + 1` (the `+1` is the possible
extra child of `v`). Since `I ∩ E` and `P` are disjoint subsets of `E`, `|I ∩ E| + |P| ≤ D`.
Adding,

`|I| ≤ D + (L − 2)|P| + 1 ≤ D + (L − 2)D + 1 = (L − 1)D + 1`,

using `|P| ≤ D` (as `P ⊆ E`) and `L ≥ 2`. Choosing `v` to minimise `disteven(v)` gives the
conjecture. ∎

---

## WOWII Conjecture 19 (DeLaVina, 2003)

> `b(G) ≥ ⌊ē + L⌋`, where `b` is the order of a largest induced bipartite subgraph and `ē`
> the average eccentricity.

**Layer lemma.** For any vertex `v` and independent sets `I_i ⊆ L_i(v)`, the union `⋃ I_i`
induces a bipartite graph. An edge inside the union cannot lie within one layer, so it joins
consecutive layers, and colouring by the parity of `d(v,·)` is proper. Hence
`b(G) ≥ Σ_i α(G[L_i(v)])`.

Fix `v*` with `l(v*) = L` and put `e = ecc(v*) ≥ 1` and `D = diam(G)`. Layer `0` contributes
`1`, layer `1 = N(v*)` contributes `L`, and every layer `2, …, e` is non-empty.

* **Case `e ≥ ē`.** `b ≥ 1 + L + (e − 1) = L + e ≥ L + ē ≥ ⌊ē + L⌋`.

* **Case `e < ē`.** All eccentricities are at most `D`, and if `ē = D` every eccentricity
  would equal `D`, including `e`, contradicting `e < ē`. So `ē < D`, hence `⌊ē⌋ ≤ D − 1` and
  `⌊ē + L⌋ ≤ L + D − 1`.

  Take `x, y` with `d(x,y) = D`, labelled so that `a = d(v*,x) ≤ c = d(v*,y)`. Note `c ≤ e`
  and `a + c ≥ D`. Let `x_i`, `y_i` be the `i`-th vertices of shortest walks from `v*` to `x`
  and to `y`, so both lie in `L_i(v*)`. By the triangle inequality,

  `D = d(x,y) ≤ (a − i) + d(x_i, y_i) + (c − i)`, so `d(x_i, y_i) ≥ D + 2i − a − c`.

  Whenever `2i ≥ a + c − D + 2`, the vertices `x_i, y_i` are distinct and non-adjacent, so
  layer `i` contributes at least `2`. Let `i₀ = max(2, ⌈(a + c − D + 2)/2⌉)`. Then

  `b ≥ L + e + #{i : i₀ ≤ i ≤ a} ≥ L + e + (a + 1 − i₀)`.

  A short calculation using `a ≥ D − c ≥ D − e` shows `e + a + 1 − i₀ ≥ D − 1` in both cases
  of the maximum. Therefore `b ≥ L + D − 1 ≥ ⌊ē + L⌋`. ∎

**Credit and novelty.** This conjecture is no longer open: Zhipeng Chen, Qisheng Wang and Yan Feng
posted a Lean-verified proof on Preprints.org on 2 July 2026 ("A Source-Scoped Lean-Verified Proof of
WOWII Conjecture 19", doi:10.20944/preprints202607.0114.v1), not yet reflected on the WOWII page or in
formal-conjectures. The bound `b ≥ L + D − 1` of the second case is exactly WOWII #13 (DeLaVina–Waller,
2004), so #19 is a short corollary of #13 plus the layer bound; WOWII itself noted in 2005 that the case
`ē ≤ D − 1` follows from #13. The argument above is an independent, self-contained proof of both pieces.

---

## Partial results (not formalized)

* **WOWII #84** (`tree ≥ 2·rad/δ`). For `δ ≥ 2`: `tree ≥ diam + 1 ≥ rad + 1 > 2 rad/δ`, since a
  diametral geodesic is an induced path. So only graphs with a leaf remain, where one needs
  an induced tree on `2·rad` vertices. By Erdős–Saks–Sós and Fajtlowicz's ciliate theorem,
  `tree ≥ 2 rad − 1` always, and `tree ≥ 2 rad` unless the witnessing ciliate is the even
  cycle `C_{2·rad}`. The leaf case with an attached cycle remains.
* **WOWII #189** (`max disteven ≤ 1 + σ ⇒` Hamiltonian path). If `diam ≤ 2`, the non-neighbours
  of `v` are exactly the even-distance vertices other than `v`, so `deg v ≥ n − 1 − σ`. At most
  one vertex has degree `< σ`, so every non-adjacent pair has degree sum `≥ n − 1`, and Ore's
  theorem gives a Hamiltonian path. Graphs of diameter 3 and 4 satisfying the hypothesis exist,
  and for those neither Ore's nor the Chvátal–Erdős condition applies.
* **OEIS A135508** (McEachen 2025). `a(n) = (n+1)/gcd(x(n), n+1)`, and for primes `p ≥ 5`,
  `p | x(p−1) ⇔ a(p−3) = p − 2 ⇔ gcd(x(p−3), p−2) = 1`. So the conjecture says that for odd
  composite `m = p − 2` some prime factor of `m` already divides `x(m−1)`. A prime `q ≥ 7` can
  only enter `x` through an appearing prime `P ≡ −2 (mod q)`, which ties the general case to
  least-prime-in-progression bounds (Linnik-type). Verified for all primes `≤ 10⁷`.
