module

public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Basic.Real.Basic

@[expose] public section

/-!
# WOWII Conjecture 96: advertised statement

Written on the Wall II (Graffiti.pc), Conjecture 96 (E. DeLaVina, 2004): for a connected
graph $G$ on at least two vertices,
$\alpha(G) \le 1 + \min_v \mathrm{disteven}(v) \cdot (\max_v l(v) - 1)$,
where $\mathrm{disteven}(v)$ is the number of vertices at even distance from $v$ and
$l(v)$ is the independence number of the subgraph induced by the neighbourhood of $v$.

The definitions and the statement are copied verbatim from
google-deepmind/formal-conjectures (Apache-2.0):
`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/{VertexDistance,Independence}.lean`
and `FormalConjectures/WrittenOnTheWallII/GraphConjecture96.lean`.
-/

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- `distEven G v` counts the vertices at even distance from `v` in `G`. This is
DeLaVina's `dist_even(v)` invariant appearing in several WOWII conjectures.
Distance zero is even, so `v` itself is always counted. -/
noncomputable def distEven (G : SimpleGraph α) (v : α) : ℕ :=
  (Finset.univ.filter fun w => Even (G.dist v w)).card

/-- Independence number of the neighbourhood of `v`. -/
noncomputable def indepNeighborsCard (G : SimpleGraph α) (v : α) : ℕ :=
  (G.induce (G.neighborSet v)).indepNum

end SimpleGraph

namespace WrittenOnTheWallII.GraphConjecture96

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- WOWII Conjecture 96, for a connected graph on at least two vertices. -/
theorem conjecture96 (G : SimpleGraph α) (h : G.Connected) :
    let minDistEven := (Finset.univ.image (distEven G)).min' (by simp)
    let maxL := (Finset.univ.image (fun v => indepNeighborsCard G v)).max' (by simp)
    (G.indepNum : ℝ) ≤ 1 + (minDistEven : ℝ) * ((maxL : ℝ) - 1) := by
  sorry

end WrittenOnTheWallII.GraphConjecture96
