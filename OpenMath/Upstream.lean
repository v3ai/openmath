/-
# The formal-conjectures statements, verbatim, proved from this project

The definitions and theorem statements below are pasted verbatim from
google-deepmind/formal-conjectures (Apache-2.0), in their original namespaces:
* `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/{VertexDistance,Independence,Induced}.lean`
* `FormalConjectures/WrittenOnTheWallII/GraphConjecture96.lean`
* `FormalConjectures/WrittenOnTheWallII/GraphConjecture19.lean`

Only the `sorry` has been replaced, by a one-line appeal to the proofs in
`OpenMath/WOWII96.lean` and `OpenMath/WOWII19.lean`. That the appeal type-checks shows the
linked statements are exactly the repository statements.
-/
module

public import OpenMath.WOWII96
public import OpenMath.WOWII19

@[expose] public section

/-! Upstream definitions (namespace `SimpleGraph`). -/
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

/-- The same quantity as a real number. -/
noncomputable def indepNeighbors (G : SimpleGraph α) (v : α) : ℝ :=
  (indepNeighborsCard G v : ℝ)

/-- `largestInducedBipartiteSubgraphSize G` is the size of a largest induced
bipartite subgraph of `G`. -/
noncomputable def largestInducedBipartiteSubgraphSize (G : SimpleGraph α) : ℕ :=
  sSup { n | ∃ s : Finset α, (G.induce s).IsBipartite ∧ s.card = n }

/-- `b G` is the number of vertices of a largest induced bipartite subgraph of `G`.
Returned as a real number. -/
noncomputable def b (G : SimpleGraph α) : ℝ :=
  (largestInducedBipartiteSubgraphSize G : ℝ)

end SimpleGraph

/-! Upstream statement of WOWII Conjecture 96. -/
namespace WrittenOnTheWallII.GraphConjecture96

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

theorem conjecture96 (G : SimpleGraph α) (h : G.Connected) :
    let minDistEven := (Finset.univ.image (distEven G)).min' (by simp)
    let maxL := (Finset.univ.image (fun v => indepNeighborsCard G v)).max' (by simp)
    (G.indepNum : ℝ) ≤ 1 + (minDistEven : ℝ) * ((maxL : ℝ) - 1) := by
  exact OpenMath.WOWII96.conjecture96 G h

end WrittenOnTheWallII.GraphConjecture96

/-! Upstream statement of WOWII Conjecture 19. -/
namespace WrittenOnTheWallII.GraphConjecture19

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem conjecture19 (G : SimpleGraph α) [Nontrivial α] (h_conn : G.Connected) :
    ⌊(∑ v ∈ Finset.univ, ((G.eccent v).toNat : ℝ)) / (Fintype.card α : ℝ) +
      sSup (Set.range (indepNeighbors G))⌋ ≤ b G := by
  exact OpenMath.WOWII19.conjecture19 G h_conn

end WrittenOnTheWallII.GraphConjecture19
