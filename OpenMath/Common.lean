/-
Shared definitions and lemmas.

The definitions `distEven`, `indepNeighborsCard`, `indepNeighbors`,
`largestInducedBipartiteSubgraphSize` and `b` (and the lemma
`induce_isBipartite_iff_exists_coloring`, whose proof needed one `simp` adjustment for
Mathlib v4.35) are copied from
google-deepmind/formal-conjectures (Apache-2.0), files
`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/{VertexDistance,Independence,Induced}.lean`,
so that the theorems in this project are literally the open statements recorded there.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Combinatorics.SimpleGraph.Diam
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Basic.Real.Basic

@[expose] public section

set_option linter.unusedSectionVars false

namespace OpenMath

open SimpleGraph Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ### Definitions copied from formal-conjectures -/

/-- `distEven G v` counts the vertices at even distance from `v` in `G` (including `v`). -/
noncomputable def distEven (G : SimpleGraph α) (v : α) : ℕ :=
  (Finset.univ.filter fun w => Even (G.dist v w)).card

/-- Independence number of the subgraph induced by the neighbourhood of `v`. -/
noncomputable def indepNeighborsCard (G : SimpleGraph α) (v : α) : ℕ :=
  (G.induce (G.neighborSet v)).indepNum

/-- The same quantity as a real number. -/
noncomputable def indepNeighbors (G : SimpleGraph α) (v : α) : ℝ :=
  (indepNeighborsCard G v : ℝ)

/-- Size of a largest induced bipartite subgraph. -/
noncomputable def largestInducedBipartiteSubgraphSize (G : SimpleGraph α) : ℕ :=
  sSup { n | ∃ s : Finset α, (G.induce s).IsBipartite ∧ s.card = n }

/-- `b(G)` as a real number. -/
noncomputable def b (G : SimpleGraph α) : ℝ :=
  (largestInducedBipartiteSubgraphSize G : ℝ)

omit [Fintype α] in
/-- An induced subgraph is bipartite exactly when its vertices admit a two-coloring. -/
theorem induce_isBipartite_iff_exists_coloring (G : SimpleGraph α) (s : Finset α) :
    (G.induce s).IsBipartite ↔
      ∃ c : α → Fin 2, ∀ u ∈ s, ∀ v ∈ s, G.Adj u v → c u ≠ c v := by
  constructor
  · rintro ⟨c⟩
    refine ⟨fun v => if hv : v ∈ s then c ⟨v, hv⟩ else 0, ?_⟩
    intro u hu v hv huv
    simp only [hu, hv, ↓reduceDIte]
    exact c.valid huv
  · rintro ⟨c, hc⟩
    exact ⟨Coloring.mk (fun v => c v) fun {u v} huv => hc u u.prop v v.prop huv⟩

/-! ### Distances -/

/-- In a connected graph every vertex `w ≠ v` has a neighbour one step closer to `v`. -/
lemma exists_parent {G : SimpleGraph α} (h : G.Connected) {v w : α} (hw : w ≠ v) :
    ∃ p, G.Adj p w ∧ G.dist v p + 1 = G.dist v w := by
  obtain ⟨q, hq⟩ := h.exists_walk_length_eq_dist w v
  have hnil : ¬ q.Nil := fun hn => hw hn.eq
  refine ⟨q.snd, (q.adj_snd hnil).symm, ?_⟩
  have h1 : G.dist q.snd v ≤ q.tail.length := dist_le q.tail
  have h2 : q.tail.length + 1 = q.length := q.length_tail_add_one hnil
  have h3 : G.dist w v ≤ G.dist w q.snd + G.dist q.snd v := h.dist_triangle
  have h4 : G.dist w q.snd = 1 := dist_eq_one_iff_adj.mpr (q.adj_snd hnil)
  rw [dist_comm (u := v) (v := q.snd), dist_comm (u := v) (v := w)]
  omega

/-- Vertices along a shortest walk are at the expected distances from both ends. -/
lemma dist_getVert_of_geodesic {G : SimpleGraph α} (h : G.Connected) {u w : α}
    (p : G.Walk u w) (hp : p.length = G.dist u w) {i : ℕ} (hi : i ≤ p.length) :
    G.dist u (p.getVert i) = i ∧ G.dist (p.getVert i) w = p.length - i := by
  have h1 : G.dist u (p.getVert i) ≤ i := by
    have := dist_le (p.take i)
    rw [Walk.take_length] at this
    omega
  have h2 : G.dist (p.getVert i) w ≤ p.length - i := by
    have := dist_le (p.drop i)
    rwa [Walk.drop_length] at this
  have h3 : G.dist u w ≤ G.dist u (p.getVert i) + G.dist (p.getVert i) w := h.dist_triangle
  omega

/-- Eccentricity as a natural number (the formal statements use `(G.eccent v).toNat`). -/
noncomputable def ecc (G : SimpleGraph α) (u : α) : ℕ := (G.eccent u).toNat

lemma dist_le_ecc {G : SimpleGraph α} (h : G.Connected) (u w : α) : G.dist u w ≤ ecc G u := by
  obtain ⟨w0, hw0⟩ := G.exists_edist_eq_eccent_of_finite u
  have hle : G.edist u w ≤ G.eccent u := by
    rw [eccent_def]
    exact le_iSup (fun v => G.edist u v) w
  rw [← hw0, ← (h.preconnected u w).coe_dist_eq_edist,
    ← (h.preconnected u w0).coe_dist_eq_edist] at hle
  unfold ecc
  rw [← hw0, ← (h.preconnected u w0).coe_dist_eq_edist, ENat.toNat_natCast]
  exact_mod_cast hle

lemma exists_dist_eq_ecc {G : SimpleGraph α} (h : G.Connected) (u : α) :
    ∃ w, G.dist u w = ecc G u := by
  obtain ⟨w0, hw0⟩ := G.exists_edist_eq_eccent_of_finite u
  refine ⟨w0, ?_⟩
  unfold ecc
  rw [← hw0, ← (h.preconnected u w0).coe_dist_eq_edist, ENat.toNat_natCast]

/-! ### Independent sets in neighbourhoods -/

/-- An independent set of neighbours of `u` has at most `l(u)` elements. -/
lemma card_le_indepNeighborsCard {G : SimpleGraph α} {u : α} {S : Finset α}
    (hS : ∀ x ∈ S, G.Adj u x) (hind : (S : Set α).Pairwise fun x y => ¬ G.Adj x y) :
    S.card ≤ indepNeighborsCard G u := by
  classical
  let T : Finset (G.neighborSet u) := S.subtype (· ∈ G.neighborSet u)
  have hT : (G.induce (G.neighborSet u)).IsIndepSet (T : Set (G.neighborSet u)) := by
    intro a ha b hb hab
    simp only [T, mem_coe, mem_subtype] at ha hb
    simpa using hind ha hb (fun h => hab (Subtype.ext h))
  have hcard : T.card = S.card := by
    simp only [T, card_subtype]
    congr 1
    exact filter_true_of_mem fun x hx => hS x hx
  have := hT.card_le_indepNum
  unfold indepNeighborsCard
  omega

/-- A maximum independent set of the neighbourhood of `u`, as a `Finset α`. -/
lemma exists_indep_neighbors (G : SimpleGraph α) (u : α) :
    ∃ S : Finset α, (∀ x ∈ S, G.Adj u x) ∧ (S : Set α).Pairwise (fun x y => ¬ G.Adj x y) ∧
      S.card = indepNeighborsCard G u := by
  classical
  obtain ⟨T, hT⟩ := (G.induce (G.neighborSet u)).exists_isNIndepSet_indepNum
  refine ⟨T.map (Function.Embedding.subtype _), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, -, rfl⟩ := mem_map.mp hx
    exact y.2
  · intro x hx y hy hxy
    obtain ⟨x', hx', rfl⟩ := mem_map.mp (mem_coe.mp hx)
    obtain ⟨y', hy', rfl⟩ := mem_map.mp (mem_coe.mp hy)
    have hne : x' ≠ y' := fun h => hxy (by rw [h])
    have := hT.isIndepSet (mem_coe.mpr hx') (mem_coe.mpr hy') hne
    simpa using this
  · rw [card_map, hT.card_eq]
    rfl

end OpenMath
