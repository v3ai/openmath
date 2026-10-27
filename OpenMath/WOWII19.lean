/-
# A proof of Written-on-the-Wall II (Graffiti.pc) Conjecture 19

> **WOWII #19 (DeLaVina, listed 3 July 2003, status "O" = open).**
> If `G` is a simple connected graph, then
> `b(G) ≥ FLOOR(average of ecc(v) + maximum of l(v))`,

where `b(G)` is the order of a largest induced bipartite subgraph and `l(v)` the independence
number of the neighbourhood of `v`.

**Prior work.** A Lean-verified proof was posted by Z. Chen, Q. Wang and Y. Feng on Preprints.org
on 2 July 2026 (doi:10.20944/preprints202607.0114.v1). The bound `b ≥ L + D − 1` used in the
second case below is WOWII #13 (DeLaVina–Waller, 2004). This file is an independent,
self-contained formalization against the verbatim formal-conjectures statement.

The statement below is copied verbatim from google-deepmind/formal-conjectures
(`FormalConjectures/WrittenOnTheWallII/GraphConjecture19.lean`).

## Proof

*Layer lemma.* Fix a vertex `v` and pick, in every distance layer `L_i(v)`, an independent set
`I_i`. Every edge of `G` joins vertices whose distances to `v` differ by at most one, so an edge
inside `⋃ I_i` joins consecutive layers; colouring by the parity of the distance shows that
`⋃ I_i` induces a bipartite graph. Hence `b(G) ≥ ∑_i α(L_i(v))`.

Let `v*` maximise `l`, `L = l(v*)`, `e = ecc(v*)`, `D = diam(G)`, `ē` the average eccentricity.
Layer `1` of `v*` is `N(v*)` and contributes `L`; layers `0` and `2, …, e` are non-empty.

* If `e ≥ ē`: `b ≥ L + e ≥ L + ē ≥ ⌊ē + L⌋`.
* If `e < ē`: then `ē < D` (otherwise every eccentricity equals `D`), so `⌊ē + L⌋ ≤ L + D − 1`.
  Take `x, y` with `d(x,y) = D`, `a = d(v*,x) ≤ c = d(v*,y) ≤ e`, and shortest walks from `v*`
  to `x` and `y` with `i`-th vertices `x_i`, `y_i`. The triangle inequality gives
  `d(x_i, y_i) ≥ D + 2i − a − c`, so `{x_i, y_i}` is an independent pair inside layer `i`
  whenever `2i ≥ a + c − D + 2`. Counting those layers gives `b ≥ L + D − 1`.
-/
import OpenMath.Common
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option linter.unusedSectionVars false

namespace OpenMath.WOWII19

open SimpleGraph Finset OpenMath

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The vertices at distance exactly `i` from `v`. -/
noncomputable def layer (G : SimpleGraph α) (v : α) (i : ℕ) : Finset α :=
  univ.filter fun w => G.dist v w = i

/-- Largest independent subset of a finite vertex set. -/
noncomputable def indepIn (G : SimpleGraph α) (T : Finset α) : ℕ := by
  classical
  exact (T.powerset.filter fun s : Finset α => (↑s : Set α).Pairwise fun x y => ¬ G.Adj x y).sup card

lemma le_indepIn {G : SimpleGraph α} {T s : Finset α} (hsT : s ⊆ T)
    (hs : (s : Set α).Pairwise fun x y => ¬ G.Adj x y) : s.card ≤ indepIn G T := by
  classical
  unfold indepIn
  have hmem : s ∈ T.powerset.filter (fun s : Finset α => (↑s : Set α).Pairwise
      fun x y => ¬ G.Adj x y) := mem_filter.mpr ⟨mem_powerset.mpr hsT, hs⟩
  convert le_sup (f := card) hmem

lemma exists_indepIn (G : SimpleGraph α) (T : Finset α) :
    ∃ s ⊆ T, (s : Set α).Pairwise (fun x y => ¬ G.Adj x y) ∧ s.card = indepIn G T := by
  classical
  have hne : (T.powerset.filter fun s : Finset α =>
      (s : Set α).Pairwise fun x y => ¬ G.Adj x y).Nonempty :=
    ⟨∅, mem_filter.mpr ⟨empty_mem_powerset T, by simp⟩⟩
  obtain ⟨s, hs, hsup⟩ := exists_mem_eq_sup _ hne card
  obtain ⟨hs1, hs2⟩ := mem_filter.mp hs
  refine ⟨s, mem_powerset.mp hs1, hs2, ?_⟩
  unfold indepIn
  convert hsup.symm

/-- A vertex set in which adjacent vertices are never at the same distance from `v` induces a
bipartite subgraph. -/
lemma card_le_b_of_layered {G : SimpleGraph α} (v : α) (H : Finset α)
    (hH : ∀ x ∈ H, ∀ y ∈ H, G.Adj x y → G.dist v x ≠ G.dist v y) :
    H.card ≤ largestInducedBipartiteSubgraphSize G := by
  have hbip : (G.induce (H : Set α)).IsBipartite := by
    rw [induce_isBipartite_iff_exists_coloring]
    refine ⟨fun x => if Even (G.dist v x) then 0 else 1, ?_⟩
    intro x hx y hy hxy
    have hne := hH x hx y hy hxy
    dsimp only
    rcases hxy.diff_dist_adj (u := v) with h' | h' | h'
    · exact absurd h'.symm hne
    · rw [h']
      by_cases he : Even (G.dist v x)
      · simp [he, Nat.even_add_one]
      · simp [he, Nat.even_add_one]
    · have hx0 : G.dist v x ≠ 0 := by
        intro h0
        rw [h0] at h'
        exact hne (by omega)
      obtain ⟨k, hk⟩ : ∃ k, G.dist v x = k + 1 := ⟨G.dist v x - 1, by omega⟩
      rw [h', hk, Nat.add_sub_cancel]
      by_cases he : Even k
      · simp [he, Nat.even_add_one]
      · simp [he, Nat.even_add_one]
  unfold largestInducedBipartiteSubgraphSize
  apply le_csSup
  · exact ⟨Fintype.card α, fun n ⟨t, _, ht⟩ => ht ▸ t.card_le_univ⟩
  · exact ⟨H, hbip, rfl⟩

/-- **Layer lemma**: `b(G) ≥ ∑_{i ≤ e} α(L_i(v))`. -/
lemma sum_indepIn_le_b (G : SimpleGraph α) (v : α) (e : ℕ) :
    ∑ i ∈ range (e + 1), indepIn G (layer G v i) ≤ largestInducedBipartiteSubgraphSize G := by
  classical
  have hex := fun i => exists_indepIn G (layer G v i)
  choose s hsT hsind hscard using hex
  have hdisj : (↑(range (e + 1)) : Set ℕ).PairwiseDisjoint s := by
    intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro x hxi hxj
    have h1 := hsT i hxi
    have h2 := hsT j hxj
    simp only [layer, mem_filter, mem_univ, true_and] at h1 h2
    exact hij (h1.symm.trans h2)
  have hcard : ((range (e + 1)).biUnion s).card = ∑ i ∈ range (e + 1), indepIn G (layer G v i) := by
    rw [card_biUnion hdisj]
    exact sum_congr rfl fun i _ => hscard i
  rw [← hcard]
  apply card_le_b_of_layered v
  intro x hx y hy hxy hdist
  obtain ⟨i, -, hxi⟩ := mem_biUnion.mp hx
  obtain ⟨j, -, hyj⟩ := mem_biUnion.mp hy
  have h1 := hsT i hxi
  have h2 := hsT j hyj
  simp only [layer, mem_filter, mem_univ, true_and] at h1 h2
  have hij : i = j := by rw [← h1, ← h2, hdist]
  subst hij
  exact hsind i hxi hyj hxy.ne hxy

variable {G : SimpleGraph α}

/-- Every layer up to the eccentricity is non-empty. -/
lemma one_le_indepIn_layer (h : G.Connected) (v : α) {i : ℕ} (hi : i ≤ ecc G v) :
    1 ≤ indepIn G (layer G v i) := by
  obtain ⟨z, hz⟩ := exists_dist_eq_ecc h v
  obtain ⟨p, hp⟩ := h.exists_walk_length_eq_dist v z
  have hd := (dist_getVert_of_geodesic h p hp (i := i) (by omega)).1
  have := le_indepIn (G := G) (s := {p.getVert i}) (T := layer G v i)
    (by simp [layer, hd]) (by simp)
  simpa using this

/-- Layer `1` is the neighbourhood. -/
lemma indepNeighborsCard_le_indepIn_layer_one (v : α) :
    indepNeighborsCard G v ≤ indepIn G (layer G v 1) := by
  obtain ⟨S, hSadj, hSind, hScard⟩ := exists_indep_neighbors G v
  rw [← hScard]
  apply le_indepIn _ hSind
  intro x hx
  simp [layer, dist_eq_one_iff_adj, hSadj x hx]

/-- **Bound 1**: `b ≥ l(v) + ecc(v)` for every vertex `v` (nontrivial connected `G`). -/
lemma bound_one (h : G.Connected) (v : α) (he : 1 ≤ ecc G v) :
    indepNeighborsCard G v + ecc G v ≤ largestInducedBipartiteSubgraphSize G := by
  refine le_trans ?_ (sum_indepIn_le_b G v (ecc G v))
  obtain ⟨k, hk⟩ : ∃ k, ecc G v = k + 1 := ⟨ecc G v - 1, by omega⟩
  rw [hk, sum_range_succ', sum_range_succ']
  have h0 : 1 ≤ indepIn G (layer G v 0) := one_le_indepIn_layer h v (by omega)
  have h1 := indepNeighborsCard_le_indepIn_layer_one (G := G) v
  have hrest : ∑ i ∈ range k, 1 ≤ ∑ i ∈ range k, indepIn G (layer G v (i + 1 + 1)) :=
    sum_le_sum fun i hi => one_le_indepIn_layer h v (by simp at hi; omega)
  simp only [sum_const, card_range, smul_eq_mul, mul_one] at hrest
  simp only [zero_add] at h1 h0 ⊢
  omega

/-- **Bound 2**: if `d(x, y) = D` and `d(v, x) ≤ d(v, y)`, then `b ≥ l(v) + D − 1`. -/
lemma bound_two (h : G.Connected) (v x y : α) (D : ℕ) (hxy : G.dist x y = D)
    (hav : G.dist v x ≤ G.dist v y) (he : 1 ≤ ecc G v) :
    indepNeighborsCard G v + D ≤ largestInducedBipartiteSubgraphSize G + 1 := by
  set a := G.dist v x with ha
  set c := G.dist v y with hc
  set e := ecc G v with he_def
  have hae : a ≤ e := dist_le_ecc h v x
  have hce : c ≤ e := dist_le_ecc h v y
  have hacD : D ≤ a + c := by
    have := h.dist_triangle (u := x) (v := v) (w := y)
    rw [dist_comm (u := x) (v := v)] at this
    omega
  obtain ⟨p, hp⟩ := h.exists_walk_length_eq_dist v x
  obtain ⟨q, hq⟩ := h.exists_walk_length_eq_dist v y
  -- first good layer
  set i0 := max 2 ((a + c + 3 - D) / 2) with hi0
  -- in every layer `i ∈ [i0, a]` the geodesic vertices `x_i, y_i` are independent
  have hgood : ∀ i ∈ Icc i0 a, 2 ≤ indepIn G (layer G v i) := by
    intro i hi
    rw [mem_Icc] at hi
    have hia : i ≤ p.length := by omega
    have hic : i ≤ q.length := by omega
    obtain ⟨hpx1, hpx2⟩ := dist_getVert_of_geodesic h p hp hia
    obtain ⟨hqy1, hqy2⟩ := dist_getVert_of_geodesic h q hq hic
    have t1 := h.dist_triangle (u := x) (v := p.getVert i) (w := y)
    have t2 := h.dist_triangle (u := p.getVert i) (v := q.getVert i) (w := y)
    have t3 : G.dist x (p.getVert i) = G.dist (p.getVert i) x := dist_comm
    have hfar : 2 ≤ G.dist (p.getVert i) (q.getVert i) := by
      have : a + c + 2 ≤ D + 2 * i := by omega
      omega
    have hne : p.getVert i ≠ q.getVert i := by
      intro heq
      rw [heq, dist_self] at hfar
      omega
    have hnadj : ¬ G.Adj (p.getVert i) (q.getVert i) := by
      intro hadj
      rw [dist_eq_one_iff_adj.mpr hadj] at hfar
      omega
    have := le_indepIn (G := G) (s := {p.getVert i, q.getVert i}) (T := layer G v i)
      (by
        intro z hz
        simp only [mem_insert, mem_singleton] at hz
        rcases hz with rfl | rfl <;> simp [layer, hpx1, hqy1])
      (by
        rw [coe_pair]
        exact Set.pairwise_pair.mpr fun _ => ⟨hnadj, fun h' => hnadj h'.symm⟩)
    rwa [card_pair hne] at this
  -- sum over layers
  refine le_trans ?_ (Nat.add_le_add_right (sum_indepIn_le_b G v e) 1)
  obtain ⟨k, hk⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
  rw [hk, sum_range_succ', sum_range_succ']
  have h0 : 1 ≤ indepIn G (layer G v 0) := one_le_indepIn_layer h v (by omega)
  have h1 := indepNeighborsCard_le_indepIn_layer_one (G := G) v
  -- each remaining layer `j + 2` (for `j < k`) contributes `1`, plus `1` if it is good
  have hrest : ∑ j ∈ range k, (1 + if j + 2 ∈ Icc i0 a then 1 else 0)
      ≤ ∑ j ∈ range k, indepIn G (layer G v (j + 1 + 1)) := by
    apply sum_le_sum
    intro j hj
    rw [mem_range] at hj
    split_ifs with hg
    · exact hgood (j + 2) hg
    · exact one_le_indepIn_layer h v (by omega)
  have hcount : a + 1 - i0 ≤ ∑ j ∈ range k, (if j + 2 ∈ Icc i0 a then 1 else 0) := by
    rw [sum_boole, Nat.cast_id, ← Nat.card_Icc]
    apply card_le_card_of_injOn (fun i => i - 2)
    · intro i hi
      simp only [coe_Icc, Set.mem_Icc] at hi
      simp only [coe_filter, mem_range, mem_Icc, Set.mem_ofPred_eq]
      have : 2 ≤ i0 := le_max_left _ _
      refine ⟨by omega, by omega, by omega⟩
    · intro i hi j hj hij
      simp only [coe_Icc, Set.mem_Icc] at hi hj
      have : 2 ≤ i0 := le_max_left _ _
      simp only at hij
      omega
  rw [sum_add_distrib] at hrest
  simp only [sum_const, card_range, smul_eq_mul, mul_one] at hrest
  simp only [zero_add] at h1 h0 ⊢
  omega

/-! ### The conjecture -/

/-- **WOWII Conjecture 19** (statement verbatim from formal-conjectures). -/
theorem conjecture19 (G : SimpleGraph α) [Nontrivial α] (h_conn : G.Connected) :
    ⌊(∑ v ∈ Finset.univ, ((G.eccent v).toNat : ℝ)) / (Fintype.card α : ℝ) +
      sSup (Set.range (indepNeighbors G))⌋ ≤ b G := by
  have hn : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  -- the vertex maximising local independence
  obtain ⟨vs, -, hvs⟩ := exists_max_image univ (indepNeighborsCard G) univ_nonempty
  set L := indepNeighborsCard G vs with hL
  have hsup : sSup (Set.range (indepNeighbors G)) = (L : ℝ) := by
    apply IsGreatest.csSup_eq
    refine ⟨⟨vs, rfl⟩, ?_⟩
    rintro _ ⟨u, rfl⟩
    unfold indepNeighbors
    exact_mod_cast hvs u (mem_univ u)
  -- diameter
  obtain ⟨xd, -, hxd⟩ := exists_max_image univ (ecc G) univ_nonempty
  set D := ecc G xd with hD
  obtain ⟨yd, hyd⟩ := exists_dist_eq_ecc h_conn xd
  -- eccentricity of `vs`
  set e := ecc G vs with he
  have he1 : 1 ≤ e := by
    obtain ⟨a, b', hab⟩ := exists_pair_ne α
    by_contra hcon
    have h1 := dist_le_ecc h_conn vs a
    have h2 := dist_le_ecc h_conn vs b'
    have ha : a = vs := by
      by_contra hne
      have := h_conn.pos_dist_of_ne (Ne.symm hne)
      omega
    have hb : b' = vs := by
      by_contra hne
      have := h_conn.pos_dist_of_ne (Ne.symm hne)
      omega
    exact hab (ha.trans hb.symm)
  set avg := (∑ v ∈ Finset.univ, ((G.eccent v).toNat : ℝ)) / (Fintype.card α : ℝ) with havg
  have hsum_le : ∑ v ∈ Finset.univ, ((G.eccent v).toNat : ℝ) ≤ Fintype.card α * (D : ℝ) := by
    have : ∀ v ∈ (univ : Finset α), ((G.eccent v).toNat : ℝ) ≤ D := fun v _ => by
      exact_mod_cast hxd v (mem_univ v)
    calc ∑ v ∈ Finset.univ, ((G.eccent v).toNat : ℝ) ≤ ∑ v ∈ (univ : Finset α), (D : ℝ) :=
          sum_le_sum this
      _ = Fintype.card α * (D : ℝ) := by simp
  -- reduce to `avg + L < b + 1`
  rw [hsup]
  unfold b
  have key : avg + L < (largestInducedBipartiteSubgraphSize G : ℝ) + 1 := by
    by_cases hcase : avg ≤ e
    · have := bound_one h_conn vs he1
      have : (L : ℝ) + e ≤ largestInducedBipartiteSubgraphSize G := by exact_mod_cast this
      linarith
    · push Not at hcase
      -- the average eccentricity is strictly below the diameter
      have hlt : avg < D := by
        have heD : (e : ℝ) < D := by
          have : avg ≤ D := by
            rw [havg, div_le_iff₀ hn]
            linarith
          linarith
        have hsum_lt : ∑ v ∈ Finset.univ, ((G.eccent v).toNat : ℝ) < Fintype.card α * (D : ℝ) := by
          have hsplit := Finset.add_sum_erase (univ : Finset α)
            (fun v => ((G.eccent v).toNat : ℝ)) (mem_univ vs)
          have hrest : ∑ v ∈ (univ : Finset α).erase vs, ((G.eccent v).toNat : ℝ)
              ≤ ((univ : Finset α).erase vs).card * (D : ℝ) := by
            calc ∑ v ∈ (univ : Finset α).erase vs, ((G.eccent v).toNat : ℝ)
                ≤ ∑ v ∈ (univ : Finset α).erase vs, (D : ℝ) :=
                  sum_le_sum fun v _ => by exact_mod_cast hxd v (mem_univ v)
              _ = ((univ : Finset α).erase vs).card * (D : ℝ) := by simp
          have hcard : (((univ : Finset α).erase vs).card : ℝ) + 1 = Fintype.card α := by
            rw [card_erase_of_mem (mem_univ vs), card_univ]
            have : 1 ≤ Fintype.card α := Fintype.card_pos
            push_cast [Nat.cast_sub this]
            ring
          have hev : ((G.eccent vs).toNat : ℝ) = e := rfl
          rw [← hsplit, hev]
          nlinarith
        rw [havg, div_lt_iff₀ hn]
        linarith
      -- choose the diametral pair so that `x` is the closer end
      have hb2 : L + D ≤ largestInducedBipartiteSubgraphSize G + 1 := by
        rcases le_total (G.dist vs xd) (G.dist vs yd) with hxy | hxy
        · exact bound_two h_conn vs xd yd D hyd hxy he1
        · have hyx : G.dist yd xd = D := by rw [dist_comm]; exact hyd
          exact bound_two h_conn vs yd xd D hyx hxy he1
      have : (L : ℝ) + D ≤ largestInducedBipartiteSubgraphSize G + 1 := by exact_mod_cast hb2
      linarith
  have hfl : ⌊avg + (L : ℝ)⌋ ≤ (largestInducedBipartiteSubgraphSize G : ℤ) := by
    rw [Int.floor_le_iff]
    push_cast
    linarith
  exact_mod_cast hfl

end OpenMath.WOWII19
