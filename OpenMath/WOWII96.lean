/-
# A proof of Written-on-the-Wall II (Graffiti.pc) Conjecture 96

> **WOWII #96 (DeLaVina, listed 21 April 2004, status "O" = open).**
> If `G` is a simple connected graph, then
> `α(G) ≤ 1 + (min_v dist_even(v)) · (max_v l(v) − 1)`.

Here `α` is the independence number, `dist_even(v)` the number of vertices at even
distance from `v` (including `v` itself), and `l(v)` the independence number of the
subgraph induced by the neighbourhood of `v`.

The theorem statement and the two auxiliary definitions below are copied verbatim from
google-deepmind/formal-conjectures (Apache-2.0):
* `FormalConjectures/WrittenOnTheWallII/GraphConjecture96.lean` (`conjecture96`)
* `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/VertexDistance.lean` (`distEven`)
* `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Independence.lean`
  (`indepNeighborsCard`)

## Proof idea

Fix any vertex `v`, put `L = max_u l(u)` and `D = dist_even(v)`, and let `I` be an
independent set. Every vertex `w ∈ I` at odd distance from `v` has a *parent*: a neighbour
one step closer to `v`. Parents lie at even distance and are not in `I`.

* A parent `u ≠ v` itself has a neighbour `x` one step closer to `v`; `x` is non-adjacent
  to all children of `u` (their distances to `v` differ by 2), so `{x} ∪ children(u)` is an
  independent subset of `N(u)` and `u` has at most `L − 1` children.
* `v` has at most `L` children.

With `P` the set of parents, `|I ∩ odd| + |P| ≤ L·|P| + 1`, and `|I ∩ even| + |P| ≤ D`
because `I` and `P` are disjoint subsets of the even layer. For `L ≥ 2` this gives
`|I| ≤ (L−1)·D + 1`. For `L = 1` every neighbourhood is a clique, so `G` is complete and
`α = 1`.
-/
import OpenMath.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace OpenMath.WOWII96

open SimpleGraph Finset OpenMath

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- If every neighbourhood has independence number at most `1`, the connected graph is
complete, hence its independence number is at most `1`. -/
lemma indepNum_le_one_of_local {G : SimpleGraph α} (h : G.Connected)
    (hL : ∀ u, indepNeighborsCard G u ≤ 1) : G.indepNum ≤ 1 := by
  classical
  obtain ⟨s, hs⟩ := G.exists_isNIndepSet_indepNum
  rw [← hs.card_eq]
  by_contra hlt
  push Not at hlt
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp hlt
  have hnadj : ¬ G.Adj a b := hs.isIndepSet ha hb hab
  have hd : 1 < G.dist a b := h.one_lt_dist_of_ne_of_not_adj hab hnadj
  obtain ⟨q, hq⟩ := h.exists_walk_length_eq_dist a b
  obtain ⟨x, y, z, hxy, hyz, hxz, hne⟩ := q.exists_adj_adj_not_adj_ne hq hd
  have h2 : ({x, z} : Finset α).card ≤ indepNeighborsCard G y := by
    apply card_le_indepNeighborsCard
    · intro t ht
      simp only [mem_insert, mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact hxy.symm
      · exact hyz
    · intro p hp r hr hpr
      simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hp hr
      rcases hp with rfl | rfl <;> rcases hr with rfl | rfl
      · exact absurd rfl hpr
      · exact hxz
      · exact fun h' => hxz h'.symm
      · exact absurd rfl hpr
  rw [card_pair hne] at h2
  have := hL y
  omega

/-! ### The main counting argument -/

/-- **Key inequality.** For every vertex `v` and every bound `L ≥ 2` on the local
independence numbers, `α(G) + dist_even(v) ≤ 1 + dist_even(v) · L`. -/
theorem key (G : SimpleGraph α) (h : G.Connected) (v : α) (L : ℕ) (hL2 : 2 ≤ L)
    (hL : ∀ u, indepNeighborsCard G u ≤ L) :
    G.indepNum + distEven G v ≤ 1 + distEven G v * L := by
  classical
  obtain ⟨I, hI⟩ := G.exists_isNIndepSet_indepNum
  have hind : (I : Set α).Pairwise fun x y => ¬ G.Adj x y := hI.isIndepSet
  rw [← hI.card_eq]
  -- the even layer, and the two halves of `I`
  set E : Finset α := univ.filter fun w => Even (G.dist v w) with hE
  set IE : Finset α := I.filter fun w => Even (G.dist v w) with hIE
  set IO : Finset α := I.filter fun w => ¬ Even (G.dist v w) with hIO
  have hsplit : IE.card + IO.card = I.card := card_filter_add_card_filter_not _
  -- parents
  have hpar : ∀ w : α, ∃ p, w ≠ v → G.Adj p w ∧ G.dist v p + 1 = G.dist v w := by
    intro w
    by_cases hw : w = v
    · exact ⟨v, fun h' => absurd hw h'⟩
    · obtain ⟨p, hp⟩ := exists_parent h hw
      exact ⟨p, fun _ => hp⟩
  choose par hpar using hpar
  have hIO_ne : ∀ w ∈ IO, w ≠ v := by
    intro w hw hwv
    subst hwv
    simp [hIO] at hw
  set P : Finset α := IO.image par with hP
  -- parents are in the even layer and outside `I`
  have hP_E : ∀ u ∈ P, u ∈ E := by
    intro u hu
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hu
    have hwodd : ¬ Even (G.dist v w) := (mem_filter.mp hw).2
    have := (hpar w (hIO_ne w hw)).2
    simp only [hE, mem_filter, mem_univ, true_and]
    by_contra hcon
    apply hwodd
    rw [← this]
    exact (Nat.not_even_iff_odd.mp hcon).add_one
  have hP_I : ∀ u ∈ P, u ∉ I := by
    intro u hu huI
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hu
    have hwI : w ∈ I := (mem_filter.mp hw).1
    have hadj := (hpar w (hIO_ne w hw)).1
    exact hind huI hwI hadj.ne hadj
  -- (1) |I ∩ even| + |P| ≤ |E|
  have h1 : IE.card + P.card ≤ E.card := by
    rw [← card_union_of_disjoint]
    · apply card_le_card
      intro x hx
      rcases mem_union.mp hx with hx | hx
      · simp only [hE, mem_filter, mem_univ, true_and]
        exact (mem_filter.mp hx).2
      · exact hP_E x hx
    · rw [Finset.disjoint_left]
      intro x hx hxP
      exact hP_I x hxP (mem_filter.mp hx).1
  -- (2) fibre bound: each parent `u` has at most `L - 1` children, `v` at most `L`
  have hfib : ∀ u ∈ P, (IO.filter fun w => par w = u).card + 1 ≤ L + (if u = v then 1 else 0) := by
    intro u hu
    set F := IO.filter fun w => par w = u with hF
    have hFadj : ∀ w ∈ F, G.Adj u w := by
      intro w hw
      obtain ⟨hwIO, hpw⟩ := mem_filter.mp hw
      rw [← hpw]
      exact (hpar w (hIO_ne w hwIO)).1
    have hFind : (F : Set α).Pairwise fun x y => ¬ G.Adj x y := by
      intro x hx y hy hxy
      exact hind (mem_filter.mp (mem_filter.mp hx).1).1 (mem_filter.mp (mem_filter.mp hy).1).1 hxy
    by_cases huv : u = v
    · simp only [huv, ite_true]
      have := card_le_indepNeighborsCard (u := u) hFadj hFind
      have := hL u
      omega
    · simp only [huv, ite_false, add_zero]
      obtain ⟨x, hxu, hxd⟩ := exists_parent h huv
      -- every child `w` of `u` is at distance `dist v u + 1`
      have hFd : ∀ w ∈ F, G.dist v w = G.dist v u + 1 := by
        intro w hw
        obtain ⟨hwIO, hpw⟩ := mem_filter.mp hw
        have := (hpar w (hIO_ne w hwIO)).2
        rw [hpw] at this
        omega
      have hxF : x ∉ F := by
        intro hx
        have := hFd x hx
        omega
      have hcard := card_le_indepNeighborsCard (u := u) (S := insert x F)
        (by
          intro t ht
          rcases mem_insert.mp ht with rfl | ht
          · exact hxu.symm
          · exact hFadj t ht)
        (by
          rw [coe_insert, Set.pairwise_insert]
          refine ⟨hFind, fun w hw _ => ⟨fun hadj => ?_, fun hadj => ?_⟩⟩
          · have hdw := hFd w hw
            rcases hadj.diff_dist_adj (u := v) with h' | h' | h' <;> omega
          · have hdw := hFd w hw
            rcases hadj.symm.diff_dist_adj (u := v) with h' | h' | h' <;> omega)
      rw [card_insert_of_notMem hxF] at hcard
      have := hL u
      omega
  -- (3) sum the fibres:  |I ∩ odd| + |P| ≤ L·|P| + 1
  have h2 : IO.card + P.card ≤ L * P.card + 1 := by
    have hsum : IO.card = ∑ u ∈ P, (IO.filter fun w => par w = u).card :=
      card_eq_sum_card_fiberwise (fun w hw => mem_image_of_mem par hw)
    have hb : ∑ u ∈ P, ((IO.filter fun w => par w = u).card + 1)
        ≤ ∑ u ∈ P, (L + if u = v then 1 else 0) := sum_le_sum hfib
    rw [sum_add_distrib, sum_add_distrib, sum_const, sum_const, smul_eq_mul, smul_eq_mul,
      mul_one, ← hsum, sum_ite_eq' P v (fun _ => 1)] at hb
    have : (if v ∈ P then 1 else 0) ≤ 1 := by split_ifs <;> omega
    rw [mul_comm]
    omega
  -- (4) combine, using `|P| ≤ |E|` and `L ≥ 2`
  have hD : distEven G v = E.card := rfl
  rw [hD]
  have hPE : P.card ≤ E.card := by omega
  obtain ⟨M, rfl⟩ : ∃ M, L = M + 2 := ⟨L - 2, by omega⟩
  have : M * P.card ≤ M * E.card := Nat.mul_le_mul_left M hPE
  nlinarith

/-! ### The conjecture -/

variable [Nontrivial α]

/-- **WOWII Conjecture 96** (statement verbatim from formal-conjectures). -/
theorem conjecture96 (G : SimpleGraph α) (h : G.Connected) :
    let minDistEven := (Finset.univ.image (distEven G)).min' (by simp)
    let maxL := (Finset.univ.image (fun v => indepNeighborsCard G v)).max' (by simp)
    (G.indepNum : ℝ) ≤ 1 + (minDistEven : ℝ) * ((maxL : ℝ) - 1) := by
  intro minDistEven maxL
  obtain ⟨v, -, hv⟩ := mem_image.mp (min'_mem (univ.image (distEven G)) (by simp))
  have hmin : distEven G v = minDistEven := hv
  have hL : ∀ u, indepNeighborsCard G u ≤ maxL := fun u =>
    le_max' _ _ (mem_image_of_mem _ (mem_univ u))
  -- `maxL ≥ 1`: a nontrivial connected graph has an edge
  have hL1 : 1 ≤ maxL := by
    obtain ⟨a, b, hab⟩ := exists_pair_ne α
    obtain ⟨q, hq⟩ := h.exists_walk_length_eq_dist a b
    have hnil : ¬ q.Nil := fun hn => hab hn.eq
    have : ({q.snd} : Finset α).card ≤ indepNeighborsCard G a :=
      card_le_indepNeighborsCard (by simpa using q.adj_snd hnil) (by simp)
    simp at this
    exact this.trans (hL a)
  rcases Nat.lt_or_ge maxL 2 with hlt | hge
  · -- every neighbourhood is a clique, so `G` is complete
    have hα := indepNum_le_one_of_local h (fun u => (hL u).trans (by omega))
    have : (maxL : ℝ) = 1 := by exact_mod_cast (by omega : maxL = 1)
    rw [this]
    have : (G.indepNum : ℝ) ≤ 1 := by exact_mod_cast hα
    linarith
  · have hk := key G h v maxL hge hL
    rw [hmin] at hk
    have hk' : (G.indepNum : ℝ) + minDistEven ≤ 1 + (minDistEven : ℝ) * maxL := by
      exact_mod_cast hk
    nlinarith

end OpenMath.WOWII96
