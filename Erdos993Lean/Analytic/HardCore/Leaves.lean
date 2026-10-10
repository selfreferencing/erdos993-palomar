module

public import Mathlib
public import Erdos993Lean.Analytic.HardCore.Basic

/-!
# Leaves and maximum-weight independent sets (Zhang, Lemma 4.1, first part)

Source: T. Zhang, *Exact
Certificates for Unimodality of Forest Independence Polynomials*, v1.1, Lemma 4.1 (proof, first
paragraph): for a leaf `u` whose component is not a single edge, with neighbour `v`,
`π_u = λ I_{F−{u,v}}(λ)/I_F(λ) > π_v = λ I_{F−N[v]}(λ)/I_F(λ)`; exchanging `v` for `u` would improve
a maximum-weight independent set, so `v ∉ B`, and maximality gives `u ∈ B`; isolated vertices are in
`B`, and each edge component has exactly one endpoint in `B`.  The note T23 §1: "Lemma 4.1
(leaves in B for non-K2 components) is the only structural property of B that T3 needs."

* `closedNbhd F v = N[v]` and `partitionFnAvoid F A t = Z_{F − A}(t)` (independent sets avoiding `A`);
* `marginal_mul_partitionFn_eq`: `π_v Z_F = t Z_{F − N[v]}` (the vertex recurrence at `v`);
* `partitionFnAvoid_lt`: `Z_{F − A'} < Z_{F − A}` for `A ⊆ A'` with a vertex of `A' \ A` (`t > 0`);
* `marginal_lt_marginal`: `N[u] ⊆ N[v]` with a vertex of `N[v] \ N[u]` gives `π_v < π_u`;
* `IsMaxWeight.mem_of_forall_not_adj`: a maximum-weight set contains every vertex with no neighbour
  in it (all marginals are positive at `t > 0`);
* **E4** `IsMaxWeight.leaf_mem` (a leaf `u` whose component is not a single edge: `v ∉ B`, `u ∈ B`),
  `IsMaxWeight.edge_mem` (for any leaf `u` with neighbour `v`, exactly one of `u`, `v` is in `B`;
  in particular each edge component has exactly one endpoint in `B`),
  `IsMaxWeight.isolated_mem` (isolated vertices are in `B`).

No acyclicity is used: the statements hold for the hard-core model of any finite graph.

Namespaces: the neighbourhood and partition-function facts are in
`Erdos993Lean.Analytic.HardCore`; the `IsMaxWeight.*` results are in
`Erdos993Lean.Analytic.IsMaxWeight` (dot notation `hB.leaf_mem`, ...).

Grade: PROVED IN LEAN (standard axioms only).
-/

@[expose] public section

namespace Erdos993Lean.Analytic

open Finset

namespace HardCore

variable (F : FiniteForest)

/-! ## Closed neighbourhoods and deleted partition functions -/

/-- The closed neighbourhood `N[v] = {v} ∪ {w : w ~ v}`. -/
noncomputable def closedNbhd (v : Fin F.n) : Finset (Fin F.n) := by
  classical
  exact univ.filter fun w => w = v ∨ F.graph.Adj v w

theorem mem_closedNbhd {v w : Fin F.n} : w ∈ closedNbhd F v ↔ w = v ∨ F.graph.Adj v w := by
  unfold closedNbhd
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- `Z_{F − A}(t)`: the partition function of `F` with the vertices of `A` deleted, as the sum of
`t^|S|` over the independent sets of `F` avoiding `A`. -/
noncomputable def partitionFnAvoid (A : Finset (Fin F.n)) (t : ℝ) : ℝ :=
  ∑ S ∈ (indepSets F).filter (fun S => Disjoint S A), t ^ S.card

/-- **The vertex recurrence at `v`**: `π_v Z_F(t) = t Z_{F − N[v]}(t)`. -/
theorem marginal_mul_partitionFn_eq {t : ℝ} (ht : 0 ≤ t) (v : Fin F.n) :
    marginal F t v * partitionFn F t = t * partitionFnAvoid F (closedNbhd F v) t := by
  rw [marginal_mul_partitionFn F ht, partitionFnAvoid, Finset.mul_sum]
  refine Finset.sum_nbij' (fun S => S.erase v) (fun S => insert v S) ?_ ?_ ?_ ?_ ?_
  · intro S hS
    rw [Finset.mem_filter] at hS
    have hSi := (mem_indepSets' F).mp hS.1
    rw [Finset.mem_filter]
    refine ⟨mem_indepSets_of_subset F hS.1 (Finset.erase_subset v S), ?_⟩
    rw [Finset.disjoint_left]
    intro w hw hwN
    rw [Finset.mem_erase] at hw
    rcases (mem_closedNbhd F).mp hwN with rfl | hadj
    · exact hw.1 rfl
    · exact hSi v hS.2 w hw.2 hadj
  · intro S hS
    rw [Finset.mem_filter] at hS
    have hSi := (mem_indepSets' F).mp hS.1
    have hvS : ∀ x ∈ S, ¬ F.graph.Adj v x := fun x hx hvx =>
      Finset.disjoint_left.mp hS.2 hx ((mem_closedNbhd F).mpr (Or.inr hvx))
    rw [Finset.mem_filter, mem_indepSets']
    refine ⟨?_, Finset.mem_insert_self v S⟩
    intro a ha b hb
    rw [Finset.mem_insert] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact F.graph.irrefl
    · exact hvS b hb
    · exact fun h => hvS a ha h.symm
    · exact hSi a ha b hb
  · intro S hS
    rw [Finset.mem_filter] at hS
    exact Finset.insert_erase hS.2
  · intro S hS
    rw [Finset.mem_filter] at hS
    apply Finset.erase_insert
    intro hvS
    exact Finset.disjoint_left.mp hS.2 hvS ((mem_closedNbhd F).mpr (Or.inl rfl))
  · intro S hS
    rw [Finset.mem_filter] at hS
    rw [← Finset.card_erase_add_one hS.2, pow_succ]
    ring

/-- Deleting more vertices strictly decreases the partition function at `t > 0`:
`Z_{F − A'} < Z_{F − A}` for `A ⊆ A'` and some `w ∈ A' \ A`. -/
theorem partitionFnAvoid_lt {A A' : Finset (Fin F.n)} (hAA' : A ⊆ A') {w : Fin F.n}
    (hwA' : w ∈ A') (hwA : w ∉ A) {t : ℝ} (ht : 0 < t) :
    partitionFnAvoid F A' t < partitionFnAvoid F A t := by
  unfold partitionFnAvoid
  refine Finset.sum_lt_sum_of_subset (i := {w}) ?_ ?_ ?_ (by positivity)
    (fun S _ _ => by positivity)
  · intro S hS
    rw [Finset.mem_filter] at hS ⊢
    exact ⟨hS.1, Finset.disjoint_of_subset_right hAA' hS.2⟩
  · rw [Finset.mem_filter]
    exact ⟨singleton_mem_indepSets F w, Finset.disjoint_singleton_left.mpr hwA⟩
  · rw [Finset.mem_filter]
    exact fun h => Finset.disjoint_singleton_left.mp h.2 hwA'

/-- If `N[u] ⊆ N[v]` and some `w ∈ N[v]` lies outside `N[u]`, then `π_v < π_u` at `t > 0`. -/
theorem marginal_lt_marginal {t : ℝ} (ht : 0 < t) {u v w : Fin F.n}
    (hsub : closedNbhd F u ⊆ closedNbhd F v) (hwv : w ∈ closedNbhd F v)
    (hwu : w ∉ closedNbhd F u) : marginal F t v < marginal F t u := by
  have hZ := partitionFn_pos F ht.le
  have hlt := partitionFnAvoid_lt F hsub hwv hwu ht
  have h : marginal F t v * partitionFn F t < marginal F t u * partitionFn F t := by
    rw [marginal_mul_partitionFn_eq F ht.le u, marginal_mul_partitionFn_eq F ht.le v]
    exact mul_lt_mul_of_pos_left hlt ht
  exact lt_of_mul_lt_mul_right h hZ.le

end HardCore

open HardCore

/-! ## Maximum-weight sets -/

variable {F : FiniteForest}

/-- A maximum-weight independent set at `t > 0` contains every vertex with no neighbour in it
(adding it keeps the set independent and adds `π_u > 0` to the weight). -/
theorem IsMaxWeight.mem_of_forall_not_adj {t : ℝ} (ht : 0 < t) {B : Finset (Fin F.n)}
    (hB : IsMaxWeight F t B) {u : Fin F.n} (hu : ∀ b ∈ B, ¬ F.graph.Adj u b) : u ∈ B := by
  classical
  by_contra huB
  have hBi := (isIndepSet_coe_iff F).mp hB.1
  have hB'i : F.graph.IsIndepSet ((insert u B : Finset (Fin F.n)) : Set (Fin F.n)) := by
    rw [isIndepSet_coe_iff]
    intro a ha b hb
    rw [Finset.mem_insert] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact F.graph.irrefl
    · exact hu b hb
    · exact fun h => hu a ha h.symm
    · exact hBi a ha b hb
  have hW : weightW F t (insert u B) = weightW F t B + marginal F t u := by
    unfold weightW
    rw [Finset.sum_insert huB]
    ring
  have h1 := hB.2 _ hB'i
  have h2 := marginal_pos F ht u
  linarith

/-- **E4 (Zhang, Lemma 4.1): leaves.**  Let `B` be a maximum-weight independent set at `t > 0`, `u`
a leaf with neighbour `v` (every neighbour of `u` is `v`), and suppose the component of `u` is not a
single edge (`v` has a neighbour `w ≠ u`).  Then `v ∉ B` and `u ∈ B`. -/
theorem IsMaxWeight.leaf_mem {t : ℝ} (ht : 0 < t) {B : Finset (Fin F.n)}
    (hB : IsMaxWeight F t B) {u v : Fin F.n} (huv : F.graph.Adj u v)
    (hleaf : ∀ x, F.graph.Adj u x → x = v) (hnot : ∃ w, F.graph.Adj v w ∧ w ≠ u) :
    v ∉ B ∧ u ∈ B := by
  classical
  obtain ⟨w, hvw, hwu⟩ := hnot
  have hsub : closedNbhd F u ⊆ closedNbhd F v := by
    intro x hx
    rw [mem_closedNbhd] at hx ⊢
    rcases hx with rfl | hux
    · exact Or.inr huv.symm
    · exact Or.inl (hleaf x hux)
  have hwv : w ∈ closedNbhd F v := (mem_closedNbhd F).mpr (Or.inr hvw)
  have hwu' : w ∉ closedNbhd F u := by
    rw [mem_closedNbhd]
    rintro (rfl | huw)
    · exact hwu rfl
    · exact F.graph.ne_of_adj hvw (hleaf w huw).symm
  have hlt := marginal_lt_marginal F ht hsub hwv hwu'
  have hBi := (isIndepSet_coe_iff F).mp hB.1
  have hvB : v ∉ B := by
    intro hvB
    have huB : u ∉ B := fun huB => hBi u huB v hvB huv
    have hB'i : F.graph.IsIndepSet
        ((insert u (B.erase v) : Finset (Fin F.n)) : Set (Fin F.n)) := by
      rw [isIndepSet_coe_iff]
      intro a ha b hb
      rw [Finset.mem_insert, Finset.mem_erase] at ha hb
      rcases ha with rfl | ⟨hav, haB⟩ <;> rcases hb with rfl | ⟨hbv, hbB⟩
      · exact F.graph.irrefl
      · exact fun hab => hbv (hleaf b hab)
      · exact fun hab => hav (hleaf a hab.symm)
      · exact hBi a haB b hbB
    have hW : weightW F t (insert u (B.erase v)) =
        weightW F t B - marginal F t v + marginal F t u := by
      unfold weightW
      rw [Finset.sum_insert (fun h => huB (Finset.mem_of_mem_erase h)),
        Finset.sum_erase_eq_sub hvB]
      ring
    have h1 := hB.2 _ hB'i
    linarith
  refine ⟨hvB, hB.mem_of_forall_not_adj ht fun b hb hub => ?_⟩
  exact hvB (hleaf b hub ▸ hb)

/-- **E4 (Zhang, Lemma 4.1): edge components.**  If `u` is a leaf with neighbour `v`, a
maximum-weight independent set at `t > 0` contains exactly one of `u`, `v`.  In particular each edge
component (both endpoints leaves) has exactly one endpoint in `B`. -/
theorem IsMaxWeight.edge_mem {t : ℝ} (ht : 0 < t) {B : Finset (Fin F.n)}
    (hB : IsMaxWeight F t B) {u v : Fin F.n} (huv : F.graph.Adj u v)
    (hu : ∀ x, F.graph.Adj u x → x = v) :
    (u ∈ B ∧ v ∉ B) ∨ (u ∉ B ∧ v ∈ B) := by
  have hBi := (isIndepSet_coe_iff F).mp hB.1
  by_cases hvB : v ∈ B
  · exact Or.inr ⟨fun huB => hBi u huB v hvB huv, hvB⟩
  · refine Or.inl ⟨hB.mem_of_forall_not_adj ht fun b hb hub => ?_, hvB⟩
    exact hvB (hu b hub ▸ hb)

/-- **E4 (Zhang, Lemma 4.1): isolated vertices** lie in every maximum-weight independent set at
`t > 0`. -/
theorem IsMaxWeight.isolated_mem {t : ℝ} (ht : 0 < t) {B : Finset (Fin F.n)}
    (hB : IsMaxWeight F t B) {u : Fin F.n} (hu : ∀ x, ¬ F.graph.Adj u x) : u ∈ B :=
  hB.mem_of_forall_not_adj ht fun b _ => hu b

end Erdos993Lean.Analytic
