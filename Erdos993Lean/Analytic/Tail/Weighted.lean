module

public import Mathlib
public import Erdos993Lean.IndependencePoly
public import Erdos993Lean.Floor.TreeDecomp

/-!
# The tail input T3, part 1: weighted independence sums over vertex subsets

Source: the note
T23, §3 (the hard-core model of a forest rooted at
C-vertices, downward ratios, the toy-unit lemma).

For a graph `G` on `V`, vertex weights `wt : V → ℝ` and a finite vertex set `s`,

  `Zw G wt s = ∑_{I ⊆ s independent} ∏_{v ∈ I} wt v`

is the partition function of the hard-core model of `G[s]` with vertex activities `wt`.  With the
uniform weight `t` it is the partition function `Z_{G[s]}(t)`; with weight `t` on `C` and `t z` on
`B` it is the numerator of the Laplace transform `E[z^{K_B}]` (T23 §1).  Working with vertex
subsets of one fixed graph keeps every recursion inside `V` (as `indepPoly` does).

Main results:
* `Zw_erase_add`, `sum_mem_eq`: the vertex recurrence `Z(s) = Z(s - v) + wt v · Z(s - N[v])`, and
  the sum over the independent sets containing `v` is `wt v · Z(s - N[v])`;
* `Zw_union`, `Zw_biUnion`: multiplicativity over edge-free disjoint unions;
* `Zw_erase_root`, `Zw_outside_root`: for a connected `s` of an acyclic graph with root `r`,
  `Z(s - r)` and `Z(s - N[r])` are the products over the branches `C_w` of `Z(C_w)` and
  `Z(C_w - w)` (the rooted decomposition of `Floor/TreeDecomp.lean`);
* positivity and monotonicity: `one_le_Zw`, `Zw_mono`, `Zw_add_le_of_mem`, `Zw_le_Zw`;
* `Zw_const_eq_sum_count`: with a uniform weight, `Z(s) = ∑_k i_k(s) t^k`.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.Tail

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

variable (G) in
/-- `Z_wt(s) = ∑_{I ⊆ s independent} ∏_{v ∈ I} wt v`: the hard-core partition function of `G[s]`
with vertex activities `wt`. -/
noncomputable def Zw (wt : V → ℝ) (s : Finset V) : ℝ :=
  ∑ I ∈ s.powerset.filter (IsIndepFinset G), ∏ v ∈ I, wt v

omit [DecidableEq V] in
theorem Zw_empty (wt : V → ℝ) : Zw G wt ∅ = 1 := by
  have h : IsIndepFinset G (∅ : Finset V) := fun v hv => absurd hv (Finset.notMem_empty v)
  rw [Zw, Finset.powerset_empty, Finset.filter_singleton, if_pos h, Finset.sum_singleton,
    Finset.prod_empty]

/-- The independent sets of `s` avoiding `v` are those of `s - v`. -/
theorem sum_not_mem_eq (wt : V → ℝ) (s : Finset V) (v : V) :
    ∑ I ∈ (s.powerset.filter (IsIndepFinset G)).filter (fun I => v ∉ I), ∏ u ∈ I, wt u =
      Zw G wt (s.erase v) := by
  unfold Zw
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext I
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_erase]
  tauto

/-- The independent sets of `s` containing `v` contribute `wt v · Z(s - N[v])`. -/
theorem sum_mem_eq (wt : V → ℝ) {s : Finset V} {v : V} (hv : v ∈ s) :
    ∑ I ∈ (s.powerset.filter (IsIndepFinset G)).filter (fun I => v ∈ I), ∏ u ∈ I, wt u =
      wt v * Zw G wt (outsideClosedNbhd G s v) := by
  unfold Zw
  rw [Finset.mul_sum]
  refine Finset.sum_nbij' (fun I => I.erase v) (fun u => insert v u) ?_ ?_ ?_ ?_ ?_
  · intro I hI
    simp only [Finset.mem_filter, Finset.mem_powerset] at hI ⊢
    obtain ⟨⟨hIs, hIi⟩, hvI⟩ := hI
    refine ⟨?_, ?_⟩
    · intro w hw
      rw [Finset.mem_erase] at hw
      simp only [outsideClosedNbhd, Finset.mem_filter]
      exact ⟨hIs hw.2, hw.1, hIi v hvI w hw.2⟩
    · exact fun a ha b hb => hIi a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb)
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_powerset] at hu ⊢
    obtain ⟨hus, hui⟩ := hu
    refine ⟨⟨?_, ?_⟩, Finset.mem_insert_self v u⟩
    · intro w hw
      rw [Finset.mem_insert] at hw
      rcases hw with rfl | hw
      · exact hv
      · exact (Finset.mem_filter.mp (hus hw)).1
    · intro a ha b hb
      rw [Finset.mem_insert] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact G.irrefl
      · exact (Finset.mem_filter.mp (hus hb)).2.2
      · exact fun h => (Finset.mem_filter.mp (hus ha)).2.2 h.symm
      · exact hui a ha b hb
  · intro I hI
    simp only [Finset.mem_filter] at hI
    exact Finset.insert_erase hI.2
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_powerset] at hu
    apply Finset.erase_insert
    intro hvu
    exact (Finset.mem_filter.mp (hu.1 hvu)).2.1 rfl
  · intro I hI
    simp only [Finset.mem_filter] at hI
    exact (Finset.mul_prod_erase I wt hI.2).symm

/-- **The vertex recurrence**: `Z(s) = Z(s - v) + wt v · Z(s - N[v])` for `v ∈ s`. -/
theorem Zw_erase_add (wt : V → ℝ) {s : Finset V} {v : V} (hv : v ∈ s) :
    Zw G wt s = Zw G wt (s.erase v) + wt v * Zw G wt (outsideClosedNbhd G s v) := by
  rw [← sum_not_mem_eq, ← sum_mem_eq wt hv, Zw]
  exact (Finset.sum_filter_not_add_sum_filter _ (fun I => v ∈ I) _).symm

/-- **Multiplicativity** over a disjoint union with no edges between the two parts. -/
theorem Zw_union (wt : V → ℝ) {s t : Finset V} (hst : Disjoint s t)
    (hno : ∀ a ∈ s, ∀ b ∈ t, ¬ G.Adj a b) :
    Zw G wt (s ∪ t) = Zw G wt s * Zw G wt t := by
  unfold Zw
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_nbij' (fun u => (u ∩ s, u ∩ t)) (fun p => p.1 ∪ p.2) ?_ ?_ ?_ ?_ ?_
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_product] at hu ⊢
    obtain ⟨_, hui⟩ := hu
    refine ⟨⟨Finset.inter_subset_right, ?_⟩, ⟨Finset.inter_subset_right, ?_⟩⟩
    · exact fun a ha b hb => hui a (Finset.mem_of_mem_inter_left ha) b
        (Finset.mem_of_mem_inter_left hb)
    · exact fun a ha b hb => hui a (Finset.mem_of_mem_inter_left ha) b
        (Finset.mem_of_mem_inter_left hb)
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_product] at hab ⊢
    obtain ⟨⟨has, hai⟩, ⟨hbt, hbi⟩⟩ := hab
    refine ⟨Finset.union_subset_union has hbt, ?_⟩
    intro x hx y hy
    rw [Finset.mem_union] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact hai x hx y hy
    · exact hno x (has hx) y (hbt hy)
    · exact fun h => hno y (has hy) x (hbt hx) h.symm
    · exact hbi x hx y hy
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_powerset] at hu
    dsimp only
    rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr hu.1]
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_product] at hab
    obtain ⟨⟨has, _⟩, ⟨hbt, _⟩⟩ := hab
    have h1 : Disjoint b s := (hst.mono_right hbt).symm
    have h2 : Disjoint a t := hst.mono_left has
    simp only [Prod.mk.injEq]
    constructor
    · rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr has,
        Finset.disjoint_iff_inter_eq_empty.mp h1, Finset.union_empty]
    · rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hbt,
        Finset.disjoint_iff_inter_eq_empty.mp h2, Finset.empty_union]
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_powerset] at hu
    have hu' : u = u ∩ s ∪ u ∩ t := by
      rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr hu.1]
    have hd : Disjoint (u ∩ s) (u ∩ t) :=
      hst.mono Finset.inter_subset_right Finset.inter_subset_right
    show ∏ v ∈ u, wt v = (∏ v ∈ u ∩ s, wt v) * ∏ v ∈ u ∩ t, wt v
    rw [← Finset.prod_union hd, ← hu']

/-- Multiplicativity over a finite family of pairwise disjoint parts with no edges between
distinct parts. -/
theorem Zw_biUnion (wt : V → ℝ) {ι : Type*} [DecidableEq ι] (I : Finset ι) (f : ι → Finset V)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (f i) (f j))
    (hno : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ∀ a ∈ f i, ∀ b ∈ f j, ¬ G.Adj a b) :
    Zw G wt (I.biUnion f) = ∏ i ∈ I, Zw G wt (f i) := by
  induction I using Finset.induction_on with
  | empty => simp [Zw_empty]
  | insert i I hiI ih =>
    rw [Finset.biUnion_insert, Finset.prod_insert hiI]
    rw [Zw_union wt ?_ ?_, ih ?_ ?_]
    · intro j hj k hk hjk
      exact hdisj j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hjk
    · intro j hj k hk hjk
      exact hno j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hjk
    · rw [Finset.disjoint_biUnion_right]
      intro j hj
      exact hdisj i (Finset.mem_insert_self i I) j (Finset.mem_insert_of_mem hj)
        (fun h => hiI (h ▸ hj))
    · intro a ha b hb
      rw [Finset.mem_biUnion] at hb
      obtain ⟨j, hj, hbj⟩ := hb
      exact hno i (Finset.mem_insert_self i I) j (Finset.mem_insert_of_mem hj)
        (fun h => hiI (h ▸ hj)) a ha b hbj

/-! ### The rooted decomposition -/

/-- `Z(s - r)` is the product over the branches at `r`. -/
theorem Zw_erase_root (hG : G.IsAcyclic) (wt : V → ℝ) {s : Finset V} (hs : ConnectedIn G s)
    {r : V} (hr : r ∈ s) :
    Zw G wt (s.erase r) = ∏ w ∈ nbrsIn G s r, Zw G wt (compIn G (s.erase r) w) := by
  conv_lhs => rw [erase_eq_biUnion hs hr]
  exact Zw_biUnion wt _ _ (fun i hi j hj hij => disjoint_branches hG hi hj hij)
    (fun i hi j hj hij a ha b hb => not_adj_branches hG hi hj hij ha hb)

/-- `Z(s - N[r])` is the product over the branches at `r` with their base vertices removed. -/
theorem Zw_outside_root (hG : G.IsAcyclic) (wt : V → ℝ) {s : Finset V} (hs : ConnectedIn G s)
    {r : V} (hr : r ∈ s) :
    Zw G wt (outsideClosedNbhd G s r) =
      ∏ w ∈ nbrsIn G s r, Zw G wt ((compIn G (s.erase r) w).erase w) := by
  rw [outsideClosedNbhd_eq_biUnion hG hs hr, Zw_biUnion]
  · intro i hi j hj hij
    exact (disjoint_branches hG hi hj hij).mono (Finset.erase_subset _ _) (Finset.erase_subset _ _)
  · intro i hi j hj hij a ha b hb
    exact not_adj_branches hG hi hj hij (Finset.mem_of_mem_erase ha) (Finset.mem_of_mem_erase hb)

/-! ### Positivity and monotonicity -/

omit [DecidableEq V] in
theorem Zw_nonneg {wt : V → ℝ} (hw : ∀ v, 0 ≤ wt v) (s : Finset V) : 0 ≤ Zw G wt s :=
  Finset.sum_nonneg fun _ _ => Finset.prod_nonneg fun v _ => hw v

omit [DecidableEq V] in
/-- `Z(s) ≥ 1` for nonnegative weights (the empty set). -/
theorem one_le_Zw {wt : V → ℝ} (hw : ∀ v, 0 ≤ wt v) (s : Finset V) : 1 ≤ Zw G wt s := by
  have h0 : (∅ : Finset V) ∈ s.powerset.filter (IsIndepFinset G) := by
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.empty_subset, true_and]
    exact fun v hv => absurd hv (Finset.notMem_empty v)
  calc (1 : ℝ) = ∏ v ∈ (∅ : Finset V), wt v := by simp
    _ ≤ Zw G wt s := Finset.single_le_sum (f := fun I : Finset V => ∏ v ∈ I, wt v)
        (fun I _ => Finset.prod_nonneg fun v _ => hw v) h0

omit [DecidableEq V] in
theorem Zw_pos {wt : V → ℝ} (hw : ∀ v, 0 ≤ wt v) (s : Finset V) : 0 < Zw G wt s :=
  lt_of_lt_of_le one_pos (one_le_Zw hw s)

omit [DecidableEq V] in
/-- `Z` is monotone under inclusion (nonnegative weights). -/
theorem Zw_mono {wt : V → ℝ} (hw : ∀ v, 0 ≤ wt v) {s s' : Finset V} (h : s ⊆ s') :
    Zw G wt s ≤ Zw G wt s' := by
  unfold Zw
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro I hI
    simp only [Finset.mem_filter, Finset.mem_powerset] at hI ⊢
    exact ⟨hI.1.trans h, hI.2⟩
  · intro I _ _
    exact Finset.prod_nonneg fun v _ => hw v

/-- Adding a vertex `u` of weight `wt u` increases `Z` by at least `wt u`. -/
theorem Zw_add_le_of_mem {wt : V → ℝ} (hw : ∀ v, 0 ≤ wt v) {s s' : Finset V} {u : V}
    (hu : u ∈ s') (h : s ⊆ s'.erase u) : Zw G wt s + wt u ≤ Zw G wt s' := by
  rw [Zw_erase_add wt hu]
  have h1 := Zw_mono (G := G) hw h
  have h2 := one_le_Zw (G := G) hw (outsideClosedNbhd G s' u)
  nlinarith [hw u]

omit [DecidableEq V] in
/-- `Z` is monotone in the weights (nonnegative weights). -/
theorem Zw_le_Zw {wt wt' : V → ℝ} (h0 : ∀ v, 0 ≤ wt v) (h : ∀ v, wt v ≤ wt' v) (s : Finset V) :
    Zw G wt s ≤ Zw G wt' s :=
  Finset.sum_le_sum fun _ _ => Finset.prod_le_prod₀ (fun v _ => h0 v) (fun v _ => h v)

theorem Zw_singleton (wt : V → ℝ) (v : V) : Zw G wt {v} = 1 + wt v := by
  rw [Zw_erase_add wt (Finset.mem_singleton_self v), Finset.erase_singleton, Zw_empty]
  have : outsideClosedNbhd G {v} v = ∅ := by
    ext x
    simp only [outsideClosedNbhd, Finset.mem_filter, Finset.mem_singleton, Finset.notMem_empty,
      iff_false, not_and]
    intro hx hxv
    exact absurd hx hxv
  rw [this, Zw_empty, mul_one]

omit [DecidableEq V] in
/-- With a uniform weight, `Z(s) = ∑_k i_k(s) t^k`. -/
theorem Zw_const_eq_sum_count (t : ℝ) (s : Finset V) :
    Zw G (fun _ => t) s = ∑ k ∈ range (s.card + 1), (indepCount G s k : ℝ) * t ^ k := by
  unfold Zw
  simp only [Finset.prod_const]
  have hmaps : ∀ I ∈ s.powerset.filter (IsIndepFinset G), I.card ∈ range (s.card + 1) := by
    intro I hI
    rw [Finset.mem_filter, Finset.mem_powerset] at hI
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.card_le_card hI.1))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_congr rfl (fun I hI => by rw [(Finset.mem_filter.mp hI).2]), Finset.sum_const,
    nsmul_eq_mul]
  rfl

end Erdos993Lean.Analytic.Tail
