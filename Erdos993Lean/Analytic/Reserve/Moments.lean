module

public import Mathlib
public import Erdos993Lean.Analytic.Tail.Rooted

/-!
# O1 by the two-generation reserve: moments of the selected count on vertex sets

Sources:
the two-generation reserve proof (the two boundary laws, recursion (1)).


For a graph `G` on `V`, a finite vertex set `s`, a set `B` and an activity `t ≥ 0`, the hard-core
law of `G[s]` gives the independent subset `I ⊆ s` the weight `t^|I| / Z(s)`.  The selected count is
`K_B = |I ∩ B|`.  We keep its raw moment sums

  `momB k s = ∑_{I ⊆ s independent} |I ∩ B|^k t^|I|`  (`k = 0, 1, 2`; `momB 0 s = Z(s)`),

its mean `meanB s = momB 1 s / momB 0 s` (the mean `U`) and variance
`varB s = momB 2 s / momB 0 s − (meanB s)²` (the variance `V`).

Main results:
* `momB_zero_eq_Zw`, `momB_zero_pos`: `momB 0` is the partition function `Zw`;
* `sum_indep_union`, `meanB_union`, `varB_union`, `meanB_biUnion`, `varB_biUnion`: the mean and the
  variance add over edge-free disjoint unions (product law);
* `sum_indep_erase_add`, `meanB_root`, `varB_root`: the root decomposition, i.e. the law of total
  variance for the mixture over `r ∈ I` (weight `p = rootProb G t s r`) and `r ∉ I` (weight `1 − p`):
  `U(s) = (1 − p) U(s − r) + p (a + U(s − N[r]))`,
  `V(s) = (1 − p) V(s − r) + p V(s − N[r]) + p (1 − p)(a + U(s − N[r]) − U(s − r))²`, `a = 1_B(r)`;
* `meanB_of_disjoint`, `varB_of_disjoint`: a vertex set without selected vertices has `U = V = 0`.

Scalarity check.  `meanB s` and `varB s` are the mean and variance of the selected count `K_B` under
the hard-core law of the actual vertex set `s` (the subtree with its parent unoccupied, `U⁰, V⁰`) or
of `s − r` (parent occupied, `U¹, V¹`); `rootProb` is the downward occupation message of the root.
They are produced here from the actual law and consumed by the tree recursion
(`Reserve/Induction.lean`) and the assembly (`Reserve/Assembly.lean`).
-/

@[expose] public section

namespace Erdos993Lean.Analytic.Reserve

open Finset Erdos993Lean.Analytic.Tail

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### Sums over independent subsets -/

/-- Sums over the independent subsets of an edge-free disjoint union are double sums. -/
theorem sum_indep_union {M : Type*} [AddCommMonoid M] (f : Finset V → M) {s t : Finset V}
    (hst : Disjoint s t) (hno : ∀ a ∈ s, ∀ b ∈ t, ¬ G.Adj a b) :
    ∑ I ∈ (s ∪ t).powerset.filter (IsIndepFinset G), f I =
      ∑ I ∈ s.powerset.filter (IsIndepFinset G),
        ∑ J ∈ t.powerset.filter (IsIndepFinset G), f (I ∪ J) := by
  rw [← Finset.sum_product']
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
    dsimp only
    rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr hu.1]

/-- **The vertex decomposition of sums over independent subsets**: for `r ∈ s`, the independent
subsets of `s` avoiding `r` are those of `s − r`, and those containing `r` are `insert r J` for the
independent subsets `J` of `s − N[r]`. -/
theorem sum_indep_erase_add {M : Type*} [AddCommMonoid M] (f : Finset V → M) {s : Finset V}
    {r : V} (hr : r ∈ s) :
    ∑ I ∈ s.powerset.filter (IsIndepFinset G), f I =
      ∑ I ∈ (s.erase r).powerset.filter (IsIndepFinset G), f I +
        ∑ J ∈ (outsideClosedNbhd G s r).powerset.filter (IsIndepFinset G), f (insert r J) := by
  rw [← Finset.sum_filter_not_add_sum_filter _ (fun I => r ∈ I)]
  congr 1
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext I
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_erase]
    tauto
  · refine Finset.sum_nbij' (fun I => I.erase r) (fun J => insert r J) ?_ ?_ ?_ ?_ ?_
    · intro I hI
      simp only [Finset.mem_filter, Finset.mem_powerset] at hI ⊢
      obtain ⟨⟨hIs, hIi⟩, hrI⟩ := hI
      refine ⟨?_, ?_⟩
      · intro w hw
        rw [Finset.mem_erase] at hw
        simp only [outsideClosedNbhd, Finset.mem_filter]
        exact ⟨hIs hw.2, hw.1, hIi r hrI w hw.2⟩
      · exact fun a ha b hb => hIi a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb)
    · intro J hJ
      simp only [Finset.mem_filter, Finset.mem_powerset] at hJ ⊢
      obtain ⟨hJs, hJi⟩ := hJ
      refine ⟨⟨?_, ?_⟩, Finset.mem_insert_self r J⟩
      · intro w hw
        rw [Finset.mem_insert] at hw
        rcases hw with rfl | hw
        · exact hr
        · exact (Finset.mem_filter.mp (hJs hw)).1
      · intro a ha b hb
        rw [Finset.mem_insert] at ha hb
        rcases ha with rfl | ha <;> rcases hb with rfl | hb
        · exact G.irrefl
        · exact (Finset.mem_filter.mp (hJs hb)).2.2
        · exact fun h => (Finset.mem_filter.mp (hJs ha)).2.2 h.symm
        · exact hJi a ha b hb
    · intro I hI
      simp only [Finset.mem_filter] at hI
      exact Finset.insert_erase hI.2
    · intro J hJ
      simp only [Finset.mem_filter, Finset.mem_powerset] at hJ
      apply Finset.erase_insert
      intro hrJ
      exact (Finset.mem_filter.mp (hJ.1 hrJ)).2.1 rfl
    · intro I hI
      simp only [Finset.mem_filter] at hI
      rw [Finset.insert_erase hI.2]

/-! ### Moment sums, mean and variance -/

variable (G) in
/-- The raw moment sums `∑_{I ⊆ s independent} |I ∩ B|^k t^|I|` of the selected count. -/
noncomputable def momB (B : Finset V) (t : ℝ) (k : ℕ) (s : Finset V) : ℝ :=
  ∑ I ∈ s.powerset.filter (IsIndepFinset G), ((I ∩ B).card : ℝ) ^ k * t ^ I.card

variable (G) in
/-- The mean `U(s) = E|I ∩ B|` under the hard-core law of `G[s]` at activity `t`. -/
noncomputable def meanB (B : Finset V) (t : ℝ) (s : Finset V) : ℝ :=
  momB G B t 1 s / momB G B t 0 s

variable (G) in
/-- The variance `V(s) = Var |I ∩ B|` under the hard-core law of `G[s]` at activity `t`. -/
noncomputable def varB (B : Finset V) (t : ℝ) (s : Finset V) : ℝ :=
  momB G B t 2 s / momB G B t 0 s - meanB G B t s ^ 2

/-- The selection indicator `a = 1_B(r)`. -/
noncomputable def aB (B : Finset V) (r : V) : ℝ := if r ∈ B then 1 else 0

theorem aB_cases (B : Finset V) (r : V) : aB B r = 0 ∨ aB B r = 1 := by
  unfold aB
  split_ifs
  · right; rfl
  · left; rfl

section Moments

variable {B : Finset V} {t : ℝ}

/-- `momB 0 s` is the partition function `Z(s)`. -/
theorem momB_zero_eq_Zw (s : Finset V) : momB G B t 0 s = Zw G (fun _ => t) s := by
  simp only [momB, Zw, pow_zero, one_mul, Finset.prod_const]

theorem momB_zero_pos (ht : 0 ≤ t) (s : Finset V) : 0 < momB G B t 0 s := by
  rw [momB_zero_eq_Zw]
  exact Zw_pos (fun _ => ht) s

theorem card_union_inter_eq {I J : Finset V} (h : Disjoint I J) :
    ((I ∪ J) ∩ B).card = (I ∩ B).card + (J ∩ B).card := by
  rw [Finset.union_inter_distrib_right, Finset.card_union_of_disjoint]
  exact h.mono Finset.inter_subset_left Finset.inter_subset_left

/-- The moment sums of an edge-free disjoint union, as a double sum. -/
theorem momB_union (k : ℕ) {s s' : Finset V} (hss : Disjoint s s')
    (hno : ∀ a ∈ s, ∀ b ∈ s', ¬ G.Adj a b) :
    momB G B t k (s ∪ s') =
      ∑ I ∈ s.powerset.filter (IsIndepFinset G), ∑ J ∈ s'.powerset.filter (IsIndepFinset G),
        (((I ∩ B).card : ℝ) + (J ∩ B).card) ^ k * (t ^ I.card * t ^ J.card) := by
  unfold momB
  rw [sum_indep_union _ hss hno]
  refine Finset.sum_congr rfl fun I hI => Finset.sum_congr rfl fun J hJ => ?_
  simp only [Finset.mem_filter, Finset.mem_powerset] at hI hJ
  have hd : Disjoint I J := hss.mono hI.1 hJ.1
  rw [card_union_inter_eq hd, Finset.card_union_of_disjoint hd, pow_add, Nat.cast_add]

theorem momB_union_zero {s s' : Finset V} (hss : Disjoint s s')
    (hno : ∀ a ∈ s, ∀ b ∈ s', ¬ G.Adj a b) :
    momB G B t 0 (s ∪ s') = momB G B t 0 s * momB G B t 0 s' := by
  rw [momB_union 0 hss hno]
  unfold momB
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun J _ => ?_
  ring

theorem momB_union_one {s s' : Finset V} (hss : Disjoint s s')
    (hno : ∀ a ∈ s, ∀ b ∈ s', ¬ G.Adj a b) :
    momB G B t 1 (s ∪ s') = momB G B t 1 s * momB G B t 0 s' + momB G B t 0 s * momB G B t 1 s' := by
  rw [momB_union 1 hss hno]
  unfold momB
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun J _ => ?_
  ring

theorem momB_union_two {s s' : Finset V} (hss : Disjoint s s')
    (hno : ∀ a ∈ s, ∀ b ∈ s', ¬ G.Adj a b) :
    momB G B t 2 (s ∪ s') = momB G B t 2 s * momB G B t 0 s' +
      2 * (momB G B t 1 s * momB G B t 1 s') + momB G B t 0 s * momB G B t 2 s' := by
  rw [momB_union 2 hss hno]
  unfold momB
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun J _ => ?_
  ring

/-- **The mean adds** over an edge-free disjoint union. -/
theorem meanB_union (ht : 0 ≤ t) {s s' : Finset V} (hss : Disjoint s s')
    (hno : ∀ a ∈ s, ∀ b ∈ s', ¬ G.Adj a b) :
    meanB G B t (s ∪ s') = meanB G B t s + meanB G B t s' := by
  have h1 := (momB_zero_pos (G := G) (B := B) ht s).ne'
  have h2 := (momB_zero_pos (G := G) (B := B) ht s').ne'
  unfold meanB
  rw [momB_union_one hss hno, momB_union_zero hss hno]
  field_simp

/-- **The variance adds** over an edge-free disjoint union (product law). -/
theorem varB_union (ht : 0 ≤ t) {s s' : Finset V} (hss : Disjoint s s')
    (hno : ∀ a ∈ s, ∀ b ∈ s', ¬ G.Adj a b) :
    varB G B t (s ∪ s') = varB G B t s + varB G B t s' := by
  have h1 := (momB_zero_pos (G := G) (B := B) ht s).ne'
  have h2 := (momB_zero_pos (G := G) (B := B) ht s').ne'
  unfold varB meanB
  rw [momB_union_two hss hno, momB_union_one hss hno, momB_union_zero hss hno]
  field_simp
  ring

theorem momB_empty (k : ℕ) : momB G B t k ∅ = if k = 0 then 1 else 0 := by
  have h : IsIndepFinset G (∅ : Finset V) := fun v hv => absurd hv (Finset.notMem_empty v)
  unfold momB
  rw [Finset.powerset_empty, Finset.filter_singleton, if_pos h, Finset.sum_singleton,
    Finset.empty_inter, Finset.card_empty, pow_zero, mul_one, Nat.cast_zero]
  split_ifs with hk
  · rw [hk, pow_zero]
  · exact zero_pow hk

theorem meanB_empty : meanB G B t ∅ = 0 := by
  simp [meanB, momB_empty]

theorem varB_empty : varB G B t ∅ = 0 := by
  simp [varB, meanB, momB_empty]

/-- The mean adds over a finite family of pairwise disjoint parts without edges between parts. -/
theorem meanB_biUnion (ht : 0 ≤ t) {ι : Type*} [DecidableEq ι] (I : Finset ι) (f : ι → Finset V)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (f i) (f j))
    (hno : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ∀ a ∈ f i, ∀ b ∈ f j, ¬ G.Adj a b) :
    meanB G B t (I.biUnion f) = ∑ i ∈ I, meanB G B t (f i) := by
  induction I using Finset.induction_on with
  | empty => simp [meanB_empty]
  | insert i I hiI ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hiI]
    rw [meanB_union ht ?_ ?_, ih ?_ ?_]
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

/-- The variance adds over a finite family of pairwise disjoint parts without edges between
parts. -/
theorem varB_biUnion (ht : 0 ≤ t) {ι : Type*} [DecidableEq ι] (I : Finset ι) (f : ι → Finset V)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (f i) (f j))
    (hno : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ∀ a ∈ f i, ∀ b ∈ f j, ¬ G.Adj a b) :
    varB G B t (I.biUnion f) = ∑ i ∈ I, varB G B t (f i) := by
  induction I using Finset.induction_on with
  | empty => simp [varB_empty]
  | insert i I hiI ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hiI]
    rw [varB_union ht ?_ ?_, ih ?_ ?_]
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

/-! ### The root decomposition -/

theorem card_insert_inter_eq {J : Finset V} {r : V} (hrJ : r ∉ J) :
    ((insert r J ∩ B).card : ℝ) = aB B r + (J ∩ B).card := by
  unfold aB
  by_cases hrB : r ∈ B
  · rw [Finset.insert_inter_of_mem hrB, Finset.card_insert_of_notMem
      (fun h => hrJ (Finset.mem_of_mem_inter_left h)), if_pos hrB]
    push_cast
    ring
  · rw [Finset.insert_inter_of_notMem hrB, if_neg hrB, zero_add]

/-- The moment sums at a vertex `r`: the part avoiding `r` and the part containing `r`. -/
theorem momB_root (k : ℕ) {s : Finset V} {r : V} (hr : r ∈ s) :
    momB G B t k s = momB G B t k (s.erase r) +
      t * ∑ J ∈ (outsideClosedNbhd G s r).powerset.filter (IsIndepFinset G),
        (aB B r + (J ∩ B).card) ^ k * t ^ J.card := by
  unfold momB
  rw [sum_indep_erase_add _ hr, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun J hJ => ?_
  have hrJ : r ∉ J := by
    intro h
    simp only [Finset.mem_filter, Finset.mem_powerset] at hJ
    exact (Finset.mem_filter.mp (hJ.1 h)).2.1 rfl
  rw [card_insert_inter_eq hrJ, Finset.card_insert_of_notMem hrJ, pow_succ]
  ring

theorem momB_root_zero {s : Finset V} {r : V} (hr : r ∈ s) :
    momB G B t 0 s = momB G B t 0 (s.erase r) + t * momB G B t 0 (outsideClosedNbhd G s r) := by
  rw [momB_root 0 hr]
  congr 2

theorem momB_root_one {s : Finset V} {r : V} (hr : r ∈ s) :
    momB G B t 1 s = momB G B t 1 (s.erase r) +
      t * (aB B r * momB G B t 0 (outsideClosedNbhd G s r) +
        momB G B t 1 (outsideClosedNbhd G s r)) := by
  rw [momB_root 1 hr]
  congr 2
  unfold momB
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun J _ => ?_
  ring

theorem momB_root_two {s : Finset V} {r : V} (hr : r ∈ s) :
    momB G B t 2 s = momB G B t 2 (s.erase r) +
      t * (aB B r ^ 2 * momB G B t 0 (outsideClosedNbhd G s r) +
        2 * aB B r * momB G B t 1 (outsideClosedNbhd G s r) +
        momB G B t 2 (outsideClosedNbhd G s r)) := by
  rw [momB_root 2 hr]
  congr 2
  unfold momB
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun J _ => ?_
  ring

/-- The downward message in terms of the moment sums: `p = t Z(s − N[r]) / Z(s)`. -/
theorem rootProb_eq_momB (s : Finset V) (r : V) :
    rootProb G t s r = t * momB G B t 0 (outsideClosedNbhd G s r) / momB G B t 0 s := by
  rw [rootProb, momB_zero_eq_Zw, momB_zero_eq_Zw]

theorem one_sub_rootProb_eq_momB (ht : 0 ≤ t) {s : Finset V} {r : V} (hr : r ∈ s) :
    1 - rootProb G t s r = momB G B t 0 (s.erase r) / momB G B t 0 s := by
  rw [one_sub_rootProb ht hr, momB_zero_eq_Zw, momB_zero_eq_Zw]

/-- **The root decomposition of the mean**: `U(s) = (1 − p) U(s − r) + p (a + U(s − N[r]))`. -/
theorem meanB_root (ht : 0 ≤ t) {s : Finset V} {r : V} (hr : r ∈ s) :
    meanB G B t s = (1 - rootProb G t s r) * meanB G B t (s.erase r) +
      rootProb G t s r * (aB B r + meanB G B t (outsideClosedNbhd G s r)) := by
  have hX := (momB_zero_pos (G := G) (B := B) ht (s.erase r)).ne'
  have hO := (momB_zero_pos (G := G) (B := B) ht (outsideClosedNbhd G s r)).ne'
  have hZ := (momB_zero_pos (G := G) (B := B) ht s).ne'
  rw [one_sub_rootProb_eq_momB (B := B) ht hr, rootProb_eq_momB (B := B)]
  unfold meanB
  rw [momB_root_one hr]
  field_simp

/-- **The root decomposition of the variance (law of total variance)**:
`V(s) = (1 − p) V(s − r) + p V(s − N[r]) + p (1 − p)(a + U(s − N[r]) − U(s − r))²`. -/
theorem varB_root (ht : 0 ≤ t) {s : Finset V} {r : V} (hr : r ∈ s) :
    varB G B t s = (1 - rootProb G t s r) * varB G B t (s.erase r) +
      rootProb G t s r * varB G B t (outsideClosedNbhd G s r) +
      rootProb G t s r * (1 - rootProb G t s r) *
        (aB B r + meanB G B t (outsideClosedNbhd G s r) - meanB G B t (s.erase r)) ^ 2 := by
  have hXp := momB_zero_pos (G := G) (B := B) ht (s.erase r)
  have hOp := momB_zero_pos (G := G) (B := B) ht (outsideClosedNbhd G s r)
  have hX := hXp.ne'
  have hO := hOp.ne'
  have h0 := momB_root_zero (G := G) (B := B) (t := t) hr
  have hZ' : momB G B t 0 (s.erase r) + t * momB G B t 0 (outsideClosedNbhd G s r) ≠ 0 := by
    have : 0 ≤ t * momB G B t 0 (outsideClosedNbhd G s r) := mul_nonneg ht hOp.le
    linarith
  rw [one_sub_rootProb_eq_momB (B := B) ht hr, rootProb_eq_momB (B := B)]
  unfold varB meanB
  rw [momB_root_two hr, momB_root_one hr, h0]
  field_simp
  ring

/-! ### Sets without selected vertices -/

theorem momB_of_disjoint {s : Finset V} (hsB : Disjoint s B) {k : ℕ} (hk : k ≠ 0) :
    momB G B t k s = 0 := by
  unfold momB
  refine Finset.sum_eq_zero fun I hI => ?_
  simp only [Finset.mem_filter, Finset.mem_powerset] at hI
  have : I ∩ B = ∅ := Finset.disjoint_iff_inter_eq_empty.mp (hsB.mono_left hI.1)
  rw [this, Finset.card_empty, Nat.cast_zero, zero_pow hk, zero_mul]

/-- A vertex set without selected vertices has `U = 0`. -/
theorem meanB_of_disjoint {s : Finset V} (hsB : Disjoint s B) : meanB G B t s = 0 := by
  unfold meanB
  rw [momB_of_disjoint hsB one_ne_zero, zero_div]

/-- A vertex set without selected vertices has `V = 0`. -/
theorem varB_of_disjoint {s : Finset V} (hsB : Disjoint s B) : varB G B t s = 0 := by
  unfold varB
  rw [meanB_of_disjoint hsB, momB_of_disjoint hsB two_ne_zero]
  simp

end Moments

end Erdos993Lean.Analytic.Reserve
