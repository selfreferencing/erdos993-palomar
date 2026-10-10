module

public import Erdos993Lean.Analytic.V213.SmallForestInventory
public import Erdos993Lean.Analytic.V213.Foundation

/-!
Section 7's signed-index decomposition and the nonnegative-p regime
of affine summation. Real weights are unrestricted in the identities. All
subtractions a-h in the affine coefficients are real, never truncated natural
subtractions. No finite certificate family or small-forest theorem is used.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.SmallForest

open Finset

noncomputable def binom (m : ℕ) (j : ℤ) : ℝ :=
  if 0 ≤ j then (m.choose j.toNat : ℝ) else 0

noncomputable def G (w : ℝ) (j : ℤ) (m : ℕ) : ℝ :=
  binom m j - w * binom m (j - 1) - (1 - w) * binom m (j + 1)

theorem binom_nat (m j : ℕ) : binom m (j : ℤ) = (m.choose j : ℝ) := by
  simp [binom]

theorem binom_sub_nat (m k h : ℕ) :
    binom m ((k : ℤ) - h) = if h ≤ k then (m.choose (k - h) : ℝ) else 0 := by
  by_cases hh : h ≤ k
  · have hz : 0 ≤ (k : ℤ) - h := by omega
    have ht : ((k : ℤ) - h).toNat = k - h := by omega
    simp [binom, hh, hz, ht]
  · have hz : ¬ 0 ≤ (k : ℤ) - h := by omega
    simp [binom, hh, hz]

theorem G_zero_below (w : ℝ) {j : ℤ} (hj : j ≤ -2) (m : ℕ) : G w j m = 0 := by
  have h0 : ¬ 0 ≤ j := by omega
  have h1 : ¬ 0 ≤ j - 1 := by omega
  have h2 : ¬ 0 ≤ j + 1 := by omega
  simp only [G, binom, if_neg h0, if_neg h1, if_neg h2, mul_zero, sub_zero]

variable (F : FiniteForest) [DecidableRel F.graph.Adj]

noncomputable def variation (k : ℕ) (w : ℝ) : ℝ :=
  w * ((indepCount F.graph univ k : ℝ) - indepCount F.graph univ (k - 1)) +
    (1 - w) * ((indepCount F.graph univ k : ℝ) - indepCount F.graph univ (k + 1))

noncomputable def row (A : Finset (Fin F.n)) (k : ℕ) (w : ℝ) (h : ℕ) : ℝ :=
  ∑ J ∈ Fiber.indepSubsets F.graph Aᶜ h,
    G w ((k : ℤ) - h) (available F A J).card

theorem variation_eq_counts (k : ℕ) (w : ℝ) :
    variation F k w =
      w * ((independenceCount F k : ℝ) - independenceCount F (k - 1)) +
      (1 - w) * ((independenceCount F k : ℝ) - independenceCount F (k + 1)) := by
  simp only [variation, independenceCount, indepCount_univ]
  congr 7

theorem variation_nonpos_of_valley {k : ℕ} {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hleft : independenceCount F k ≤ independenceCount F (k - 1))
    (hright : independenceCount F k ≤ independenceCount F (k + 1)) :
    variation F k w ≤ 0 := by
  rw [variation_eq_counts]
  have hl : (independenceCount F k : ℝ) ≤ independenceCount F (k - 1) := by
    exact_mod_cast hleft
  have hr : (independenceCount F k : ℝ) ≤ independenceCount F (k + 1) := by
    exact_mod_cast hright
  exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos hw0 (sub_nonpos.mpr hl))
    (mul_nonpos_of_nonneg_of_nonpos (by linarith) (sub_nonpos.mpr hr))

private theorem independent_finset {A : Finset (Fin F.n)}
    (hA : F.graph.IsIndepSet (A : Set (Fin F.n))) : IsIndepFinset F.graph A := by
  intro x hx y hy hxy
  exact hA (mem_coe.mpr hx) (mem_coe.mpr hy) (F.graph.ne_of_adj hxy) hxy

theorem coefficient_decomposition (A : Finset (Fin F.n))
    (hA : F.graph.IsIndepSet (A : Set (Fin F.n))) (r : ℕ) :
    (indepCount F.graph univ r : ℝ) =
      ∑ J ∈ (Aᶜ).powerset.filter (IsIndepFinset F.graph),
        binom (available F A J).card ((r : ℤ) - J.card) := by
  have hn := Zhang.indepCount_decomposition (independent_finset F hA)
    (Finset.subset_univ A) r
  have hu : (univ : Finset (Fin F.n)) \ A = Aᶜ := by ext x; simp
  rw [hu] at hn
  have hr := congrArg (fun n : ℕ => (n : ℝ)) hn
  push_cast at hr
  rw [hr]
  apply sum_congr rfl
  intro J _
  rw [binom_sub_nat]
  by_cases hh : J.card ≤ r <;> simp [hh, available]

theorem variation_decomposition (A : Finset (Fin F.n))
    (hA : F.graph.IsIndepSet (A : Set (Fin F.n))) {k : ℕ} (hk : 1 ≤ k) (w : ℝ) :
    variation F k w = ∑ J ∈ (Aᶜ).powerset.filter (IsIndepFinset F.graph),
      G w ((k : ℤ) - J.card) (available F A J).card := by
  unfold variation
  rw [coefficient_decomposition F A hA k,
    coefficient_decomposition F A hA (k - 1),
    coefficient_decomposition F A hA (k + 1)]
  simp only [← sum_sub_distrib, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro J _
  have hm : ((k - 1 : ℕ) : ℤ) - J.card = (k : ℤ) - J.card - 1 := by omega
  have hp : ((k + 1 : ℕ) : ℤ) - J.card = (k : ℤ) - J.card + 1 := by omega
  rw [hm, hp]
  unfold G
  ring

theorem row_zero_above_complement (A : Finset (Fin F.n)) (k : ℕ) (w : ℝ)
    {h : ℕ} (hh : (Aᶜ).card < h) : row F A k w h = 0 := by
  simp [row, Fiber.indepSubsets, powersetCard_eq_empty.mpr hh]

theorem row_zero_above_rank (A : Finset (Fin F.n)) (k : ℕ) (w : ℝ)
    {h : ℕ} (hh : k + 2 ≤ h) : row F A k w h = 0 := by
  unfold row
  apply sum_eq_zero
  intro J _
  exact G_zero_below w (by omega) _

theorem row_zero (A : Finset (Fin F.n)) (k : ℕ) (w : ℝ) :
    row F A k w 0 = G w (k : ℤ) A.card := by
  have he : IsIndepFinset F.graph (∅ : Finset (Fin F.n)) := by
    intro x hx; simp at hx
  unfold row Fiber.indepSubsets
  rw [powersetCard_zero, filter_singleton]
  simp only [he, if_true, sum_singleton, Nat.cast_zero, sub_zero]
  congr 1
  unfold available Zhang.avail
  simp

theorem variation_eq_sum_rows (A : Finset (Fin F.n))
    (hA : F.graph.IsIndepSet (A : Set (Fin F.n))) {k : ℕ} (hk : 1 ≤ k) (w : ℝ) :
    variation F k w = ∑ h ∈ range (k + 2), row F A k w h := by
  have hmap : ∀ J ∈ (Aᶜ).powerset.filter (IsIndepFinset F.graph),
      J.card ∈ range ((Aᶜ).card + 1) := by
    intro J hJ
    exact mem_range.mpr (Nat.lt_succ_of_le (card_le_card (mem_powerset.mp (mem_filter.mp hJ).1)))
  have hgroup := sum_fiberwise_of_maps_to hmap
    (fun J => G w ((k : ℤ) - J.card) (available F A J).card)
  have hf : ∀ h : ℕ,
      (((Aᶜ).powerset.filter (IsIndepFinset F.graph)).filter (fun J => J.card = h)) =
      Fiber.indepSubsets F.graph Aᶜ h := by
    intro h
    ext J
    simp [Fiber.indepSubsets, mem_powersetCard, and_assoc, and_left_comm, and_comm]
  have hc : variation F k w = ∑ h ∈ range ((Aᶜ).card + 1), row F A k w h := by
    rw [variation_decomposition F A hA hk, ← hgroup]
    apply sum_congr rfl
    intro h _
    unfold row
    rw [hf]
    apply sum_congr rfl
    intro J hJ
    have he := (mem_powersetCard.mp (mem_filter.mp hJ).1).2
    simp only [row, he]
  rw [hc]
  let r := max ((Aᶜ).card + 1) (k + 2)
  have hc' : (∑ h ∈ range ((Aᶜ).card + 1), row F A k w h) =
      ∑ h ∈ range r, row F A k w h := by
    apply sum_subset (range_mono (le_max_left _ _))
    intro h _ hn
    exact row_zero_above_complement F A k w (by
      have := not_lt.mp (fun ht => hn (mem_range.mpr ht)); omega)
  have hk' : (∑ h ∈ range (k + 2), row F A k w h) =
      ∑ h ∈ range r, row F A k w h := by
    apply sum_subset (range_mono (le_max_right _ _))
    intro h _ hn
    exact row_zero_above_rank F A k w (not_lt.mp (fun ht => hn (mem_range.mpr ht)))
  exact hc'.trans hk'.symm

theorem variation_eq_empty_add_rows (A : Finset (Fin F.n))
    (hA : F.graph.IsIndepSet (A : Set (Fin F.n))) {k : ℕ} (hk : 1 ≤ k) (w : ℝ) :
    variation F k w = G w (k : ℤ) A.card + ∑ h ∈ Icc 1 (k + 1), row F A k w h := by
  rw [variation_eq_sum_rows F A hA hk]
  have hs : range (k + 2) = insert 0 (Icc 1 (k + 1)) := by
    ext h
    simp only [mem_range, mem_insert, mem_Icc]
    omega
  rw [hs, sum_insert (by simp), row_zero]

theorem line_sum_eq (A : Finset (Fin F.n)) (h : ℕ) (β q : ℝ) :
    (∑ J ∈ Fiber.indepSubsets F.graph Aᶜ h,
      (β + q * (available F A J).card)) =
    (β + q * ((A.card : ℝ) - h)) * (N F A h : ℝ) - q * (E F A h : ℝ) := by
  have he : (E F A h : ℝ) = ∑ J ∈ Fiber.indepSubsets F.graph Aᶜ h,
      ((A.card : ℝ) - h - (available F A J).card) := by
    rw [E_eq_sum_excess]
    push_cast
    apply sum_congr rfl
    intro J hJ
    rw [excess_eq_card_sub_available]
    push_cast
    have hc := (mem_powersetCard.mp (mem_filter.mp hJ).1).2
    rw [hc]
  have hn : (N F A h : ℝ) = ((Fiber.indepSubsets F.graph Aᶜ h).card : ℝ) := by
    rw [N_eq_card_independent_subsets]
    rfl
  rw [he, hn]
  simp only [sum_sub_distrib, sum_add_distrib, ← mul_sum, sum_const,
    nsmul_eq_mul]
  ring

theorem row_line_bound (A : Finset (Fin F.n))
    (hA : F.graph.IsIndepSet (A : Set (Fin F.n)))
    (hmax : ∀ S : Finset (Fin F.n), F.graph.IsIndepSet (S : Set (Fin F.n)) → S.card ≤ A.card)
    (k h : ℕ) (w β q : ℝ)
    (hline : ∀ m : ℕ, m + h ≤ A.card → β + q * m ≤ G w ((k : ℤ) - h) m) :
    (β + q * ((A.card : ℝ) - h)) * (N F A h : ℝ) - q * (E F A h : ℝ) ≤
      row F A k w h := by
  rw [← line_sum_eq]
  apply sum_le_sum
  intro J hJ
  have hj := mem_powersetCard.mp (mem_filter.mp hJ).1
  have hb := support_card_add_le F A J hA hmax hj.1 (mem_filter.mp hJ).2
  apply hline
  omega

end Erdos993Lean.Analytic.V213.SmallForest

#check Erdos993Lean.Analytic.V213.SmallForest.binom_nat
#print axioms Erdos993Lean.Analytic.V213.SmallForest.binom_nat
#check Erdos993Lean.Analytic.V213.SmallForest.binom_sub_nat
#print axioms Erdos993Lean.Analytic.V213.SmallForest.binom_sub_nat
#check Erdos993Lean.Analytic.V213.SmallForest.G_zero_below
#print axioms Erdos993Lean.Analytic.V213.SmallForest.G_zero_below
#check Erdos993Lean.Analytic.V213.SmallForest.coefficient_decomposition
#print axioms Erdos993Lean.Analytic.V213.SmallForest.coefficient_decomposition
#check Erdos993Lean.Analytic.V213.SmallForest.variation_eq_counts
#print axioms Erdos993Lean.Analytic.V213.SmallForest.variation_eq_counts
#check Erdos993Lean.Analytic.V213.SmallForest.variation_nonpos_of_valley
#print axioms Erdos993Lean.Analytic.V213.SmallForest.variation_nonpos_of_valley
#check Erdos993Lean.Analytic.V213.SmallForest.variation_decomposition
#print axioms Erdos993Lean.Analytic.V213.SmallForest.variation_decomposition
#check Erdos993Lean.Analytic.V213.SmallForest.row_zero_above_complement
#print axioms Erdos993Lean.Analytic.V213.SmallForest.row_zero_above_complement
#check Erdos993Lean.Analytic.V213.SmallForest.row_zero_above_rank
#print axioms Erdos993Lean.Analytic.V213.SmallForest.row_zero_above_rank
#check Erdos993Lean.Analytic.V213.SmallForest.row_zero
#print axioms Erdos993Lean.Analytic.V213.SmallForest.row_zero
#check Erdos993Lean.Analytic.V213.SmallForest.variation_eq_sum_rows
#print axioms Erdos993Lean.Analytic.V213.SmallForest.variation_eq_sum_rows
#check Erdos993Lean.Analytic.V213.SmallForest.variation_eq_empty_add_rows
#print axioms Erdos993Lean.Analytic.V213.SmallForest.variation_eq_empty_add_rows
#check Erdos993Lean.Analytic.V213.SmallForest.line_sum_eq
#print axioms Erdos993Lean.Analytic.V213.SmallForest.line_sum_eq
#check Erdos993Lean.Analytic.V213.SmallForest.row_line_bound
#print axioms Erdos993Lean.Analytic.V213.SmallForest.row_line_bound
