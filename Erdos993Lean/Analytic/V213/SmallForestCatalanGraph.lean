module

public import Erdos993Lean.Analytic.V213.SmallForestCatalan
public import Erdos993Lean.Analytic.V213.SmallForestAffineIdentity

/-!
The graph consequence in current Lemma 7.4, equation (7.10).
This consumes the newly proved scalar Catalan floor and current signed-index
decomposition. No finite rank table or Catalan checker of version 2.10 of the manuscript is used.

The lower bound actually needs only independence of A. The final wrapper retains
the paper's maximum-cardinality context. At h=k the contribution is 1; at h>k
it is zero. These statements use integer indices, never truncated k-h.

-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.SmallForest

open Finset
open SmallForestCatalan

theorem G_one_nat (m j : ℕ) (hj : 1 ≤ j) :
    G 1 (j : ℤ) m = (Nat.choose m j : ℝ) - (Nat.choose m (j - 1) : ℝ) := by
  have he : (j : ℤ) - 1 = ((j - 1 : ℕ) : ℤ) := by omega
  simp only [G, one_mul, sub_self, zero_mul, sub_zero, he, binom_nat]

theorem G_one_zero (m : ℕ) : G 1 0 m = 1 := by
  norm_num [G, binom]

theorem G_one_negative (m : ℕ) {j : ℤ} (hj : j < 0) : G 1 j m = 0 := by
  have h0 : ¬0 ≤ j := by omega
  have h1 : ¬0 ≤ j - 1 := by omega
  simp only [G, one_mul, sub_self, zero_mul, sub_zero, binom, if_neg h0, if_neg h1]

theorem G_one_nonneg_of_nonpos (m : ℕ) {j : ℤ} (hj : j ≤ 0) : 0 ≤ G 1 j m := by
  rcases lt_or_eq_of_le hj with h | h
  · rw [G_one_negative m h]
  · rw [h, G_one_zero]
    norm_num

theorem G_one_floor (m k h : ℕ) (hh : h < k) :
    -realCatalan (k - h - 1) ≤ G 1 ((k : ℤ) - h) m := by
  have he : (k : ℤ) - h = ((k - h : ℕ) : ℤ) := by omega
  rw [he, G_one_nat m (k - h) (by omega)]
  exact catalan_floor_real (k - h) m (by omega)

variable (F : FiniteForest) [DecidableRel F.graph.Adj]

/-- Basic count bound; no maximum-set or acyclicity premise is needed here. -/
theorem catalan_N_le_choose (A : Finset (Fin F.n)) (h : ℕ) :
    N F A h ≤ (Aᶜ).card.choose h := by
  rw [N_eq_card_independent_subsets]
  unfold Zhang.Rows.indepSets
  calc
    _ ≤ ((Aᶜ).powersetCard h).card := Finset.card_filter_le _ _
    _ = (Aᶜ).card.choose h := Finset.card_powersetCard h Aᶜ

theorem catalan_row_floor (A : Finset (Fin F.n)) (k h : ℕ) (hh : h < k) :
    -((Nat.choose (Aᶜ).card h : ℝ) * realCatalan (k - h - 1)) ≤ row F A k 1 h := by
  have hc : (0 : ℝ) ≤ realCatalan (k - h - 1) := by
    unfold realCatalan
    exact_mod_cast cat_nonneg (k - h - 1)
  have hn : (N F A h : ℝ) = ((Fiber.indepSubsets F.graph Aᶜ h).card : ℝ) := by
    rw [N_eq_card_independent_subsets]
    rfl
  have hs :
      (∑ J ∈ Fiber.indepSubsets F.graph Aᶜ h, -realCatalan (k - h - 1)) ≤ row F A k 1 h := by
    unfold row
    apply sum_le_sum
    intro J _
    exact G_one_floor _ k h hh
  simp only [sum_const, nsmul_eq_mul] at hs
  rw [← hn] at hs
  have hN : (N F A h : ℝ) ≤ (Nat.choose (Aᶜ).card h : ℝ) := by
    exact_mod_cast catalan_N_le_choose F A h
  calc
    -((Nat.choose (Aᶜ).card h : ℝ) * realCatalan (k - h - 1)) ≤
        -((N F A h : ℝ) * realCatalan (k - h - 1)) :=
      neg_le_neg (mul_le_mul_of_nonneg_right hN hc)
    _ = (N F A h : ℝ) * (-realCatalan (k - h - 1)) := by ring
    _ ≤ row F A k 1 h := hs

theorem catalan_row_nonneg (A : Finset (Fin F.n)) (k h : ℕ) (hh : k ≤ h) :
    0 ≤ row F A k 1 h := by
  unfold row
  apply sum_nonneg
  intro J _
  exact G_one_nonneg_of_nonpos _ (by omega)

/-- The printed Catalan lower bound, before unnecessary maximum-set restrictions. -/
theorem catalan_rising_bound (A : Finset (Fin F.n))
    (hA : F.graph.IsIndepSet (A : Set (Fin F.n))) {k : ℕ} (hk : 1 ≤ k) :
    realRising A.card (Aᶜ).card k ≤
      (indepCount F.graph univ k : ℝ) - (indepCount F.graph univ (k - 1) : ℝ) := by
  have hsubset : Icc 1 (k - 1) ⊆ Icc 1 (k + 1) := by
    intro h hh
    simp only [mem_Icc] at hh ⊢
    omega
  have hs : (∑ h ∈ Icc 1 (k - 1), row F A k 1 h) ≤
      ∑ h ∈ Icc 1 (k + 1), row F A k 1 h := by
    apply sum_le_sum_of_subset_of_nonneg hsubset
    intro h hh hn
    have hkh : k ≤ h := by
      simp only [mem_Icc] at hh hn
      omega
    exact catalan_row_nonneg F A k h hkh
  have hf :
      (∑ h ∈ Icc 1 (k - 1), -((Nat.choose (Aᶜ).card h : ℝ) * realCatalan (k - h - 1))) ≤
        ∑ h ∈ Icc 1 (k - 1), row F A k 1 h := by
    apply sum_le_sum
    intro h hh
    exact catalan_row_floor F A k h (by have := (mem_Icc.mp hh).2; omega)
  have hR : realRising A.card (Aᶜ).card k = G 1 (k : ℤ) A.card +
      ∑ h ∈ Icc 1 (k - 1), -((Nat.choose (Aᶜ).card h : ℝ) * realCatalan (k - h - 1)) := by
    rw [G_one_nat A.card k hk]
    simp only [realRising, rising, Rat.cast_sub, Rat.cast_sum, Rat.cast_mul,
      Rat.cast_natCast, realCatalan, sum_neg_distrib]
    ring
  have hV : realRising A.card (Aᶜ).card k ≤ variation F k 1 := by
    rw [hR, variation_eq_empty_add_rows F A hA hk 1]
    exact add_le_add (le_refl _) (hf.trans hs)
  simpa only [variation, one_mul, sub_self, zero_mul, add_zero] using hV

/-- Lemma 7.4's literal forest context and displayed truncated sum. -/
theorem catalan_forest_consequence (A : Finset (Fin F.n))
    (hA : F.graph.IsIndepSet (A : Set (Fin F.n)))
    (_hmax : ∀ S : Finset (Fin F.n), F.graph.IsIndepSet (S : Set (Fin F.n)) → S.card ≤ A.card)
    {k : ℕ} (hk : 1 ≤ k) :
    (Nat.choose A.card k : ℝ) - (Nat.choose A.card (k - 1) : ℝ) -
      (∑ h ∈ Icc 1 (min (Aᶜ).card (k - 1)),
        (Nat.choose (Aᶜ).card h : ℝ) * realCatalan (k - h - 1)) ≤
      (indepCount F.graph univ k : ℝ) - (indepCount F.graph univ (k - 1) : ℝ) := by
  rw [← realRising_eq_printed]
  exact catalan_rising_bound F A hA hk

end Erdos993Lean.Analytic.V213.SmallForest

#check Erdos993Lean.Analytic.V213.SmallForest.G_one_nat
#print axioms Erdos993Lean.Analytic.V213.SmallForest.G_one_nat
#check Erdos993Lean.Analytic.V213.SmallForest.G_one_zero
#print axioms Erdos993Lean.Analytic.V213.SmallForest.G_one_zero
#check Erdos993Lean.Analytic.V213.SmallForest.G_one_negative
#print axioms Erdos993Lean.Analytic.V213.SmallForest.G_one_negative
#check Erdos993Lean.Analytic.V213.SmallForest.G_one_nonneg_of_nonpos
#print axioms Erdos993Lean.Analytic.V213.SmallForest.G_one_nonneg_of_nonpos
#check Erdos993Lean.Analytic.V213.SmallForest.G_one_floor
#print axioms Erdos993Lean.Analytic.V213.SmallForest.G_one_floor
#check Erdos993Lean.Analytic.V213.SmallForest.catalan_N_le_choose
#print axioms Erdos993Lean.Analytic.V213.SmallForest.catalan_N_le_choose
#check Erdos993Lean.Analytic.V213.SmallForest.catalan_row_floor
#print axioms Erdos993Lean.Analytic.V213.SmallForest.catalan_row_floor
#check Erdos993Lean.Analytic.V213.SmallForest.catalan_row_nonneg
#print axioms Erdos993Lean.Analytic.V213.SmallForest.catalan_row_nonneg
#check Erdos993Lean.Analytic.V213.SmallForest.catalan_rising_bound
#print axioms Erdos993Lean.Analytic.V213.SmallForest.catalan_rising_bound
#check Erdos993Lean.Analytic.V213.SmallForest.catalan_forest_consequence
#print axioms Erdos993Lean.Analytic.V213.SmallForest.catalan_forest_consequence
