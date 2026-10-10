module

public import Erdos993Lean.Analytic.V213.SmallForestFiniteFormula

/-!
The exact rational cut operands are interpreted
as the printed real affine lines. No finite assertion occurs in this proof;
all choices of cuts select one of the three proved universal Catalan lines.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.SmallForest

open Finset SmallForestFinite SmallForestCatalan

theorem catalan_cut_slope_nonneg (k s t h : ℕ) :
    (0 : ℝ) ≤ ((catalanLineQ k s t h).2 : ℝ) := by
  unfold catalanLineQ
  split_ifs <;> dsimp only
  all_goals first
    | (rw [catQ_cast]; unfold realCatalan; exact_mod_cast cat_nonneg _)
    | norm_num

/-- The actual line hypothesis of (109) for the displayed Catalan cuts. -/
theorem catalan_cut_line (k s t h m : ℕ) :
    ((catalanLineQ k s t h).1 : ℝ) +
      ((catalanLineQ k s t h).2 : ℝ) * (m : ℝ) ≤
        G 1 ((k : ℤ) - h) m := by
  by_cases hh : h < k
  · have hj : 1 ≤ k - h := by omega
    have hi : (k : ℤ) - h = ((k - h : ℕ) : ℤ) := by omega
    rw [hi, G_one_nat m (k - h) hj]
    by_cases hs : h ≤ s
    · simp only [catalanLineQ, if_pos hh, if_pos hs, Rat.cast_mul,
        Rat.cast_sub, Rat.cast_one, Rat.cast_ofNat, Rat.cast_natCast, catQ_cast]
      have hb := catalan_rising_upper_real (k - h) m hj
      nlinarith only [hb]
    · by_cases ht : h ≤ t
      · simp only [catalanLineQ, if_pos hh, if_neg hs, if_pos ht, Rat.cast_mul,
          Rat.cast_sub, Rat.cast_one, Rat.cast_ofNat, Rat.cast_natCast, catQ_cast]
        have hb := catalan_rising_lower_real (k - h) m hj
        nlinarith only [hb]
      · simp only [catalanLineQ, if_pos hh, if_neg hs, if_neg ht,
          Rat.cast_neg, Rat.cast_zero, zero_mul, add_zero, catQ_cast]
        exact catalan_floor_real (k - h) m hj
  · simp only [catalanLineQ, if_neg hh, Rat.cast_zero, zero_mul, zero_add]
    exact G_one_nonneg_of_nonpos m (by omega)

/-- Exact affine summation with these lines, before any finite evaluation. -/
theorem catalan_cut_forest_bound (F : FiniteForest) [DecidableRel F.graph.Adj]
    (A : Finset (Fin F.n)) (hA : F.graph.IsIndepSet (A : Set (Fin F.n)))
    (hmax : ∀ S : Finset (Fin F.n), F.graph.IsIndepSet (S : Set (Fin F.n)) →
      S.card ≤ A.card) (hc : 2 ≤ (Aᶜ).card) (k s t : ℕ) (hk : 1 ≤ k) :
    (catalanAQ A.card (Aᶜ).card k s t : ℝ) +
      (catalanBQ A.card (Aᶜ).card k s t : ℝ) * (internalEdges F A : ℝ) ≤
        variation F k 1 := by
  unfold catalanAQ catalanBQ
  rw [affineAQ_cast, affineBQ_cast]
  simp only [Rat.cast_one]
  exact affine_summation F A hA hmax hc hk 1 (by norm_num)
    (fun h => ((catalanLineQ k s t h).1 : ℝ))
    (fun h => ((catalanLineQ k s t h).2 : ℝ))
    (fun h _ => catalan_cut_slope_nonneg k s t h)
    (fun h _ m _ => catalan_cut_line k s t h m)

end Erdos993Lean.Analytic.V213.SmallForest

#check Erdos993Lean.Analytic.V213.SmallForest.catalan_cut_slope_nonneg
#print axioms Erdos993Lean.Analytic.V213.SmallForest.catalan_cut_slope_nonneg
#check Erdos993Lean.Analytic.V213.SmallForest.catalan_cut_line
#print axioms Erdos993Lean.Analytic.V213.SmallForest.catalan_cut_line
#check Erdos993Lean.Analytic.V213.SmallForest.catalan_cut_forest_bound
#print axioms Erdos993Lean.Analytic.V213.SmallForest.catalan_cut_forest_bound
