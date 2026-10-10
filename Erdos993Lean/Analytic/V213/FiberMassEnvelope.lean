module

public import Erdos993Lean.Analytic.V213.FiberWidthRatios

/-!
Semantic envelope for the exact mass error E_W.
The actual square-root windows and radial variance remain in E_W; upper
window bounds are propagated into its positive denominators by ordinary
real inequalities. Concrete Eq74 consumers discharge every window premise.
No generated finite family is consumed here.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real

theorem fiber_mass_error_coarse {N r W L U : ℝ}
    (hN : 0 < N) (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hW : 0 ≤ W)
    (hL0 : 0 ≤ L) (hL1 : L < 1) (hU0 : 0 ≤ U) (hU1 : U < 1)
    (hL : fiberWindowLeft N r W ≤ L)
    (hU : r + fiberWindowRight N r W ≤ U) :
    fiberMassError N r W ≤
      max (fiberWidthPower (Real.sqrt W) 1 N / (9 * (1 - L ^ 2)))
        (fiberWidthPower (Real.sqrt W) 0 N / (9 * (1 - U ^ 2))) := by
  have hm : 0 < N + 1 := by linarith
  have ha : (3 / 4 : ℝ) ≤ 1 - r ^ 2 := by nlinarith
  have ha0 : 0 < 1 - r ^ 2 := by linarith
  have he := fiber_window_envelopes hN hr0 hrh hW
  have hLden : 0 < 1 - L ^ 2 := by nlinarith
  have hUden : 0 < 1 - U ^ 2 := by nlinarith
  have hLD : 1 - L ^ 2 ≤ 1 - (fiberWindowLeft N r W) ^ 2 := by
    nlinarith [he.2.2.1]
  have hUD : 1 - U ^ 2 ≤ 1 - (r + fiberWindowRight N r W) ^ 2 := by
    have ht : 0 ≤ r + fiberWindowRight N r W := add_nonneg hr0 he.1
    nlinarith
  have hActualL : 0 < 1 - (fiberWindowLeft N r W) ^ 2 := hLden.trans_le hLD
  have hActualU : 0 < 1 - (r + fiberWindowRight N r W) ^ 2 := hUden.trans_le hUD
  have hDenL : 9 * (1 - L ^ 2) ≤
      12 * (1 - r ^ 2) * (1 - (fiberWindowLeft N r W) ^ 2) := by
    calc
      _ ≤ 12 * (1 - r ^ 2) * (1 - L ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith) hLden.le
      _ ≤ _ := mul_le_mul_of_nonneg_left hLD (by positivity)
  have hDenU : 9 * (1 - U ^ 2) ≤
      12 * (1 - r ^ 2) * (1 - (r + fiberWindowRight N r W) ^ 2) := by
    calc
      _ ≤ 12 * (1 - r ^ 2) * (1 - U ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith) hUden.le
      _ ≤ _ := mul_le_mul_of_nonneg_left hUD (by positivity)
  have hNumL : (N + 1) * (fiberWindowLeft N r W) ^ 4 ≤
      fiberWidthPower (Real.sqrt W) 1 N := by
    have ht := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ he.2.2.1 he.2.2.2 4) hm.le
    have hid : (N + 1) * (fiberWidthRatio (Real.sqrt W) 1 N) ^ 4 =
        fiberWidthPower (Real.sqrt W) 1 N := by
      unfold fiberWidthRatio fiberWidthPower
      field_simp [hm.ne']
    rwa [hid] at ht
  have hNumR : (N + 1) * (fiberWindowRight N r W) ^ 4 ≤
      fiberWidthPower (Real.sqrt W) 0 N := by
    have ht := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ he.1 he.2.1 4) hm.le
    have hid : (N + 1) * (fiberWidthRatio (Real.sqrt W) 0 N) ^ 4 =
        fiberWidthPower (Real.sqrt W) 0 N := by
      unfold fiberWidthRatio fiberWidthPower
      field_simp [hm.ne']
    rwa [hid] at ht
  have hLeft : (N + 1) / (12 * (1 - r ^ 2)) *
      ((fiberWindowLeft N r W) ^ 4 / (1 - (fiberWindowLeft N r W) ^ 2)) ≤
      fiberWidthPower (Real.sqrt W) 1 N / (9 * (1 - L ^ 2)) := by
    calc
      _ = (N + 1) * (fiberWindowLeft N r W) ^ 4 /
          (12 * (1 - r ^ 2) * (1 - (fiberWindowLeft N r W) ^ 2)) := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ ≤ fiberWidthPower (Real.sqrt W) 1 N /
          (12 * (1 - r ^ 2) * (1 - (fiberWindowLeft N r W) ^ 2)) :=
        div_le_div_of_nonneg_right hNumL (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (by unfold fiberWidthPower; positivity)
        (by positivity) hDenL
  have hRight : (N + 1) / (12 * (1 - r ^ 2)) *
      ((fiberWindowRight N r W) ^ 4 / (1 - (r + fiberWindowRight N r W) ^ 2)) ≤
      fiberWidthPower (Real.sqrt W) 0 N / (9 * (1 - U ^ 2)) := by
    calc
      _ = (N + 1) * (fiberWindowRight N r W) ^ 4 /
          (12 * (1 - r ^ 2) * (1 - (r + fiberWindowRight N r W) ^ 2)) := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ ≤ fiberWidthPower (Real.sqrt W) 0 N /
          (12 * (1 - r ^ 2) * (1 - (r + fiberWindowRight N r W) ^ 2)) :=
        div_le_div_of_nonneg_right hNumR (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (by unfold fiberWidthPower; positivity)
        (by positivity) hDenU
  unfold fiberMassError
  rw [mul_max_of_nonneg _ _ (by positivity)]
  exact max_le_max hLeft hRight

end Erdos993Lean.Analytic.V213
