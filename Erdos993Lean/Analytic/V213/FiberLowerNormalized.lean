module

public import Erdos993Lean.Analytic.V213.FiberMassLower

/-!
General conditional Eq75, using the actual F/B, actual c_N, actual
upper bound for its template shift, and the exact Eq73 mass lower estimate.
The source support, denominator, absorption and W<=gamma conditions remain
explicit; no additional numerical premise or finite family is introduced.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real
open Erdos993Lean.Analytic.V22.Analysis

theorem fiber_template_ratio {N : ℕ} (hN : 2 ≤ N) {mu X : ℝ}
    (hmu : 0 < mu) (hX : 0 < X) :
    shapeTemplatePrefactor mu N X / ((N : ℝ) / mu) =
      Real.exp ((Erdos993Lean.Analytic.V22.rho N) / 2 - fiberTemplateOmega mu N X) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hB : 0 < (N : ℝ) / mu := by positivity
  have hP := shapeTemplatePrefactor_pos hmu hNr hX
  have ht : 0 < ((N : ℝ) / mu) * Real.exp ((Erdos993Lean.Analytic.V22.rho N) / 2) /
      shapeTemplatePrefactor mu N X := by positivity
  unfold fiberTemplateOmega shapeTemplateLambda Erdos993Lean.Analytic.V22.rho
  unfold Erdos993Lean.Analytic.V22.rho at ht
  rw [Real.exp_sub, Real.exp_log ht]
  field_simp [hB.ne', hP.ne', (Real.exp_pos _).ne']

theorem fiber_central_template_ratio_lower {M : ℕ} (hM : 8 ≤ M)
    {mu : ℝ} (hmu : 0 < mu) :
    ((M : ℝ) / mu) ^ (-(5 / 2 : ℝ)) *
      Real.exp ((Erdos993Lean.Analytic.V22.rho ((M : ℝ) + 2)) / 2 -
        ((77 / 20 : ℝ) + 10 / (M : ℝ)) / ((M : ℝ) + 3)) ≤
    shapeTemplatePrefactor mu (M + 2) (fiberCentralPrefactor (M + 2)) /
      (((M : ℝ) + 2) / mu) := by
  have hM0 : 0 < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have ht : 0 < (M : ℝ) / mu := by positivity
  have hshift := (fiber_central_shift_bounds hmu hM).2
  have he := Real.exp_le_exp.mpr (show
      (Erdos993Lean.Analytic.V22.rho ((M : ℝ) + 2)) / 2 -
        ((77 / 20 : ℝ) + 10 / (M : ℝ)) / ((M : ℝ) + 3) -
        (5 / 2 : ℝ) * Real.log ((M : ℝ) / mu) ≤
      (Erdos993Lean.Analytic.V22.rho ((M : ℝ) + 2)) / 2 -
        fiberTemplateOmega mu (M + 2) (fiberCentralPrefactor (M + 2)) by linarith)
  have hratio := fiber_template_ratio (N := M + 2) (by omega) hmu (fiber_central_prefactor_pos (M + 2))
  push_cast at hratio
  rw [← hratio] at he
  rw [Real.rpow_def_of_pos ht, ← Real.exp_add]
  convert he using 1 <;> congr 1 <;> ring

theorem fiber_radial_fiber_offset (q : ℝ) (M : ℕ) (j : ℤ) :
    fiberRadialOffset (fiberSkew q) (M + 2) (j + 1) = fiberOffset q M j := by
  unfold fiberRadialOffset fiberOffset fiberSkew
  push_cast
  ring

theorem fiber_radial_fiber_square (q : ℝ) (M : ℕ) (j : ℤ) :
    fiberRadialSquare (fiberSkew q) (M + 2) (j + 1) = fiberSquareOffset q M j := by
  have hv : Erdos993Lean.Analytic.V22.varianceR (fiberSkew q) = fiberVariance q := by
    unfold Erdos993Lean.Analytic.V22.varianceR
    rw [fiber_variance_skew]
    ring
  unfold fiberRadialSquare fiberSquareOffset
  rw [fiber_radial_fiber_offset, hv]

theorem fiber_bonus_current_formula {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (M : ℕ) :
    fiberBonus q M = 1 +
      (((M : ℝ) + 2) - 1 + 1 / ((M : ℝ) + 2)) *
        (fiberSkew q / Real.sqrt (1 - fiberSkew q ^ 2)) ^ 2 := by
  have ha : 0 < 1 - fiberSkew q ^ 2 := by
    rw [fiber_variance_skew]
    exact mul_pos (by norm_num) (fiber_variance_pos hq0 hq1)
  have hsq := Real.sq_sqrt ha.le
  have hN : (M : ℝ) + 2 ≠ 0 := by positivity
  unfold fiberBonus
  rw [div_pow, hsq]
  field_simp [ha.ne', hN] <;> ring

theorem fiber_F_template_ratio (M : ℕ) (j : ℤ) {q mu : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (hmu : 0 < mu) :
    fiberF q mu M j / (((M : ℝ) + 2) / mu) =
      fiberSquareOffset q M j +
      (shapeTemplatePrefactor mu (M + 2) (fiberCentralPrefactor (M + 2)) /
        (((M : ℝ) + 2) / mu)) *
      (Real.sqrt (1 - fiberSkew q ^ 2) * binom (M + 2) q (j + 1) /
        fiberCentralPrefactor (M + 2)) *
      (fiberBonus q M - fiberSquareOffset q M j) := by
  rw [fiber_F_normalized M j hq0 hq1 hmu]
  unfold shapeTemplatePrefactor
  rw [← fiber_AG_port_identity]
  push_cast
  have hN : (M : ℝ) + 2 ≠ 0 := by positivity
  have hm : (M : ℝ) + 1 ≠ 0 := by positivity
  have hC := fiber_central_prefactor_pos (M + 2)
  rw [show (M : ℝ) + 2 - 1 = (M : ℝ) + 1 by ring]
  field_simp [hN, hm, hC.ne', fiber_AG_pos.ne', hmu.ne']
  ring

theorem fiber_lower_normalized_general {M : ℕ} (hM : 8 ≤ M) {q mu W : ℝ}
    (hq0 : 1 / 2 ≤ q) (hqh : q ≤ 3 / 4) (hmu : 0 < mu) (hW : 1 ≤ W)
    (j : ℤ) (hJ0 : 0 ≤ j + 1) (hJN : j + 1 ≤ ((M + 2 : ℕ) : ℤ))
    (hLeft : 0 < 1 - (fiberWindowLeft ((M : ℝ) + 2) (fiberSkew q) W) ^ 2)
    (hRight : 0 < 1 - (fiberSkew q + fiberWindowRight ((M : ℝ) + 2) (fiberSkew q) W) ^ 2)
    (hAbs : W ≤ 12 * (1 - (fiberSkew q + fiberWindowRight ((M : ℝ) + 2) (fiberSkew q) W) ^ 2) /
      ((1 - fiberSkew q ^ 2) * Erdos993Lean.Analytic.V22.rho ((M : ℝ) + 2)))
    (hw : fiberSquareOffset q M j ≤ W) (hWg : W ≤ fiberBonus q M) :
    fiberF q mu M j / (((M : ℝ) + 2) / mu) ≥
      fiberSquareOffset q M j + ((M : ℝ) / mu) ^ (-(5 / 2 : ℝ)) *
      Real.exp (Erdos993Lean.Analytic.V22.rho ((M : ℝ) + 2) *
        (1 - fiberSquareOffset q M j) / 2 -
        ((77 / 20 : ℝ) + 10 / (M : ℝ)) / ((M : ℝ) + 3) -
        fiberMassError ((M : ℝ) + 2) (fiberSkew q) W) *
      (1 - fiberSquareOffset q M j +
        (((M : ℝ) + 2) - 1 + 1 / ((M : ℝ) + 2)) *
          (fiberSkew q / Real.sqrt (1 - fiberSkew q ^ 2)) ^ 2) *
      Real.exp (-(2 * (fiberSkew q / Real.sqrt (1 - fiberSkew q ^ 2)) *
        Real.sqrt (((M : ℝ) + 2) * fiberSquareOffset q M j) +
        2 * (fiberSkew q / Real.sqrt (1 - fiberSkew q ^ 2)) ^ 2) / ((M : ℝ) + 3)) := by
  have hq0' : 0 < q := by linarith
  have hq1 : q < 1 := by linarith
  have hr0 : 0 ≤ fiberSkew q := by unfold fiberSkew; linarith
  have hrh : fiberSkew q ≤ 1 / 2 := by unfold fiberSkew; linarith
  have hM0 : 0 < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hB : 0 < ((M : ℝ) + 2) / mu := by positivity
  have hP : 0 < shapeTemplatePrefactor mu ((M : ℝ) + 2) (fiberCentralPrefactor (M + 2)) :=
    shapeTemplatePrefactor_pos hmu (by linarith [Nat.cast_nonneg (α := ℝ) M])
      (fiber_central_prefactor_pos (M + 2))
  have hm := fiber_binomial_mass_lower_general (by omega : 2 ≤ M + 2) hr0 hrh hW
    (j + 1) hJ0 hJN (by simpa only [Nat.cast_add, Nat.cast_ofNat] using hLeft)
    (by simpa only [Nat.cast_add, Nat.cast_ofNat] using hRight)
    (by simpa only [Nat.cast_add, Nat.cast_ofNat] using hAbs)
    (by push_cast; rw [fiber_radial_fiber_square]; exact hw)
  push_cast at hm
  rw [fiber_radial_fiber_square] at hm
  have hprob : (1 + fiberSkew q) / 2 = q := by unfold fiberSkew; ring
  rw [hprob] at hm
  rw [show (M : ℝ) + 2 + 1 = (M : ℝ) + 3 by ring] at hm
  have hp := fiber_central_template_ratio_lower hM hmu
  have hg : 0 ≤ fiberBonus q M - fiberSquareOffset q M j := by linarith
  have hprod := mul_le_mul hp hm (Real.exp_nonneg _)
    (div_nonneg hP.le hB.le)
  have hscaled := mul_le_mul_of_nonneg_right hprod hg
  let A : ℝ := Erdos993Lean.Analytic.V22.rho ((M : ℝ) + 2) / 2 -
    ((77 / 20 : ℝ) + 10 / (M : ℝ)) / ((M : ℝ) + 3)
  let C : ℝ := (2 * (fiberSkew q / Real.sqrt (1 - fiberSkew q ^ 2)) *
    Real.sqrt (((M : ℝ) + 2) * fiberSquareOffset q M j) +
    2 * (fiberSkew q / Real.sqrt (1 - fiberSkew q ^ 2)) ^ 2) / ((M : ℝ) + 3)
  let E : ℝ := -Erdos993Lean.Analytic.V22.rho ((M : ℝ) + 2) *
    fiberSquareOffset q M j / 2 - C - fiberMassError ((M : ℝ) + 2) (fiberSkew q) W
  let D : ℝ := Erdos993Lean.Analytic.V22.rho ((M : ℝ) + 2) *
    (1 - fiberSquareOffset q M j) / 2 -
    ((77 / 20 : ℝ) + 10 / (M : ℝ)) / ((M : ℝ) + 3) -
    fiberMassError ((M : ℝ) + 2) (fiberSkew q) W
  have hexp : Real.exp A * Real.exp E = Real.exp D * Real.exp (-C) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp [A, E, D]
    ring
  have hgroup : ((M : ℝ) / mu) ^ (-(5 / 2 : ℝ)) * Real.exp A * Real.exp E *
      (fiberBonus q M - fiberSquareOffset q M j) =
    ((M : ℝ) / mu) ^ (-(5 / 2 : ℝ)) * Real.exp D *
      (fiberBonus q M - fiberSquareOffset q M j) * Real.exp (-C) := by
    rw [mul_assoc (((M : ℝ) / mu) ^ (-(5 / 2 : ℝ))) (Real.exp A) (Real.exp E), hexp]
    ring
  change ((M : ℝ) / mu) ^ (-(5 / 2 : ℝ)) * Real.exp A * Real.exp E *
      (fiberBonus q M - fiberSquareOffset q M j) ≤ _ at hscaled
  rw [hgroup] at hscaled
  rw [fiber_F_template_ratio M j hq0' hq1 hmu]
  have hh := add_le_add_left hscaled (fiberSquareOffset q M j)
  have hbonus := fiber_bonus_current_formula hq0' hq1 M
  rw [hbonus] at hh
  rw [hbonus]
  dsimp [D, C] at hh
  convert hh using 1 <;> ring

theorem fiber_mass_amgm {w W : ℝ} (hw : 0 ≤ w) (hW : 0 < W) :
    2 * Real.sqrt w ≤ (w + W) / Real.sqrt W := by
  have hs := Real.sqrt_pos.2 hW
  have hws := Real.sq_sqrt hw
  have hWs := Real.sq_sqrt hW.le
  apply (le_div_iff₀ hs).2
  nlinarith [sq_nonneg (Real.sqrt w - Real.sqrt W)]

end Erdos993Lean.Analytic.V213
