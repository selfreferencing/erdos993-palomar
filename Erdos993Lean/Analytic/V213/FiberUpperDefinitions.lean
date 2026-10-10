module

public import Erdos993Lean.Analytic.V213.FiberAmplitudes
public import Erdos993Lean.Analytic.V213.FiberCoefficientBounds

/-!
Exact upper quantities in Eq77 and their actual-fiber amplitude shift.
The positive upper template is the printed U_N, not a fitted amplitude.
All normalization identities use its actual source definition.
No finite DF10 family is consumed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Erdos993Lean.Analytic.V22.Analysis

noncomputable def fiberUpperP (mu r : ℝ) (N : ℕ) : ℝ :=
  shapeTemplatePrefactor mu N (fiberUpperPrefactor N) *
    Real.exp (((N : ℝ) + 1) * V22.cr r - V22.c0Prime r N +
      V22.epsilonPrime r N * Real.sqrt (V22.gamma r N) / 2)

noncomputable def fiberUpperOmega (mu r : ℝ) (N : ℕ) : ℝ :=
  Real.log (((N : ℝ) / mu) * Real.exp (V22.rhoU r N * V22.gamma r N / 2) /
    fiberUpperP mu r N)

theorem fiber_upper_P_pos {mu r : ℝ} {N : ℕ} (hmu : 0 < mu) (hN : 2 ≤ N) :
    0 < fiberUpperP mu r N := by
  unfold fiberUpperP
  exact mul_pos (shapeTemplatePrefactor_pos hmu
    (by exact_mod_cast (by omega : 1 < N)) (symmetricUpperPrefactor_pos N))
    (Real.exp_pos _)

theorem fiber_upper_omega_identity {mu r : ℝ} {N : ℕ}
    (hmu : 0 < mu) (hN : 2 ≤ N) :
    fiberUpperOmega mu r N = fiberTemplateOmega mu N (fiberUpperPrefactor N) +
      V22.rhoU r N * V22.Delta r N / 2 - V22.eU r N := by
  have hn : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hb : 0 < (N : ℝ) / mu := div_pos (by linarith) hmu
  have hp : 0 < shapeTemplatePrefactor mu N (fiberUpperPrefactor N) :=
    shapeTemplatePrefactor_pos hmu hn (symmetricUpperPrefactor_pos N)
  unfold fiberUpperOmega fiberUpperP fiberTemplateOmega shapeTemplateLambda
  simp (disch := positivity) only [Real.log_div, Real.log_mul, Real.log_exp]
  simp only [V22.gamma, V22.rhoU, V22.eU, V22.rho, div_eq_mul_inv, mul_inv_rev]
  ring

theorem fiber_upper_omega_gain_identity {mu r : ℝ} {N : ℕ}
    (hmu : 0 < mu) (hN : 2 ≤ N) :
    fiberUpperOmega mu r N = fiberTemplateOmega mu N (fiberUpperPrefactor N) +
      V22.phiR r N - 71 / (20 * ((N : ℝ) + 1)) := by
  rw [fiber_upper_omega_identity hmu hN]
  unfold V22.phiR
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem fiber_actual_upper_omega_gain {mu r : ℝ} {M : ℕ}
    (hmu : 0 < mu) (hM : 8 ≤ M) :
    5 / 2 * Real.log ((M : ℝ) / mu) + V22.phiR r ((M : ℝ) + 2) ≤
      fiberUpperOmega mu r (M + 2) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hm : 0 < (M : ℝ) + 3 := by positivity
  have hk := (fiber_upper_shift_bounds hM).1
  have hs := fiber_template_omega_shift (X := fiberUpperPrefactor (M + 2)) hmu (by omega : 0 < M)
    (symmetricUpperPrefactor_pos (M + 2))
  rw [fiber_upper_omega_gain_identity hmu (by omega), hs]
  simp only [Nat.cast_add, Nat.cast_ofNat]
  have hc : (71 / 20 : ℝ) / ((M : ℝ) + 3) ≤
      logShiftKValue (M : ℝ) (Real.log (fiberAmplitude (M + 2)
        (fiberUpperPrefactor (M + 2)))) / ((M : ℝ) + 3) :=
    div_le_div_of_nonneg_right hk hm.le
  have he : (71 / 20 : ℝ) / ((M : ℝ) + 3) = 71 / (20 * ((M : ℝ) + 2 + 1)) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [he] at hc
  linarith

end Erdos993Lean.Analytic.V213
