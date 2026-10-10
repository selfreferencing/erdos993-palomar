module

public import Erdos993Lean.Analytic.V213.FiberMassExponent

/-!
Literal conditional Eq73 on a general real W>=1, actual supported
integer J and actual central binomial amplitude c_N. Every denominator and
absorption hypothesis is the printed one. Definitions of w, xi and the
radial coordinate are explicit; no generated finite family is consumed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real
open Erdos993Lean.Analytic.V22.Analysis

noncomputable def fiberRadialOffset (r N : ℝ) (J : ℤ) : ℝ :=
  (J : ℝ) - N / 2 - r * (N - 1) / 2

noncomputable def fiberRadialX (r N : ℝ) (J : ℤ) : ℝ :=
  fiberRadialOffset r N J / Erdos993Lean.Analytic.V22.sN r N

noncomputable def fiberRadialSquare (r N : ℝ) (J : ℤ) : ℝ :=
  fiberRadialOffset r N J ^ 2 / (Erdos993Lean.Analytic.V22.varianceR r * N)

theorem fiber_radial_square_identity {r N : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hN : 0 < N) (J : ℤ) : fiberRadialX r N J ^ 2 = fiberRadialSquare r N J := by
  unfold fiberRadialX fiberRadialSquare
  rw [div_pow, shared_sN_sq hr0 hr1 hN]

theorem fiber_radial_coordinate (r : ℝ) (N : ℕ) (J : ℤ) :
    interiorTiltCoordinate r N J = sharedGaussianZ r N (fiberRadialOffset r N J) := by
  unfold interiorTiltCoordinate interiorSymmetricCoordinate sharedGaussianZ fiberRadialOffset
  have hm : (N : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hm] <;> ring

theorem fiber_mass_linear_correction {r N : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hN : 0 < N) (x : ℝ) :
    Erdos993Lean.Analytic.V22.epsilon r N * |x| + Erdos993Lean.Analytic.V22.c0 r N =
      (2 * (r / Real.sqrt (1 - r ^ 2)) * Real.sqrt (N * x ^ 2) +
        2 * (r / Real.sqrt (1 - r ^ 2)) ^ 2) / (N + 1) := by
  have ha := shared_one_sub_sq_pos (by linarith : -1 < r) hr1
  have hs0 : 0 < Real.sqrt (1 - r ^ 2) := Real.sqrt_pos.2 ha
  have hsq := Real.sq_sqrt ha.le
  have hm : 0 < N + 1 := by positivity
  have hprod : Real.sqrt (N * x ^ 2) = Real.sqrt N * |x| := by
    rw [Real.sqrt_mul hN.le, Real.sqrt_sq_eq_abs]
  have hvroot : Real.sqrt (Erdos993Lean.Analytic.V22.varianceR r) =
      Real.sqrt (1 - r ^ 2) / 2 := by
    unfold Erdos993Lean.Analytic.V22.varianceR
    rw [Real.sqrt_div ha.le]
    norm_num
  rw [hprod]
  unfold Erdos993Lean.Analytic.V22.epsilon Erdos993Lean.Analytic.V22.c0
  rw [hvroot]
  unfold Erdos993Lean.Analytic.V22.varianceR
  generalize haeq : 1 - r ^ 2 = a at *
  generalize hseq : Real.sqrt a = s at *
  rw [← hsq]
  field_simp [hs0.ne', hm.ne'] <;> ring

theorem fiber_binomial_mass_lower_general {N : ℕ} (hN : 2 ≤ N)
    {r W : ℝ} (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hW : 1 ≤ W)
    (J : ℤ) (hJ0 : 0 ≤ J) (hJN : J ≤ (N : ℤ))
    (hLeft : 0 < 1 - (fiberWindowLeft N r W) ^ 2)
    (hRight : 0 < 1 - (r + fiberWindowRight N r W) ^ 2)
    (hAbs : W ≤ 12 * (1 - (r + fiberWindowRight N r W) ^ 2) /
      ((1 - r ^ 2) * Erdos993Lean.Analytic.V22.rho N))
    (hw : fiberRadialSquare r N J ≤ W) :
    Real.exp (-(Erdos993Lean.Analytic.V22.rho N) * fiberRadialSquare r N J / 2 -
      (2 * (r / Real.sqrt (1 - r ^ 2)) * Real.sqrt ((N : ℝ) * fiberRadialSquare r N J) +
        2 * (r / Real.sqrt (1 - r ^ 2)) ^ 2) / ((N : ℝ) + 1) - fiberMassError N r W) ≤
      Real.sqrt (1 - r ^ 2) * binom N ((1 + r) / 2) J / fiberCentralPrefactor N := by
  have hr1 : r < 1 := by linarith
  have hNr : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hW0 : 0 ≤ W := by linarith
  have hm : 0 < (N : ℝ) + 1 := by positivity
  have ha := shared_one_sub_sq_pos (by linarith : -1 < r) hr1
  have hv := shared_varianceR_pos hr0 hr1
  have hs : 0 < Erdos993Lean.Analytic.V22.sN r N := by
    unfold Erdos993Lean.Analytic.V22.sN
    positivity
  have hroot := Real.sqrt_pos.2 ha
  have hC := fiber_central_prefactor_pos N
  have hZL := fiber_window_left_identity hNr hr0 hr1 hW0
  have hZR := fiber_window_right_identity hNr hr0 hr1 hW0
  have hDL : 0 < 1 - (Erdos993Lean.Analytic.V22.ZL r N W) ^ 2 := by rw [hZL]; exact hLeft
  have hDR : 0 < 1 - (r + Erdos993Lean.Analytic.V22.ZR r N W) ^ 2 := by rw [hZR]; exact hRight
  have hrho : 0 < Erdos993Lean.Analytic.V22.rho N := by
    unfold Erdos993Lean.Analytic.V22.rho
    positivity
  have hcondition := (le_div_iff₀ (mul_pos ha hrho)).mp hAbs
  have hcondition' : W * (1 - r ^ 2) * (N : ℝ) / ((N : ℝ) + 1) ≤
      12 * (1 - (r + fiberWindowRight N r W) ^ 2) := by
    convert hcondition using 1 <;> unfold Erdos993Lean.Analytic.V22.rho <;> ring
  have hcondition'' := (div_le_iff₀ hm).mp hcondition'
  have hA : W * (1 - r ^ 2) * (N : ℝ) ≤
      12 * ((N : ℝ) + 1) * (1 - (r + Erdos993Lean.Analytic.V22.ZR r N W) ^ 2) := by
    rw [hZR]
    convert hcondition'' using 1 <;> ring
  have hxw : fiberRadialX r N J ^ 2 ≤ W := by
    rw [fiber_radial_square_identity hr0 hr1 hNr]
    exact hw
  have hPsi := fiber_mass_exponent_upper hr0 hr1 hNr hW hDL hDR hA (fiberRadialX r N J) hxw
  have hu : Erdos993Lean.Analytic.V22.sN r N * fiberRadialX r N J = fiberRadialOffset r N J := by
    unfold fiberRadialX
    field_simp [hs.ne']
  rw [hu, ← fiber_radial_coordinate] at hPsi
  have hlocal := fiber_binomial_local_lower hN hr0 hr1 J hJ0 hJN
  have hscaled := mul_le_mul_of_nonneg_left hlocal (by positivity : 0 ≤ Real.sqrt (1 - r ^ 2) / fiberCentralPrefactor N)
  have hscaled' : Real.exp (-((N : ℝ) + 1) * sharedKLPsi r (interiorTiltCoordinate r N J)) ≤
      Real.sqrt (1 - r ^ 2) * binom N ((1 + r) / 2) J / fiberCentralPrefactor N := by
    convert hscaled using 1 <;> field_simp [hC.ne', hroot.ne'] <;> ring
  have he : Real.exp (-(Erdos993Lean.Analytic.V22.rho N) / 2 * fiberRadialX r N J ^ 2 -
      Erdos993Lean.Analytic.V22.epsilon r N * |fiberRadialX r N J| -
      Erdos993Lean.Analytic.V22.c0 r N - Erdos993Lean.Analytic.V22.quarticError r N W) ≤
      Real.sqrt (1 - r ^ 2) * binom N ((1 + r) / 2) J / fiberCentralPrefactor N :=
    (Real.exp_le_exp.mpr (by linarith [hPsi])).trans hscaled'
  have hc := fiber_mass_linear_correction hr0 hr1 hNr (fiberRadialX r N J)
  rw [fiber_radial_square_identity hr0 hr1 hNr] at hc
  rw [fiber_mass_error_identity hNr hr0 hr1 hW0] at he
  have hlin : -(Erdos993Lean.Analytic.V22.rho N) / 2 * fiberRadialX r N J ^ 2 -
      Erdos993Lean.Analytic.V22.epsilon r N * |fiberRadialX r N J| -
      Erdos993Lean.Analytic.V22.c0 r N - fiberMassError N r W =
      -(Erdos993Lean.Analytic.V22.rho N) * fiberRadialSquare r N J / 2 -
      (2 * (r / Real.sqrt (1 - r ^ 2)) * Real.sqrt ((N : ℝ) * fiberRadialSquare r N J) +
        2 * (r / Real.sqrt (1 - r ^ 2)) ^ 2) / ((N : ℝ) + 1) - fiberMassError N r W := by
    rw [fiber_radial_square_identity hr0 hr1 hNr]
    linarith [hc]
  rwa [hlin] at he

end Erdos993Lean.Analytic.V213
