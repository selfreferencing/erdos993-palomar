module

public import Erdos993Lean.Analytic.V213.FiberAmplitudes
public import Erdos993Lean.Analytic.V213.FiberDefinitions
public import Erdos993Lean.Analytic.V22.Analysis.SharedRoot

/-!
Exact endpoint Taylor lower bound, Eq71--72.
The real base logarithm and both endpoint cases are retained. The shift is
bound to the actual U_N amplitude and its proved interval; no finite family
or extra paper statement is assumed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real
open Erdos993Lean.Analytic.V22 Erdos993Lean.Analytic.V22.Analysis

theorem fiber_concave_quadratic_endpoints {a b k A B C : ℝ}
    (hab : a ≤ b) (hak : a ≤ k) (hkb : k ≤ b) (hC : 0 ≤ C) :
    min (A + B * a - C * a ^ 2) (A + B * b - C * b ^ 2) ≤
      A + B * k - C * k ^ 2 := by
  by_cases he : a = b
  · have hk : k = a := by linarith
    subst b
    subst k
    simp
  · have hspan : 0 < b - a := sub_pos.mpr (lt_of_le_of_ne hab he)
    let L := min (A + B * a - C * a ^ 2) (A + B * b - C * b ^ 2)
    have hl := mul_le_mul_of_nonneg_left (min_le_left
      (A + B * a - C * a ^ 2) (A + B * b - C * b ^ 2)) (sub_nonneg.mpr hkb)
    have hr := mul_le_mul_of_nonneg_left (min_le_right
      (A + B * a - C * a ^ 2) (A + B * b - C * b ^ 2)) (sub_nonneg.mpr hak)
    have hid : (b - a) * (A + B * k - C * k ^ 2) -
        ((b - k) * (A + B * a - C * a ^ 2) +
          (k - a) * (A + B * b - C * b ^ 2)) =
        C * (b - a) * (k - a) * (b - k) := by ring
    have hp : 0 ≤ (b - a) * (A + B * k - C * k ^ 2) -
        ((b - k) * (A + B * a - C * a ^ 2) +
          (k - a) * (A + B * b - C * b ^ 2)) := by
      rw [hid]
      exact mul_nonneg (mul_nonneg (mul_nonneg hC hspan.le)
        (sub_nonneg.mpr hak)) (sub_nonneg.mpr hkb)
    apply le_of_mul_le_mul_left ?_ hspan
    nlinarith

noncomputable def fiberTaylorS (t : ℝ) : ℝ :=
  9 / 2 * (t - 1) ^ 2 / t - 2 * G (5 / 2 * Real.log t)

noncomputable def fiberTaylorEndpoint (t M k : ℝ) : ℝ :=
  M * fiberTaylorS t + 2 - 6 * G (5 / 2 * Real.log t) -
    2 * k * G1 (5 / 2 * Real.log t) -
      k ^ 2 * G2 (5 / 2 * Real.log t) / (M + 3)

noncomputable def fiberTaylorT (t M : ℝ) : ℝ :=
  min (fiberTaylorEndpoint t M (71 / 20))
    (fiberTaylorEndpoint t M (77 / 20 + 10 / M))

theorem fiber_upper_taylor_minorant {M : ℕ} (hM : 8 ≤ M) {mu : ℝ}
    (hmu : 0 < mu) :
    (M : ℝ) + 2 - mu * fiberPsi ((M : ℝ) / mu) -
      2 * ((M : ℝ) + 3) *
        G (fiberTemplateOmega mu (M + 2) (fiberUpperPrefactor (M + 2))) ≥
      fiberTaylorT ((M : ℝ) / mu) (M : ℝ) := by
  have hM0 : 0 < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hm : 0 < (M : ℝ) + 3 := by positivity
  have ht : 0 < (M : ℝ) / mu := div_pos hM0 hmu
  have hk := fiber_upper_shift_bounds hM
  change 71 / 20 ≤ fiberUpperK M ∧ fiberUpperK M ≤ 77 / 20 + 10 / (M : ℝ) at hk
  have hk0 : 0 ≤ fiberUpperK M := by linarith [hk.1]
  have hfrac0 : 0 ≤ 10 / (M : ℝ) := by positivity
  have hp : 0 < fiberUpperPrefactor (M + 2) := symmetricUpperPrefactor_pos _
  have hshift := fiber_template_omega_shift hmu (by omega : 0 < M) hp
  change fiberTemplateOmega mu (M + 2) (fiberUpperPrefactor (M + 2)) =
    5 / 2 * Real.log ((M : ℝ) / mu) + fiberUpperK M / ((M : ℝ) + 3) at hshift
  have hTaylor := shared_G_taylor_shift_upper (5 / 2 * Real.log ((M : ℝ) / mu))
    (fiberUpperK M / ((M : ℝ) + 3)) (by positivity)
  have hscaled := mul_le_mul_of_nonneg_left hTaylor (by positivity : 0 ≤ 2 * ((M : ℝ) + 3))
  have hbase : (M : ℝ) + 2 - mu * fiberPsi ((M : ℝ) / mu) =
      2 + (9 / 2 : ℝ) * (M : ℝ) * (((M : ℝ) / mu) - 1) ^ 2 / ((M : ℝ) / mu) := by
    unfold fiberPsi
    field_simp [hmu.ne', hM0.ne'] <;> ring
  have hpoly : (M : ℝ) + 2 - mu * fiberPsi ((M : ℝ) / mu) -
      2 * ((M : ℝ) + 3) *
        G (fiberTemplateOmega mu (M + 2) (fiberUpperPrefactor (M + 2))) ≥
      fiberTaylorEndpoint ((M : ℝ) / mu) (M : ℝ) (fiberUpperK M) := by
    rw [hshift, hbase]
    have hid : 2 + (9 / 2 : ℝ) * (M : ℝ) * (((M : ℝ) / mu) - 1) ^ 2 / ((M : ℝ) / mu) -
        2 * ((M : ℝ) + 3) *
          (G (5 / 2 * Real.log ((M : ℝ) / mu)) +
            fiberUpperK M / ((M : ℝ) + 3) * G1 (5 / 2 * Real.log ((M : ℝ) / mu)) +
            (fiberUpperK M / ((M : ℝ) + 3)) ^ 2 / 2 * G2 (5 / 2 * Real.log ((M : ℝ) / mu))) =
        fiberTaylorEndpoint ((M : ℝ) / mu) (M : ℝ) (fiberUpperK M) := by
      unfold fiberTaylorEndpoint fiberTaylorS
      field_simp [hm.ne', ht.ne'] <;> ring
    rw [← hid]
    exact sub_le_sub_left hscaled _
  have hends := fiber_concave_quadratic_endpoints
    (A := (M : ℝ) * fiberTaylorS ((M : ℝ) / mu) + 2 - 6 * G (5 / 2 * Real.log ((M : ℝ) / mu)))
    (B := -2 * G1 (5 / 2 * Real.log ((M : ℝ) / mu)))
    (C := G2 (5 / 2 * Real.log ((M : ℝ) / mu)) / ((M : ℝ) + 3))
    (by linarith : (71 / 20 : ℝ) ≤ 77 / 20 + 10 / (M : ℝ)) hk.1 hk.2
    (div_nonneg (shared_G2_pos _).le hm.le)
  have hends' : fiberTaylorT ((M : ℝ) / mu) (M : ℝ) ≤
      fiberTaylorEndpoint ((M : ℝ) / mu) (M : ℝ) (fiberUpperK M) := by
    convert hends using 1
    · unfold fiberTaylorT fiberTaylorEndpoint
      congr 1 <;> ring
    · unfold fiberTaylorEndpoint
      ring
  exact hends'.trans hpoly

end Erdos993Lean.Analytic.V213
