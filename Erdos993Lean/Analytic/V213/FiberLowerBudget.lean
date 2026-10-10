module

public import Erdos993Lean.Analytic.V213.FiberLowerDamping

/-!
Eq82 and the literal simplified gain from Eq75/81/82.
The exact positive budget is proved algebraically on all real N>=14;
its generic mass-error premise is the printed bound and is discharged by
actual Eq74 in the concrete consumer. No paper theorem is assumed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real

noncomputable def fiberLowerShiftBound (N : ℝ) : ℝ := (77 / 20 + 10 / (N - 2)) / (N + 1)

theorem fiber_lower_budget_identity {N : ℝ} (hN : 14 ≤ N) :
    5 / (N - 2) - fiberLowerShiftBound N - 1 / (3 * N) - 1 / (2 * (N + 1)) - 1 / (N + 1) ^ 2 =
      (19 * N ^ 3 + 201 * N ^ 2 + 402 * N + 40) / (60 * N * (N - 2) * (N + 1) ^ 2) := by
  have hn : N ≠ 0 := by linarith
  have hn2 : N - 2 ≠ 0 := by linarith
  have hm : N + 1 ≠ 0 := by linarith
  unfold fiberLowerShiftBound
  field_simp [hn, hn2, hm] <;> ring

theorem fiber_lower_budget_positive {N : ℝ} (hN : 14 ≤ N) :
    fiberLowerShiftBound N + 1 / (3 * N) + 1 / (2 * (N + 1)) + 1 / (N + 1) ^ 2 < 5 / (N - 2) := by
  have hn : 0 < N := by linarith
  have hn2 : 0 < N - 2 := by linarith
  have hm : 0 < N + 1 := by linarith
  have hnum : 0 < 19 * N ^ 3 + 201 * N ^ 2 + 402 * N + 40 := by positivity
  have hd : 0 < (19 * N ^ 3 + 201 * N ^ 2 + 402 * N + 40) /
      (60 * N * (N - 2) * (N + 1) ^ 2) := by positivity
  linarith [fiber_lower_budget_identity hN]

theorem fiber_lower_scalar_gain {N w xi t E : ℝ} (hN : 14 ≤ N)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hxi0 : 0 ≤ xi) (hxisq : xi ^ 2 ≤ 1 / 3)
    (ht : 0 < t) (hE : E < 1 / (3 * N)) :
    w + (1 - w) * t ^ (-(5 / 2 : ℝ)) * (1 + (1 - w) / 2 - 5 / (N - 2)) ≤
      w + t ^ (-(5 / 2 : ℝ)) *
        Real.exp (Erdos993Lean.Analytic.V22.rho N * (1 - w) / 2 - fiberLowerShiftBound N - E) *
        (1 - w + fiberLowerH N * xi ^ 2) *
        Real.exp (-(2 * xi ^ 2 + 2 * xi * Real.sqrt (N * w)) / (N + 1)) := by
  have hn : 0 < N := by linarith
  have hm : 0 < N + 1 := by linarith
  have ha : 0 ≤ 1 - w := by linarith
  have hb := fiber_lower_budget_positive hN
  have hrho : Erdos993Lean.Analytic.V22.rho N * (1 - w) / 2 =
      (1 - w) / 2 - (1 - w) / (2 * (N + 1)) := by
    unfold Erdos993Lean.Analytic.V22.rho
    field_simp [hm.ne'] <;> ring
  have hadiv : (1 - w) / (2 * (N + 1)) ≤ 1 / (2 * (N + 1)) :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  have harg : (1 - w) / 2 - 5 / (N - 2) ≤
      Erdos993Lean.Analytic.V22.rho N * (1 - w) / 2 - fiberLowerShiftBound N - E -
        1 / (N + 1) ^ 2 := by
    rw [hrho]
    linarith
  have hdamp := fiber_lower_damping_square hN hw0 hw1 hxi0 hxisq
  have hpositive : 0 ≤ Real.exp (Erdos993Lean.Analytic.V22.rho N * (1 - w) / 2 - fiberLowerShiftBound N - E) := Real.exp_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hdamp hpositive
  have hcomb : Real.exp (Erdos993Lean.Analytic.V22.rho N * (1 - w) / 2 - fiberLowerShiftBound N - E) *
      ((1 - w) * Real.exp (-1 / (N + 1) ^ 2)) =
        (1 - w) * Real.exp (Erdos993Lean.Analytic.V22.rho N * (1 - w) / 2 -
          fiberLowerShiftBound N - E - 1 / (N + 1) ^ 2) := by
    calc
      _ = (1 - w) * (Real.exp (Erdos993Lean.Analytic.V22.rho N * (1 - w) / 2 - fiberLowerShiftBound N - E) *
          Real.exp (-1 / (N + 1) ^ 2)) := by ring
      _ = (1 - w) * Real.exp ((Erdos993Lean.Analytic.V22.rho N * (1 - w) / 2 - fiberLowerShiftBound N - E) +
          (-1 / (N + 1) ^ 2)) := by rw [Real.exp_add]
      _ = _ := by congr 1; ring

  rw [hcomb] at hmul
  have he := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) ha
  have hlinear := mul_le_mul_of_nonneg_left
    (Real.add_one_le_exp ((1 - w) / 2 - 5 / (N - 2))) ha
  have hchain : (1 - w) * (1 + (1 - w) / 2 - 5 / (N - 2)) ≤
      Real.exp (Erdos993Lean.Analytic.V22.rho N * (1 - w) / 2 - fiberLowerShiftBound N - E) *
        ((1 - w + fiberLowerH N * xi ^ 2) *
          Real.exp (-(2 * xi ^ 2 + 2 * xi * Real.sqrt (N * w)) / (N + 1))) := by
    convert hlinear.trans (he.trans hmul) using 1 <;> ring
  have hfinal := mul_le_mul_of_nonneg_left hchain (Real.rpow_nonneg ht.le (-(5 / 2 : ℝ)))
  convert add_le_add_left hfinal w using 1 <;> ring

end Erdos993Lean.Analytic.V213
