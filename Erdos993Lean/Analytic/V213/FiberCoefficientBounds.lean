module

public import Erdos993Lean.Analytic.V22.Analysis.LinearizedBounds
public import Erdos993Lean.Analytic.V22.Analysis.CoefficientMonotonicity
public import Mathlib.Analysis.SpecialFunctions.Artanh

/-!
The literal coefficients in Eq.76--77 and Lemma 6.9.
The accepted common functions retain their
original definitions; the equalities below identify the printed formulas.
No generated DF10 records are consumed.

The stronger activity-endpoint clause is stated with its necessary
nonnegative lower endpoint. The omitted endpoint condition in Lemma 6.9 is an
author-confirmed correction (7 October 2026).

-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Erdos993Lean.Analytic.V22.Analysis

theorem fiber_artanh_source {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 2) :
    V22.artanh r = Real.artanh r := by
  rw [Real.artanh_eq_half_log ⟨by linarith, by linarith⟩]
  unfold V22.artanh
  ring

theorem fiber_upper_small_coefficients {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 2) :
    (0 ≤ V22.aHat r ∧ V22.aHat r ≤ r ^ 3 / (3 * (1 - r ^ 2))) ∧
      (0 ≤ V22.cr r ∧ V22.cr r ≤ r ^ 4 / (12 * (1 - r ^ 2) ^ 2)) := by
  exact ⟨sharedAHat_bounds hr0 (by linarith),
    shared_cr_nonneg hr0 (by linarith), shared_cr_quartic_bound hr0 hr1⟩

theorem fiber_upper_coefficient_formulas (r N : ℝ) :
    V22.aHat r = V22.artanh r - r ∧
    V22.cr r = (V22.artanh r ^ 2 + Real.log (1 - r ^ 2)) / 2 ∧
    V22.epsilonPrime r N =
      4 * (r + (N + 1) * V22.aHat r / 2) *
        Real.sqrt ((1 - r ^ 2) / 4 * N) / (N + 1) ∧
    V22.c0Prime r N = 2 * (r + (N + 1) * V22.aHat r / 2) ^ 2 / (N + 1) ∧
    V22.rhoU r N = (1 - r ^ 2) * V22.rho N -
      V22.epsilonPrime r N / Real.sqrt (V22.gamma r N) ∧
    V22.eU r N = r ^ 2 * V22.rho N / 2 +
      V22.epsilonPrime r N / 2 *
        (Real.sqrt (V22.gamma r N) + 1 / Real.sqrt (V22.gamma r N)) +
      (N + 1) * V22.cr r - V22.c0Prime r N := by
  simp [V22.aHat, V22.cr, V22.epsilonPrime, V22.yTilde, V22.sN,
    V22.varianceR, V22.c0Prime, V22.rhoU, V22.eU, mul_comm]

theorem fiber_rhoStar_formula (N rm : ℝ) :
    V22.rhoStar N rm = (1 - rm ^ 2) * V22.rho N -
      (2 / (N + 1) + rm ^ 2 / (3 * (1 - rm ^ 2))) /
        Real.sqrt (1 - 1 / N) := by
  unfold V22.rhoStar V22.cCoef
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem fiber_kappaA_formula (N rm : ℝ) :
    V22.kappaA N rm = 2 + 2 * (N + 1) /
      (3 * N * (1 - rm ^ 2) * Real.sqrt (1 - 1 / N)) := rfl

theorem fiber_E_formula (N rm zeta : ℝ) :
    V22.E N rm zeta = 2 * zeta + zeta ^ 2 / 2 +
      5 * zeta ^ 3 / (6 * (1 - rm ^ 2)) +
      (N + 1) * zeta ^ 4 / (12 * N * (1 - rm ^ 2) ^ 2) +
      zeta ^ 5 / (12 * (1 - rm ^ 2) ^ 2) := by
  unfold V22.E V22.e2 V22.e3 V22.e4 V22.e5
  ring

theorem fiber_upper_rate_lower {r rm N : ℝ} (hN : 10 ≤ N)
    (hr0 : 0 ≤ r) (hrrm : r ≤ rm) (hrm : rm ≤ 1 / 2) :
    V22.rhoStar N rm ≤ V22.rhoU r N :=
  linearized_rhoU_lower hN hr0 hrrm hrm

theorem fiber_upper_reciprocal_loss {r rm N : ℝ} (hN : 10 ≤ N)
    (hr0 : 0 ≤ r) (hrrm : r ≤ rm) (hrm : rm ≤ 1 / 2)
    (_hStar : 0 < V22.rhoStar N rm) :
    2 * N * ((V22.rhoU r N)⁻¹ - (V22.rho N)⁻¹) ≤
      (4 * (r * Real.sqrt N) + V22.kappaA N rm * (r * Real.sqrt N) ^ 2) /
        V22.rhoStar N rm := by
  simpa only [one_div, activityNu] using linearized_reciprocal_loss hN hr0 hrrm hrm

theorem fiber_upper_exponent_loss {r rm N : ℝ} (hN : 10 ≤ N)
    (hr0 : 0 ≤ r) (hrrm : r ≤ rm) (hrm : rm ≤ 1 / 2) :
    N * V22.eU r N ≤ 2 * (r * Real.sqrt N) + (r * Real.sqrt N) ^ 2 / 2 +
      5 * (r * Real.sqrt N) ^ 3 / (6 * (1 - rm ^ 2)) +
      (N + 1) * (r * Real.sqrt N) ^ 4 / (12 * N * (1 - rm ^ 2) ^ 2) +
      (r * Real.sqrt N) ^ 5 / (12 * (1 - rm ^ 2) ^ 2) := by
  rw [← fiber_E_formula]
  exact linearized_eU_upper hN hr0 hrrm hrm

theorem fiber_activity_bonus {r N : ℝ} (hN : 10 ≤ N)
    (hr0 : 0 ≤ r) (hrm : r ≤ 1 / 2) :
    (N - 1) * (r * Real.sqrt N) ^ 2 ≤ N * V22.Delta r N := by
  exact scaled_delta_lower hN (by nlinarith)

/-- The stronger bonus on the explicitly nonnegative activity interval. -/
theorem fiber_activity_interval_bonus {r ra N : ℝ} (hN : 10 ≤ N)
    (hra : 0 ≤ ra) (har : ra ≤ r) (hrm : r ≤ 1 / 2) :
    (N - 1) * (r * Real.sqrt N) ^ 2 / (1 - ra ^ 2) ≤ N * V22.Delta r N := by
  exact scaled_delta_lower_activity hN hra har (by
    have hr0 := hra.trans har
    nlinarith)

theorem fiber_upper_coefficient_monotonicity {rm : ℝ}
    (hr0 : 0 ≤ rm) (hrm : rm ≤ 1 / 2) :
    AntitoneOn (fun N => V22.kappaA N rm) (Set.Ici 10) ∧
    AntitoneOn (fun _ : ℝ => (1 / 2 : ℝ)) (Set.Ici 10) ∧
    AntitoneOn (fun _ : ℝ => 5 / (6 * (1 - rm ^ 2))) (Set.Ici 10) ∧
    AntitoneOn (fun N => (N + 1) / (12 * N * (1 - rm ^ 2) ^ 2)) (Set.Ici 10) ∧
    AntitoneOn (fun _ : ℝ => 1 / (12 * (1 - rm ^ 2) ^ 2)) (Set.Ici 10) ∧
    MonotoneOn (fun N => V22.rhoStar N rm) (Set.Ici 10) := by
  have h := source_coefficient_monotonicity rm hr0 hrm
  have e := source_E_coefficient_monotonicity rm
  exact ⟨h.2.2.1, e.1, e.2.1, e.2.2.1, e.2.2.2, h.2.2.2.2⟩

end Erdos993Lean.Analytic.V213
