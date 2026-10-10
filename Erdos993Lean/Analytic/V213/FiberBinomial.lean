module

public import Erdos993Lean.Analytic.V213.FiberKernel
public import Erdos993Lean.Analytic.V213.FiberAmplitudes

/-!
Exact binomial upper and lower estimates, `r12:eq69`.
The lower law uses the actual current c_N.
The lower coordinate is bound to the printed u and integer J=j+1.
The upper estimate covers every integer rank, including off-support ranks.
No generated finite family is consumed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Erdos993Lean.Analytic.V22.Analysis

theorem fiber_symmetric_binomial_upper {N : ℕ} (hN : 2 ≤ N) (J : ℤ) :
    binom N (1 / 2) J ≤ fiberUpperPrefactor N *
      Real.exp (-2 * ((J : ℝ) - (N : ℝ) / 2) ^ 2 / ((N : ℝ) + 1)) :=
  symmetric_binomial_upper hN J

theorem fiber_tilt_coordinate (q : ℝ) (M : ℕ) (j : ℤ) :
    interiorTiltCoordinate (fiberSkew q) (M + 2) (j + 1) =
      2 * (fiberOffset q M j - fiberSkew q) / ((M : ℝ) + 3) := by
  unfold interiorTiltCoordinate interiorSymmetricCoordinate fiberOffset fiberSkew
  push_cast
  have hm : (M : ℝ) + 3 ≠ 0 := by positivity
  field_simp [hm]
  ring

theorem fiber_binomial_local_lower {N : ℕ} (hN : 2 ≤ N)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (J : ℤ)
    (hJ0 : 0 ≤ J) (hJN : J ≤ (N : ℤ)) :
    fiberCentralPrefactor N / Real.sqrt (1 - r ^ 2) *
      Real.exp (-((N : ℝ) + 1) * sharedKLPsi r (interiorTiltCoordinate r N J)) ≤
      binom N ((1 + r) / 2) J := by
  rw [show fiberCentralPrefactor N = interiorCentralPrefactor N from shared_centralAmplitude_eq N]
  exact binomial_local_lower hN hr0 hr1 J hJ0 hJN

theorem fiber_binomial_local_lower_offset {M : ℕ} {q : ℝ}
    (hq0 : 1 / 2 ≤ q) (hq1 : q < 1) (j : ℤ)
    (hJ0 : 0 ≤ j + 1) (hJN : j + 1 ≤ ((M + 2 : ℕ) : ℤ)) :
    fiberCentralPrefactor (M + 2) / Real.sqrt (1 - fiberSkew q ^ 2) *
      Real.exp (-((M : ℝ) + 3) * sharedKLPsi (fiberSkew q)
        (2 * (fiberOffset q M j - fiberSkew q) / ((M : ℝ) + 3))) ≤
      binom (M + 2) q (j + 1) := by
  have hr0 : 0 ≤ fiberSkew q := by unfold fiberSkew; linarith
  have hr1 : fiberSkew q < 1 := by unfold fiberSkew; linarith
  have h := fiber_binomial_local_lower (by omega : 2 ≤ M + 2) hr0 hr1 (j+1) hJ0 hJN
  rw [fiber_tilt_coordinate] at h
  have hq : (1 + fiberSkew q) / 2 = q := by unfold fiberSkew; ring
  rw [hq] at h
  simpa only [Nat.cast_add, Nat.cast_ofNat, show ((M : ℝ) + 2) + 1 = (M : ℝ) + 3 by ring] using h

end Erdos993Lean.Analytic.V213
