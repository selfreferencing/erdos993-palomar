module

public import Erdos993Lean.Analytic.V213.FiberRationalGainSkew

/-!
Lemma 6.22: the literal Eq100 rational expression is below the actual
Phi. This uses the already proved exact Eq78 and radical upper bound,
both artanh-error bounds, and every favorable quartic/sextic term.
No finite numerical premise or monotonicity assumption for Phi is retained.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real
open Erdos993Lean.Analytic.V22.Analysis

theorem fiber_phi_rational_diagonal {r N : ℝ} (hr : 0 < r) (hrh : r ≤ 1 / 2)
    (hN : 10 ≤ N) : fiberRationalGain r r N ≤ V22.phiR r N := by
  have hm0 : 0 < N + 1 := by linarith
  have hm2 : 0 < N + 1 - 2 := by linarith
  have ho : 0 < 1 - r ^ 2 := by nlinarith
  have hA0 := (sharedAHat_bounds hr.le (by linarith : r < 1)).1
  have hAu := (sharedAHat_bounds hr.le (by linarith : r < 1)).2
  have hAl := fiber_ahat_cubic_lower hr.le (by linarith : r < 1)
  have hcr := shared_cr_quartic_bound hr.le hrh
  have hsource := fiber_phi_completed_square hr hrh hN
  have hsourceEq :
      71 / (20 * (N + 1)) + (r * (N + 1 - 4) - (N + 1) * V22.aHat r) ^ 2 /
          (2 * (N + 1)) - N / ((N + 1) * (N + 1 - 2)) -
        V22.aHat r * N / (2 * r * (N + 1 - 2)) - (N + 1) * V22.cr r =
      (N + 1) * r ^ 2 / 2 - (N + 1) * r * V22.aHat r +
        (N + 1) * (V22.aHat r) ^ 2 / 2 - 4 * r ^ 2 + 4 * r * V22.aHat r +
          (8 * r ^ 2 + 71 / 20) / (N + 1) - N / ((N + 1) * (N + 1 - 2)) -
            V22.aHat r * N / (2 * r * (N + 1 - 2)) - (N + 1) * V22.cr r := by
    field_simp [hm0.ne',hm2.ne',hr.ne'] <;> ring
  rw [hsourceEq] at hsource
  have hcross := mul_le_mul_of_nonneg_left hAu (by positivity : 0 ≤ (N + 1) * r)
  have hcrossEq : (N + 1) * r * (r ^ 3 / (3 * (1 - r ^ 2))) =
      (N + 1) * r ^ 4 / (3 * (1 - r ^ 2)) := by ring
  rw [hcrossEq] at hcross
  have hn0 : 0 ≤ N := by linarith
  have hfrac := mul_le_mul_of_nonneg_right hAu
    (div_nonneg hn0 (by positivity) : 0 ≤ N / (2 * r * (N + 1 - 2)))
  have hfracEq : (r ^ 3 / (3 * (1 - r ^ 2))) * (N / (2 * r * (N + 1 - 2))) =
      r ^ 2 * N / (6 * (1 - r ^ 2) * (N + 1 - 2)) := by
    field_simp [ho.ne',hm2.ne',hr.ne'] <;> ring
  have hfracLeft : V22.aHat r * (N / (2 * r * (N + 1 - 2))) =
      V22.aHat r * N / (2 * r * (N + 1 - 2)) := by ring
  rw [hfracEq,hfracLeft] at hfrac
  have hcrmul := mul_le_mul_of_nonneg_left hcr hm0.le
  have hcrEq : (N + 1) * (r ^ 4 / (12 * (1 - r ^ 2) ^ 2)) =
      (N + 1) * r ^ 4 / (12 * (1 - r ^ 2) ^ 2) := by ring
  rw [hcrEq] at hcrmul
  have hAsq := (sq_le_sq₀ (by positivity : 0 ≤ r ^ 3 / 3) hA0).2 hAl
  have hs := mul_le_mul_of_nonneg_left hAsq (by positivity : 0 ≤ (N + 1) / 2)
  have hsEq : (N + 1) / 2 * (r ^ 3 / 3) ^ 2 = (N + 1) * r ^ 6 / 18 := by ring
  have hsEq2 : (N + 1) / 2 * (V22.aHat r) ^ 2 = (N + 1) * (V22.aHat r) ^ 2 / 2 := by ring
  rw [hsEq,hsEq2] at hs
  have hquart := mul_le_mul_of_nonneg_left hAl (by positivity : 0 ≤ 4 * r)
  have hquartEq : 4 * r * (r ^ 3 / 3) = 4 * r ^ 4 / 3 := by ring
  rw [hquartEq] at hquart
  have he : fiberRationalGain r r N =
      (N + 1) * r ^ 2 / 2 - (N + 1) * r ^ 4 / (3 * (1 - r ^ 2)) -
        (N + 1) * r ^ 4 / (12 * (1 - r ^ 2) ^ 2) - 4 * r ^ 2 +
          (8 * r ^ 2 + 71 / 20) / (N + 1) - N / ((N + 1) * (N + 1 - 2)) -
            r ^ 2 * N / (6 * (1 - r ^ 2) * (N + 1 - 2)) +
              4 * r ^ 4 / 3 + (N + 1) * r ^ 6 / 18 := by
    unfold fiberRationalGain fiberRationalA
    dsimp only
    field_simp [ho.ne',hm0.ne',hm2.ne'] <;> ring
  linarith only [hsource,hcross,hfrac,hcrmul,hs,hquart,he]

/-- Literal first assertion of Lemma 6.22, on the full printed real domain. -/
theorem fiber_rational_gain_actual {a r b N : ℝ} (ha : 0 < a) (har : a ≤ r)
    (hrb : r ≤ b) (hbh : b ≤ 1 / 2) (hN : 10 ≤ N) :
    fiberRationalGain a b N ≤ V22.phiR r N := by
  have hr : 0 < r := ha.trans_le har
  exact (fiber_rational_gain_skew_lower ha.le har hrb hbh hN).trans
    (fiber_phi_rational_diagonal hr (hrb.trans hbh) hN)

end Erdos993Lean.Analytic.V213
