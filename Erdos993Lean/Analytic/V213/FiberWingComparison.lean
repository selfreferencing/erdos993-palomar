module

public import Erdos993Lean.Analytic.V213.FiberWingPositive
public import Erdos993Lean.Analytic.V213.FiberPointwiseReflection

/-!
The literal Theorem6.16 for all three printed wing identities,
including both sides of q=1/2 and every closed skew/start/mean seam.
Only the pointwise F and offset case are reflected. Original q is retained
for all subsequent Laplace weights, Z(1-q)^M and tail calculations.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

theorem fiber_wing_comparison (id : FiberWingIdentity) {q mu : ℝ}
    (hmu : lowMeanFractionReal (fiberWingById id).mu_W ≤ mu)
    (hqlo : lowMeanFractionReal (fiberWingById id).skew_lower ≤ |fiberSkew q|)
    (hqhi : |fiberSkew q| ≤ lowMeanFractionReal (fiberWingById id).skew_upper)
    (M : ℕ) (j : ℤ) (htlo : lowMeanFractionReal (fiberWingById id).tau ≤ (M : ℝ) / mu)
    (hthi : (M : ℝ) / mu ≤ 3 / 5) :
    fiberPsi ((M : ℝ) / mu) ≤ fiberF q mu M j := by
  by_cases hq : 1 / 2 ≤ q
  · have hr0 : 0 ≤ fiberSkew q := by unfold fiberSkew; linarith only [hq]
    rw [abs_of_nonneg hr0] at hqlo hqhi
    exact fiber_wing_positive_comparison id hmu hqlo hqhi M j htlo hthi
  · have hr0 : fiberSkew q ≤ 0 := by unfold fiberSkew; linarith only [hq]
    have hr : fiberSkew (1 - q) = |fiberSkew q| := by
      rw [fiber_skew_reflect,abs_of_nonpos hr0]
    have hf := fiber_wing_positive_comparison (q := 1 - q) (mu := mu) id hmu
      (by simpa only [hr] using hqlo) (by simpa only [hr] using hqhi)
      M ((M : ℤ) - j) htlo hthi
    rw [fiber_F_reflect] at hf
    exact hf

end Erdos993Lean.Analytic.V213
