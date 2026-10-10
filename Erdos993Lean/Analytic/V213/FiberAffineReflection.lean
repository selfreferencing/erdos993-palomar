module

public import Erdos993Lean.Analytic.V213.FiberAffineComparison
public import Erdos993Lean.Analytic.V213.FiberPointwiseReflection

/-!
Required below-half packaging of the accepted literal Theorem6.15.
Only the pointwise kernel is reflected, with both actual w and gamma.
The original q is retained for every subsequent Laplace/tail factor.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

theorem fiber_uniform_affine_comparison_reflected {q mu b beta : ℝ}
    (hql : 1 / 4 ≤ q) (hqh : q ≤ 3 / 4) (hrl : 4 / 25 ≤ |fiberSkew q|)
    (hmu : 40 ≤ mu) (hb0 : 0 ≤ b) (hbh : b ≤ 2 / 5)
    (hbeta0 : 0 ≤ beta) (hbetah : beta ≤ 1) (M : ℕ) (j : ℤ)
    (hw : fiberSquareOffset q M j ≤ fiberBonus q M) :
    fiberPsi ((M : ℝ) / mu) + b + beta * ((M : ℝ) / mu - 1) + 1 / 28 ≤
      fiberF q mu M j := by
  by_cases hq0 : 1 / 2 ≤ q
  · have hr0 : 0 ≤ fiberSkew q := by unfold fiberSkew; linarith only [hq0]
    rw [abs_of_nonneg hr0] at hrl
    exact fiber_uniform_affine_comparison hq0 hqh hrl hmu hb0 hbh hbeta0 hbetah M j hw
  · have hqr0 : 1 / 2 ≤ 1 - q := by linarith only [hq0]
    have hqrh : 1 - q ≤ 3 / 4 := by linarith only [hql]
    have hrneg : fiberSkew q ≤ 0 := by unfold fiberSkew; linarith only [hq0]
    have hr' : 4 / 25 ≤ fiberSkew (1 - q) := by
      rw [fiber_skew_reflect]
      simpa only [abs_of_nonpos hrneg] using hrl
    have hw' := (fiber_lower_offset_reflect q M j).mpr hw
    have hf := fiber_uniform_affine_comparison hqr0 hqrh hr' hmu hb0 hbh hbeta0 hbetah M
      ((M : ℤ) - j) hw'
    rw [fiber_F_reflect] at hf
    exact hf

end Erdos993Lean.Analytic.V213
