module

public import Erdos993Lean.Analytic.V213.FiberOuterClassRegions
public import Erdos993Lean.Analytic.V213.FiberAffineReflection

/-!
Literal Theorem6.18 for every one of the eight printed classes.
The whole natural-width and integer-rank domains, closed starts and
absolute skew ranges are covered by actual lower/upper-offset comparisons.
Reflection acts only on pointwise F,w,gamma; all later Laplace/tail factors
retain their original q.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

theorem fiber_outer_class_comparison_nonnegative (id : FiberOuterClassIdentity)
    {M : ℕ} {q mu : ℝ}
    (hmu : lowMeanFractionReal (fiberOuterClassById id).mu_D ≤ mu)
    (hra : lowMeanFractionReal (fiberOuterClassById id).skew_lower ≤ fiberSkew q)
    (hrb : fiberSkew q ≤ lowMeanFractionReal (fiberOuterClassById id).skew_upper)
    (ht : lowMeanFractionReal (fiberOuterClassById id).tau ≤ (M : ℝ) / mu) (j : ℤ) :
    let r := fiberOuterClassById id
    fiberPsi ((M : ℝ) / mu) + lowMeanFractionReal r.b +
      lowMeanFractionReal r.beta_prime * ((M : ℝ) / mu - 1) ≤ fiberF q mu M j := by
  have hc := fiber_outer_class_controls id
  rcases hc with ⟨hra0,hrb0,hb0,hb1,hbeta0,hbeta1,hmu40,ht0,hN,ha,hr,htau⟩
  by_cases hw : fiberSquareOffset q M j ≤ fiberBonus q M
  · have hq0 : 1 / 2 ≤ q := by unfold fiberSkew at hra; linarith only [hra,hra0]
    have hqh : q ≤ 3 / 4 := by unfold fiberSkew at hrb; linarith only [hrb,hrb0]
    have hl := fiber_uniform_affine_comparison hq0 hqh (hra0.trans hra) (hmu40.trans hmu)
      hb0 hb1 hbeta0 hbeta1 M j hw
    linarith only [hl]
  · exact fiber_outer_class_upper_comparison id hmu hra hrb ht j (le_of_lt (lt_of_not_ge hw))

theorem fiber_outer_class_comparison (id : FiberOuterClassIdentity)
    {M : ℕ} {q mu : ℝ}
    (hmu : lowMeanFractionReal (fiberOuterClassById id).mu_D ≤ mu)
    (hra : lowMeanFractionReal (fiberOuterClassById id).skew_lower ≤ |fiberSkew q|)
    (hrb : |fiberSkew q| ≤ lowMeanFractionReal (fiberOuterClassById id).skew_upper)
    (ht : lowMeanFractionReal (fiberOuterClassById id).tau ≤ (M : ℝ) / mu) (j : ℤ) :
    let r := fiberOuterClassById id
    fiberPsi ((M : ℝ) / mu) + lowMeanFractionReal r.b +
      lowMeanFractionReal r.beta_prime * ((M : ℝ) / mu - 1) ≤ fiberF q mu M j := by
  by_cases hr0 : 0 ≤ fiberSkew q
  · rw [abs_of_nonneg hr0] at hra hrb
    exact fiber_outer_class_comparison_nonnegative id hmu hra hrb ht j
  · have hneg : fiberSkew q ≤ 0 := (lt_of_not_ge hr0).le
    have hra' : lowMeanFractionReal (fiberOuterClassById id).skew_lower ≤ fiberSkew (1 - q) := by
      rw [fiber_skew_reflect]
      simpa only [abs_of_nonpos hneg] using hra
    have hrb' : fiberSkew (1 - q) ≤ lowMeanFractionReal (fiberOuterClassById id).skew_upper := by
      rw [fiber_skew_reflect]
      simpa only [abs_of_nonpos hneg] using hrb
    have hf := fiber_outer_class_comparison_nonnegative id hmu hra' hrb' ht ((M : ℤ) - j)
    rw [fiber_F_reflect] at hf
    exact hf

end Erdos993Lean.Analytic.V213
