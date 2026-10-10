module

public import Erdos993Lean.Analytic.V213.FiberSmallWidths
public import Erdos993Lean.Analytic.V213.FiberRayDefinitions

/-!
Generic actual-kernel normalization for Eq91/92. The variance
lower bound uses the absolute skew but leaves the original probability
unchanged. The full rank minimum includes both infinite tails and M=0.

-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

noncomputable def fiberTailC (rhi : ℝ) : ℝ :=
  (4*fiberAG*Real.sqrt ((1-rhi^2)/4))⁻¹

theorem fiber_tail_variance_lower {q rhi : ℝ} (hr0 : 0 ≤ rhi)
    (hr : |fiberSkew q| ≤ rhi) : (1-rhi^2)/4 ≤ fiberVariance q := by
  have hs := (sq_le_sq₀ (abs_nonneg (fiberSkew q)) hr0).2 hr
  rw [sq_abs] at hs
  have hv := fiber_variance_skew q
  nlinarith only [hs,hv]

theorem fiber_tail_C_pos {rhi : ℝ} (hr0 : 0 ≤ rhi) (hr1 : rhi < 1) : 0 < fiberTailC rhi := by
  have hs : 0 < (1-rhi^2)/4 := by nlinarith only [hr0,hr1]
  unfold fiberTailC
  have ha := fiber_AG_pos
  have hsq := Real.sqrt_pos.mpr hs
  positivity

theorem fiber_tail_normalization_upper {q mu rhi : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hmu : 0 < mu) (hr0 : 0 ≤ rhi) (hr1 : rhi < 1) (hr : |fiberSkew q| ≤ rhi) :
    fiberNormalization q mu ≤ fiberTailC rhi * mu^(3/2 : ℝ) := by
  have hv := fiber_tail_variance_lower hr0 hr
  have hs := Real.sqrt_le_sqrt hv
  have ha := fiber_AG_pos
  have hden : 0 < 4*fiberAG*Real.sqrt ((1-rhi^2)/4) := by
    have hsq : 0 < (1-rhi^2)/4 := by nlinarith only [hr0,hr1]
    have hp := Real.sqrt_pos.mpr hsq
    positivity
  have hprod := mul_le_mul_of_nonneg_left hs (show 0 ≤ 4*fiberAG by positivity)
  have h := div_le_div_of_nonneg_left (Real.rpow_nonneg hmu.le (3/2 : ℝ)) hden hprod
  unfold fiberNormalization fiberTailC
  simpa only [Real.rpow_eq_pow,div_eq_mul_inv,mul_comm] using h

theorem fiber_tail_F_lower {q mu rhi K : ℝ} {M : ℕ}
    (hq0 : 0 < q) (hq1 : q < 1) (hmu : 0 < mu)
    (hr0 : 0 ≤ rhi) (hr1 : rhi < 1) (hr : |fiberSkew q| ≤ rhi) (hK : 0 ≤ K)
    (hkernel : ∀ j : ℤ, -K ≤ kernel2 q (fiberWeightL q) (fiberWeightR q) M j) (j : ℤ) :
    -(fiberTailC rhi*mu^(3/2 : ℝ)*K) ≤ fiberF q mu M j := by
  have hn := fiber_normalization_pos hq0 hq1 hmu
  have hu := fiber_tail_normalization_upper hq0 hq1 hmu hr0 hr1 hr
  have h1 := mul_le_mul_of_nonneg_left (hkernel j) hn.le
  have h2 := mul_le_mul_of_nonneg_right hu hK
  have hs : 0 ≤ fiberOffset q M j^2/(fiberVariance q*mu) :=
    div_nonneg (sq_nonneg _) (mul_nonneg (fiber_variance_pos hq0 hq1).le hmu.le)
  unfold fiberF
  nlinarith only [h1,h2,hs]

theorem fiber_tail_deficit_lower_kernel {q mu rhi K : ℝ} {M : ℕ} (g : ℝ → ℝ)
    (hq0 : 0 < q) (hq1 : q < 1) (hmu : 0 < mu)
    (hr0 : 0 ≤ rhi) (hr1 : rhi < 1) (hr : |fiberSkew q| ≤ rhi) (hK : 0 ≤ K)
    (htarget : fiberPsi ((M : ℝ)/mu)+g ((M : ℝ)/mu) ≤ 0)
    (hkernel : ∀ j : ℤ, -K ≤ kernel2 q (fiberWeightL q) (fiberWeightR q) M j) :
    fiberDeficit q mu g M ≤ fiberTailC rhi*mu^(3/2 : ℝ)*K := by
  have hmin := fiber_minimum_lower hq0 hq1 hmu M
    (fiber_tail_F_lower hq0 hq1 hmu hr0 hr1 hr hK hkernel)
  have hC := (fiber_tail_C_pos hr0 hr1).le
  have hp : 0 ≤ fiberTailC rhi*mu^(3/2 : ℝ)*K :=
    mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hmu.le (3/2 : ℝ))) hK
  unfold fiberDeficit
  exact max_le hp (by linarith only [htarget,hmin])

end Erdos993Lean.Analytic.V213
