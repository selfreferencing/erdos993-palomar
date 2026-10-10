module

public import Erdos993Lean.Analytic.V213.FiberAffineExponentComponents

/-!
The complete printed Eq85 exponent budgets on all real shifted widths.
Each finite strict budget and root bound is consumed by its accepted F03
printed identity. The actual E_(3/2), amplitude h(N), rho and xi correction
are bounded analytically; no numerical side hypothesis remains.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real

noncomputable def fiberAffineExponent (N r w : ℝ) : ℝ :=
  V22.rho N * (1 - w) / 2 - ((77 / 20 : ℝ) + 10 / (N - 2)) / (N + 1) -
    fiberMassError N r (3 / 2) -
    (2 * (4 / 25 : ℝ) ^ 2 + fiberAffineK w * Real.sqrt N * (4 / 25)) / (N + 1)

theorem fiber_affine_exponent22 {N r w : ℝ} (hN : 22 ≤ N)
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hw0 : 0 ≤ w) :
    1 / 5 - (8 / 15 : ℝ) * w ≤ fiberAffineExponent N r w := by
  have hn : 0 < N := by linarith
  have hm : 0 < N + 1 := by linarith
  have hrho := fiber_affine_rho_loss hn hw0
  have hh := fiber_affine_h22 hN
  have he := (fiber_mass_error_w15_n22 hN hr0 hrh).2.le
  have hhalf : 1 / (2 * (N + 1)) ≤ (1 / 46 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * (N + 1))).2
    linarith only [hN]
  have hxi : 2 * (4 / 25 : ℝ) ^ 2 / (N + 1) ≤ 32 / 14375 := by
    apply (div_le_iff₀ hm).2
    linarith only [hN]
  have hroot := mul_le_mul_of_nonneg_left (fiber_affine_root_correction22 hN)
    (by linarith only [hw0] : 0 ≤ w + 3 / 2)
  have hc : (2 * (4 / 25 : ℝ) ^ 2 + fiberAffineK w * Real.sqrt N * (4 / 25)) / (N + 1) =
      2 * (4 / 25 : ℝ) ^ 2 / (N + 1) +
        (w + 3 / 2) * ((4 / 25 : ℝ) * Real.sqrt N / (Real.sqrt (3 / 2) * (N + 1))) := by
    unfold fiberAffineK
    rw [div_mul_eq_div_div]
    ring
  have hs := mul_le_mul_of_nonneg_right fiber_affine_slope22.le hw0
  have hb := fiber_affine_constant22.le
  unfold fiberAffineExponent
  rw [hc]
  nlinarith only [hrho,hh,he,hhalf,hxi,hroot,hs,hb]

theorem fiber_affine_exponent32 {N r w : ℝ} (hN : 32 ≤ N)
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hw0 : 0 ≤ w) :
    3 / 10 - (21 / 40 : ℝ) * w ≤ fiberAffineExponent N r w := by
  have hn : 0 < N := by linarith
  have hm : 0 < N + 1 := by linarith
  have hrho := fiber_affine_rho_loss hn hw0
  have hh := fiber_affine_h32 hN
  have he := (fiber_mass_error_w15_n32 hN hr0 hrh).2.le
  have hhalf : 1 / (2 * (N + 1)) ≤ (1 / 66 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * (N + 1))).2
    linarith only [hN]
  have hxi : 2 * (4 / 25 : ℝ) ^ 2 / (N + 1) ≤ 32 / 20625 := by
    apply (div_le_iff₀ hm).2
    linarith only [hN]
  have hroot := mul_le_mul_of_nonneg_left (fiber_affine_root_correction32 hN)
    (by linarith only [hw0] : 0 ≤ w + 3 / 2)
  have hc : (2 * (4 / 25 : ℝ) ^ 2 + fiberAffineK w * Real.sqrt N * (4 / 25)) / (N + 1) =
      2 * (4 / 25 : ℝ) ^ 2 / (N + 1) +
        (w + 3 / 2) * ((4 / 25 : ℝ) * Real.sqrt N / (Real.sqrt (3 / 2) * (N + 1))) := by
    unfold fiberAffineK
    rw [div_mul_eq_div_div]
    ring
  have hs := mul_le_mul_of_nonneg_right fiber_affine_slope32.le hw0
  have hb := fiber_affine_constant32.le
  unfold fiberAffineExponent
  rw [hc]
  nlinarith only [hrho,hh,he,hhalf,hxi,hroot,hs,hb]

end Erdos993Lean.Analytic.V213
