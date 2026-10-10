module

public import Erdos993Lean.BCFG.ChartDefinitions

/-!
Auxiliary endpoint algebra for the full light source minorant.
These are literal scalar residuals. No equality with the actual source g,
phase concavity, or endpoint source bound is a premise or a conclusion here.
Those separate analytic facts are required before deriving Lemma 5.16.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Erdos993Lean.BCFG.Analytic

theorem light_left_residual (lam omega : ℝ) (hl : lam ≠ 0)
    (hd : 1+lam*omega ≠ 0) (he : 1+lam+lam*omega ≠ 0) :
    sourceA lam*occupation lam omega*rhoZero lam omega-
      (lightSourceA lam omega*rhoZero lam omega+lightSourceB lam omega) =
    (1-omega)*((1+lam)*omega-1)/(4*lam^2*(1+lam+lam*omega)) := by
  unfold sourceA occupation rhoZero lightSourceA lightSourceB
  field_simp [hl, hd, he] <;> ring

theorem light_middle_residual (lam omega : ℝ) (hl : lam ≠ 0) (hw : omega ≠ 0)
    (hd : 1+lam*omega ≠ 0) (hs : 1+2*lam ≠ 0) :
    1/2+((1-omega)/omega)*((1+lam)*omega-1)/(4*lam^2)-
      (lightSourceA lam omega*((lam/(1+2*lam))/occupation lam omega)+
        lightSourceB lam omega) = 0 := by
  unfold lightSourceA lightSourceB occupation
  have hd' : 1+omega*lam ≠ 0 := by simpa only [mul_comm] using hd
  field_simp [hl, hw, hd, hs] <;> ring_nf <;> field_simp [hd'] <;> ring

theorem light_right_residual (lam omega : ℝ) (hl : lam ≠ 0)
    (h1 : 1+lam ≠ 0) (hd : 1+lam*omega ≠ 0) :
    sourceA lam/q lam*occupation lam omega-1/(2*lam)-
      (lightSourceA lam omega+lightSourceB lam omega) =
    (1-omega)*((1+lam)*omega-1)/(4*lam^2*(1+lam*omega)) := by
  unfold sourceA q occupation lightSourceA lightSourceB
  field_simp [hl, h1, hd] <;> ring

/-- The two factors appearing in both outer residuals are nonnegative on full light. -/
theorem light_residual_numerator_nonneg {lam omega : ℝ} (hl : 0 < lam)
    (hlo : 1/(1+lam) ≤ omega) (hhi : omega ≤ 1) :
    0 ≤ (1-omega)*((1+lam)*omega-1) := by
  have hd : 0 < 1+lam := by linarith
  have hx : 1 ≤ omega*(1+lam) := (div_le_iff₀ hd).mp hlo
  exact mul_nonneg (sub_nonneg.mpr hhi) (by nlinarith)

theorem light_left_endpoint_minorant {lam omega : ℝ} (hl : 0 < lam)
    (hlo : 1/(1+lam) ≤ omega) (hhi : omega ≤ 1) :
    lightSourceA lam omega*rhoZero lam omega+lightSourceB lam omega ≤
      sourceA lam*occupation lam omega*rhoZero lam omega := by
  have hw : 0 < omega := (one_div_pos.mpr (show 0 < 1+lam by linarith)).trans_le hlo
  have hd : 0 < 1+lam*omega := by positivity
  have he : 0 < 1+lam+lam*omega := by positivity
  have h := div_nonneg (light_residual_numerator_nonneg hl hlo hhi)
    (show 0 ≤ 4*lam^2*(1+lam+lam*omega) by positivity)
  rw [← light_left_residual lam omega hl.ne' hd.ne' he.ne'] at h
  exact sub_nonneg.mp h

theorem light_middle_endpoint_identity {lam omega : ℝ} (hl : 0 < lam)
    (hlo : 1/(1+lam) ≤ omega) :
    lightSourceA lam omega*((lam/(1+2*lam))/occupation lam omega)+
      lightSourceB lam omega =
    1/2+((1-omega)/omega)*((1+lam)*omega-1)/(4*lam^2) := by
  have hw : 0 < omega := (one_div_pos.mpr (show 0 < 1+lam by linarith)).trans_le hlo
  have hd : 0 < 1+lam*omega := by positivity
  have hs : 0 < 1+2*lam := by linarith
  have h := light_middle_residual lam omega hl.ne' hw.ne' hd.ne' hs.ne'
  linarith

theorem light_right_endpoint_minorant {lam omega : ℝ} (hl : 0 < lam)
    (hlo : 1/(1+lam) ≤ omega) (hhi : omega ≤ 1) :
    lightSourceA lam omega+lightSourceB lam omega ≤
      sourceA lam/q lam*occupation lam omega-1/(2*lam) := by
  have hw : 0 < omega := (one_div_pos.mpr (show 0 < 1+lam by linarith)).trans_le hlo
  have h1 : 0 < 1+lam := by linarith
  have hd : 0 < 1+lam*omega := by positivity
  have h := div_nonneg (light_residual_numerator_nonneg hl hlo hhi)
    (show 0 ≤ 4*lam^2*(1+lam*omega) by positivity)
  rw [← light_right_residual lam omega hl.ne' h1.ne' hd.ne'] at h
  exact sub_nonneg.mp h

/-- The middle endpoint product estimate needed before comparing with actual g. -/
theorem min_ge_product_div {lam A B : ℝ} (hl : 0 < lam)
    (hA : 0 ≤ A) (hAl : A ≤ lam) (hB : 0 ≤ B) (hBl : B ≤ lam) :
    A*B/lam ≤ min A B := by
  apply le_min
  · apply (div_le_iff₀ hl).2
    exact mul_le_mul_of_nonneg_left hBl hA
  · apply (div_le_iff₀ hl).2
    nlinarith [mul_le_mul_of_nonneg_right hAl hB]

end Erdos993Lean.BCFG.Analytic

#check Erdos993Lean.BCFG.Analytic.light_left_residual
#print axioms Erdos993Lean.BCFG.Analytic.light_left_residual
#check Erdos993Lean.BCFG.Analytic.light_middle_residual
#print axioms Erdos993Lean.BCFG.Analytic.light_middle_residual
#check Erdos993Lean.BCFG.Analytic.light_right_residual
#print axioms Erdos993Lean.BCFG.Analytic.light_right_residual
#check Erdos993Lean.BCFG.Analytic.light_residual_numerator_nonneg
#print axioms Erdos993Lean.BCFG.Analytic.light_residual_numerator_nonneg
#check Erdos993Lean.BCFG.Analytic.light_left_endpoint_minorant
#print axioms Erdos993Lean.BCFG.Analytic.light_left_endpoint_minorant
#check Erdos993Lean.BCFG.Analytic.light_middle_endpoint_identity
#print axioms Erdos993Lean.BCFG.Analytic.light_middle_endpoint_identity
#check Erdos993Lean.BCFG.Analytic.light_right_endpoint_minorant
#print axioms Erdos993Lean.BCFG.Analytic.light_right_endpoint_minorant
#check Erdos993Lean.BCFG.Analytic.min_ge_product_div
#print axioms Erdos993Lean.BCFG.Analytic.min_ge_product_div
