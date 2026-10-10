module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightDefs

/-! Actual half-light parent geometry: cavity/source minima and the printed
trapezoid factor A*. These claims do not use affine row bounds. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows

open FreeCountVariance.Envelopes

theorem halfParent_bounds {lam H : ℝ} (hl : 0 < lam) (hH : 0 ≤ H)
    (hHq : H ≤ childQ lam/2) :
    H < 1/2 ∧ 0 < halfParent lam H ∧ halfParent lam H < 1 ∧
      halfParent lam H ≤ childQ lam := by
  have hq1 : childQ lam < 1 := (div_lt_one (by linarith : 0 < 1+lam)).2 (by linarith)
  have hH1 : H < 1 := by linarith
  have hz : 0 < lam*(1-H) := mul_pos hl (by linarith)
  have hd : 0 < 1+lam*(1-H) := by linarith
  refine ⟨by linarith,div_pos hz hd,(div_lt_one hd).2 (by linarith),?_⟩
  change lam*(1-H)/(1+lam*(1-H)) ≤ lam/(1+lam)
  apply (div_le_div_iff₀ hd (by linarith)).2
  nlinarith [mul_nonneg hl.le hH]

theorem pStar_pos {lam : ℝ} (hl : 0 < lam) : 0 < pStar lam := by
  unfold pStar
  positivity

theorem pStar_lt_one {lam : ℝ} (hl : 0 < lam) : pStar lam < 1 := by
  unfold pStar
  apply (div_lt_one (by positivity)).2
  nlinarith

theorem pStar_monotone {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u) : pStar l ≤ pStar u := by
  have hu : 0 < u := lt_of_lt_of_le hl hlu
  have h1 : 0 < l^2+4*l+2 := by positivity
  have h2 : 0 < u^2+4*u+2 := by positivity
  unfold pStar
  apply (div_le_div_iff₀ h1 h2).2
  have h := mul_nonneg (sub_nonneg.mpr hlu)
    (show 0 ≤ 2*(l*u+l+u+2) by positivity)
  nlinarith

theorem piStar_monotone {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u) : piStar l ≤ piStar u := by
  have hu : 0 < u := lt_of_lt_of_le hl hlu
  have h1 : 0 < 3*l^2+6*l+2 := by positivity
  have h2 : 0 < 3*u^2+6*u+2 := by positivity
  unfold piStar
  apply (div_le_div_iff₀ h1 h2).2
  have h := mul_nonneg (sub_nonneg.mpr hlu) (show 0 ≤ 2*(l+u+2) by positivity)
  nlinarith

theorem pStar_le_halfParent {lam H : ℝ} (hl : 0 < lam) (hH : 0 ≤ H)
    (hHq : H ≤ childQ lam/2) : pStar lam ≤ halfParent lam H := by
  have hb := halfParent_bounds hl hH hHq
  have hd : 0 < 1+lam*(1-H) := by nlinarith [mul_pos hl (show 0 < 1-H by linarith [hb.1])]
  have hq : 2*H*(1+lam) ≤ lam :=
    (le_div_iff₀ (show 0 < 1+lam by linarith)).mp (show 2*H ≤ childQ lam by linarith)
  change lam*(lam+2)/(lam^2+4*lam+2) ≤ lam*(1-H)/(1+lam*(1-H))
  apply (div_le_div_iff₀ (by positivity) hd).2
  have hn := mul_nonneg hl.le (show 0 ≤ lam-2*H*(1+lam) by linarith)
  nlinarith

theorem piStar_identity {lam : ℝ} (hl : 0 < lam) :
    piStar lam = pStar lam/(1+lam*(1-pStar lam)) := by
  have hp1 := pStar_lt_one hl
  have hpm : 0 < 1-pStar lam := sub_pos.mpr hp1
  have hd : 0 < 1+lam*(1-pStar lam) := by positivity
  unfold piStar pStar at *
  field_simp [hd.ne',show lam^2+4*lam+2 ≠ 0 by positivity,
    show 3*lam^2+6*lam+2 ≠ 0 by positivity]
  all_goals ring_nf
  all_goals field_simp [show (2+lam*6+lam^2*3 : ℝ) ≠ 0 by positivity] <;> ring

theorem piStar_le_occupied {lam H rho : ℝ} (hl : 0 < lam) (hH : 0 ≤ H)
    (hHq : H ≤ childQ lam/2) (hr : rhoMin lam (halfParent lam H) ≤ rho) :
    piStar lam ≤ rho*halfParent lam H := by
  have hb := halfParent_bounds hl hH hHq
  have hp := pStar_le_halfParent hl hH hHq
  have hs := pStar_lt_one hl
  have hpm : 0 < 1-halfParent lam H := sub_pos.mpr hb.2.2.1
  have hsm : 0 < 1-pStar lam := sub_pos.mpr hs
  have hd : 0 < 1+lam*(1-halfParent lam H) := by positivity
  have hdS : 0 < 1+lam*(1-pStar lam) := by positivity
  have hm : pStar lam/(1+lam*(1-pStar lam)) ≤
      halfParent lam H/(1+lam*(1-halfParent lam H)) := by
    apply (div_le_div_iff₀ hdS hd).2
    nlinarith [mul_nonneg hl.le (sub_nonneg.mpr hp)]
  rw [← piStar_identity hl] at hm
  have hrp := mul_le_mul_of_nonneg_right hr hb.2.1.le
  unfold rhoMin at hrp
  have hi : (1/(1+lam*(1-halfParent lam H)))*halfParent lam H =
      halfParent lam H/(1+lam*(1-halfParent lam H)) := by ring
  rw [hi] at hrp
  exact hm.trans hrp

theorem half_rho_pos {lam H rho : ℝ} (hl : 0 < lam) (hH : 0 ≤ H)
    (hHq : H ≤ childQ lam/2) (hr : rhoMin lam (halfParent lam H) ≤ rho) : 0 < rho := by
  have hb := halfParent_bounds hl hH hHq
  have hpm : 0 < 1-halfParent lam H := sub_pos.mpr hb.2.2.1
  have hm : 0 < rhoMin lam (halfParent lam H) := by
    unfold rhoMin
    positivity
  exact hm.trans_le hr

theorem aStar_pos {lam : ℝ} (hl : 0 < lam) : 0 < aStar lam := by
  unfold aStar
  split_ifs <;> positivity

theorem aStar_le_trapezoid {lam H : ℝ} (hl : 0 < lam) (hH : 0 ≤ H)
    (hHq : H ≤ childQ lam/2) :
    aStar lam ≤ 2*(1+lam*(1-H))/(lam*(2-H)) := by
  have hb := halfParent_bounds hl hH hHq
  have hHm : 0 < 2-H := by linarith [hb.1]
  have hd : 0 < lam*(2-H) := by positivity
  unfold aStar
  split_ifs with he
  · apply (div_le_div_iff₀ hl hd).2
    have hx := mul_nonneg hH (sub_nonneg.mpr he)
    nlinarith [mul_nonneg hl.le hx]
  · have hq : 2*H*(1+lam) ≤ lam :=
      (le_div_iff₀ (show 0 < 1+lam by linarith)).mp (show 2*H ≤ childQ lam by linarith)
    have hx := mul_nonneg (show 0 ≤ lam-1 by linarith)
      (show 0 ≤ lam-2*H*(1+lam) by linarith)
    apply (div_le_div_iff₀ (by positivity) hd).2
    nlinarith [mul_nonneg hl.le hx]

theorem aStar_le_parent_ratio {lam H : ℝ} (hl : 0 < lam) (hH : 0 ≤ H)
    (hHq : H ≤ childQ lam/2) : aStar lam ≤ messageRatio H/halfParent lam H := by
  have hb := halfParent_bounds hl hH hHq
  have hHm : 0 < 1-H := by linarith [hb.1]
  have hh := messageRatio_lower hH (show H < 1 by linarith [hb.1])
  have hm := div_le_div_of_nonneg_right hh hb.2.1.le
  have hi : (2*(1-H)/(2-H))/halfParent lam H =
      2*(1+lam*(1-H))/(lam*(2-H)) := by
    unfold halfParent chartParent
    field_simp [hl.ne',show 1-H ≠ 0 by linarith [hb.1],
      show 2-H ≠ 0 by linarith [hb.1],show 1+lam*(1-H) ≠ 0 by positivity] <;> ring
  rw [hi] at hm
  exact (aStar_le_trapezoid hl hH hHq).trans hm

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.halfParent_bounds
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.halfParent_bounds
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.pStar_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.pStar_pos
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.pStar_lt_one
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.pStar_lt_one
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.pStar_monotone
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.pStar_monotone
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.piStar_monotone
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.piStar_monotone
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.pStar_le_halfParent
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.pStar_le_halfParent
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.piStar_identity
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.piStar_identity
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.piStar_le_occupied
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.piStar_le_occupied
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.half_rho_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.half_rho_pos
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.aStar_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.aStar_pos
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.aStar_le_trapezoid
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.aStar_le_trapezoid
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.aStar_le_parent_ratio
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.aStar_le_parent_ratio
