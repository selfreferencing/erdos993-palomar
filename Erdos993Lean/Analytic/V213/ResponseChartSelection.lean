module

public import Erdos993Lean.Analytic.V213.ResponseChartCoordinates

/-! The phase-specific source selections in current Lemma 5.23.
In particular phase 1 uses the upper vacancy endpoint, not the lower endpoint;
the two reduced-source regions use their printed closed x inequalities.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse

private theorem sourceSwitch_mul {q : ℝ} (hq : 0 < q) :
    sourceSwitch q*(1+q) = q := div_mul_cancel₀ _ (by positivity)

theorem source_phase_one_branch {lam p rho : ℝ} (hl : 0 < lam) (hp : 0 < p)
    (hr : rho ≤ rhoStar lam p) :
    O2.fq (actQ lam) (p*rho) = sourceSlopeA (actQ lam)*(p*rho) := by
  have hq : 0 < actQ lam := div_pos hl (by linarith)
  apply fq_lower_branch hq
    ((div_lt_one (by linarith : 0 < 1+lam)).2 (by linarith))
  have hh := (le_div_iff₀ hp).mp hr
  nlinarith

theorem source_phase_two_branch {lam p rho : ℝ} (hl : 0 < lam) (hp : 0 < p)
    (hr : rhoStar lam p ≤ rho) :
    O2.fq (actQ lam) (p*rho) = sourceSlopeB (actQ lam)*(p*rho)+sourceIntercept (actQ lam) := by
  have hq : 0 < actQ lam := div_pos hl (by linarith)
  apply fq_upper_branch hq
    ((div_lt_one (by linarith : 0 < 1+lam)).2 (by linarith))
  have hh := (div_le_iff₀ hp).mp hr
  nlinarith

theorem heavy_source {lam p rho : ℝ} (hl : 0 < lam) (hp : 0 < p)
    (hpq : p ≤ actQ lam) (hr : rhoMin lam p ≤ rho) (hr1 : rho ≤ 1)
    (hpstar : p ≤ sourceSwitch (actQ lam)) (hH : O2.cavH lam p = actQ lam) :
    O2.mUp lam p rho = actQ lam*(1-p*rho) ∧
      O2.src lam p rho = sourceSlopeA (actQ lam)*(p*rho) := by
  have hq : 0 < actQ lam := div_pos hl (by linarith)
  have hq1 : actQ lam < 1 := (div_lt_one (by linarith : 0 < 1+lam)).2 (by linarith)
  have hedges := source_physical_edges hl hp hpq hr hr1
  have hpi : p*rho ≤ sourceSwitch (actQ lam) := by nlinarith
  have hmax : O2.mUp lam p rho = actQ lam*(1-p*rho) := by
    unfold O2.mUp
    rw [hH, max_eq_right (by nlinarith [hedges.2.1])]
    ring
  refine ⟨hmax,?_⟩
  have hstar := sourceSwitch_mul hq
  have hm : sourceSwitch (actQ lam) ≤ actQ lam*(1-p*rho) := by
    have hh := mul_le_mul_of_nonneg_left hpi hq.le
    nlinarith
  rw [source_eq_second hl hp hpq hr hr1,hmax,
    fq_lower_branch hq hq1 hpi,fq_upper_branch hq hq1 hm]
  unfold sourceSlopeA sourceSlopeB sourceIntercept
  field_simp [hq.ne']
  ring

theorem source_phase_two_faces {lam p rho : ℝ} (hl : 0 < lam)
    (hp : 0 < p) (hpq : p ≤ actQ lam) (hr : rhoMin lam p ≤ rho) (hr1 : rho ≤ 1)
    (hphase : rhoStar lam p ≤ rho) :
    O2.src lam p rho = min
      ((1+O2.fq (actQ lam) (p*rho)-sourceSlopeA (actQ lam)*(1-rho))/2)
      ((1+O2.fq (actQ lam) (p*rho)-sourceSlopeA (actQ lam)*((1-p*rho)*O2.cavH lam p))/2) := by
  have hq : 0 < actQ lam := div_pos hl (by linarith)
  have hq1 : actQ lam < 1 := (div_lt_one (by linarith : 0 < 1+lam)).2 (by linarith)
  have hpi : sourceSwitch (actQ lam) ≤ p*rho := by
    have hh := (div_le_iff₀ hp).mp hphase
    nlinarith
  have he := source_physical_edges hl hp hpq hr hr1
  have hs := sourceSwitch_mul hq
  have hm1 : 1-rho ≤ sourceSwitch (actQ lam) := by nlinarith [he.1]
  have hm2 : (1-p*rho)*O2.cavH lam p ≤ sourceSwitch (actQ lam) := by nlinarith [he.2.2.1]
  rw [source_eq_second hl hp hpq hr hr1, O2.mUp, fq_max hq,
    fq_lower_branch hq hq1 hm1, fq_lower_branch hq hq1 hm2]
  rcases le_total (sourceSlopeA (actQ lam)*(1-rho))
      (sourceSlopeA (actQ lam)*((1-p*rho)*O2.cavH lam p)) with h | h
  · rw [max_eq_right h, min_eq_right (by linarith)]
  · rw [max_eq_left h, min_eq_left (by linarith)]

theorem light_gap_at_switch {lam omega : ℝ} (hl : 0 < lam) (ho : 0 < omega) :
    (1-chartParent lam omega*rhoStar lam (chartParent lam omega))*(1-omega)-
      (1-rhoStar lam (chartParent lam omega)) =
        (1-(1+lam)*omega^2)/((1+2*lam)*omega) := by
  have h1 : 1+lam*omega ≠ 0 := by positivity
  have h2 : 1+2*lam ≠ 0 := by positivity
  have hp : chartParent lam omega ≠ 0 := ne_of_gt (div_pos (mul_pos hl ho) (by positivity))
  unfold rhoStar
  rw [sourceSwitch_activity hl]
  unfold chartParent at *
  field_simp [hl.ne',ho.ne',h1,h2,hp]
  ring

theorem light_gap_increasing {p H rho sigma : ℝ} (hpH : p*H ≤ 1) (hr : rho ≤ sigma) :
    (1-p*rho)*H-(1-rho) ≤ (1-p*sigma)*H-(1-sigma) := by
  have h := mul_nonneg (sub_nonneg.mpr hr) (sub_nonneg.mpr hpH)
  nlinarith

theorem light_half_numerator {lam x : ℝ} (hl : 0 < lam)
    (hx : 0 ≤ x) (hxh : x ≤ 1/2) :
    1-(1+lam)*(lightOmega lam x)^2 ≤ 0 := by
  have hi : (1+lam)*(lightOmega lam x)^2-1 =
      lam*((1-2*x)+lam*(1-x)^2)/(1+lam) := by
    unfold lightOmega actQ
    field_simp [ne_of_gt (show 0 < 1+lam by linarith)]
    ring
  have hn : 0 ≤ (1+lam)*(lightOmega lam x)^2-1 := by
    rw [hi]
    exact div_nonneg (mul_nonneg hl.le (add_nonneg (by linarith)
      (mul_nonneg hl.le (sq_nonneg _)))) (by linarith)
  linarith

theorem light_two_thirds_numerator {lam x : ℝ} (hl : 0 < lam) (hl7 : lam ≤ 7/3)
    (hx : 2/3 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ 1-(1+lam)*(lightOmega lam x)^2 := by
  have hq : 0 < actQ lam := div_pos hl (by linarith)
  have ho := (light_chart_bounds hl (by linarith) hx1).1
  have he : lightOmega lam x ≤ lightOmega lam (2/3) := by unfold lightOmega; nlinarith
  have hp := mul_le_mul_of_nonneg_left ((sq_le_sq₀ ho.le (ho.le.trans he)).mpr he)
    (show 0 ≤ 1+lam by linarith)
  have hi : (1+lam)*(lightOmega lam (2/3))^2-1 = lam*(lam-3)/(9*(1+lam)) := by
    unfold lightOmega actQ
    field_simp [ne_of_gt (show 0 < 1+lam by linarith)]
    ring
  have hn : (1+lam)*(lightOmega lam (2/3))^2-1 ≤ 0 := by
    rw [hi]
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hl.le (by linarith))
      (by positivity)
  linarith

theorem light_phase_one_dominant {lam x rho : ℝ} (hl : 0 < lam)
    (hx : 0 ≤ x) (hxh : x ≤ 1/2)
    (hr : rho ≤ rhoStar lam (chartParent lam (lightOmega lam x))) :
    (1-chartParent lam (lightOmega lam x)*rho)*
      O2.cavH lam (chartParent lam (lightOmega lam x)) ≤ 1-rho := by
  have hb := light_chart_bounds hl hx (by linarith)
  have hp := chartParent_bounds hl hb.1 hb.2.1
  have hq : actQ lam < 1 := (div_lt_one (by linarith : 0 < 1+lam)).2 (by linarith)
  have hcap : O2.cavH lam (chartParent lam (lightOmega lam x)) = 1-lightOmega lam x := by
    rw [hb.2.2.2.2]
    unfold lightOmega
    ring
  rw [hcap]
  have hg := light_gap_increasing
    (show chartParent lam (lightOmega lam x)*(1-lightOmega lam x) ≤ 1 by
      nlinarith [hb.1,hb.2.1,hp.1,hp.2.2]) hr
  rw [light_gap_at_switch hl hb.1] at hg
  have hn := div_nonpos_of_nonpos_of_nonneg (light_half_numerator hl hx hxh)
    (mul_nonneg (by linarith : 0 ≤ 1+2*lam) hb.1.le)
  linarith

theorem light_phase_two_dominant {lam x rho : ℝ} (hl : 0 < lam) (hl7 : lam ≤ 7/3)
    (hx : 2/3 ≤ x) (hx1 : x ≤ 1)
    (hr : rhoStar lam (chartParent lam (lightOmega lam x)) ≤ rho) :
    1-rho ≤ (1-chartParent lam (lightOmega lam x)*rho)*
      O2.cavH lam (chartParent lam (lightOmega lam x)) := by
  have hb := light_chart_bounds hl (by linarith) hx1
  have hp := chartParent_bounds hl hb.1 hb.2.1
  have hcap : O2.cavH lam (chartParent lam (lightOmega lam x)) = 1-lightOmega lam x := by
    rw [hb.2.2.2.2]
    unfold lightOmega
    ring
  rw [hcap]
  have hg := light_gap_increasing
    (show chartParent lam (lightOmega lam x)*(1-lightOmega lam x) ≤ 1 by
      nlinarith [hb.1,hb.2.1,hp.1,hp.2.2]) hr
  rw [light_gap_at_switch hl hb.1] at hg
  have hn := div_nonneg (light_two_thirds_numerator hl hl7 hx hx1)
    (mul_nonneg (by linarith : 0 ≤ 1+2*lam) hb.1.le)
  linarith

theorem light_phase_one_source {lam x rho : ℝ} (hl : 0 < lam)
    (hx : 0 ≤ x) (hxh : x ≤ 1/2)
    (hr0 : rhoMin lam (chartParent lam (lightOmega lam x)) ≤ rho) (hr1 : rho ≤ 1)
    (hphase : rho ≤ rhoStar lam (chartParent lam (lightOmega lam x))) :
    let p := chartParent lam (lightOmega lam x)
    let q := actQ lam
    let f := sourceSlopeA q*(p*rho)
    O2.src lam p rho = min ((1+f-sourceSlopeA q*(1-rho))/2)
      ((1+f-sourceSlopeB q*(1-rho)-sourceIntercept q)/2) := by
  dsimp only
  have hb := light_chart_bounds hl hx (by linarith)
  have hp := chartParent_bounds hl hb.1 hb.2.1
  have hm := light_phase_one_dominant hl hx hxh hphase
  rw [source_eq_second hl hp.1 hp.2.1 hr0 hr1, O2.mUp,max_eq_left hm,
    source_phase_one_branch hl hp.1 hphase,fq_branches]
  rcases le_total (sourceSlopeA (actQ lam)*(1-rho))
      (sourceSlopeB (actQ lam)*(1-rho)+sourceIntercept (actQ lam)) with h | h
  · rw [max_eq_right h,min_eq_right (by linarith)]
    ring
  · rw [max_eq_left h,min_eq_left (by linarith)]

theorem light_phase_two_source {lam x rho : ℝ} (hl : 0 < lam) (hl7 : lam ≤ 7/3)
    (hx : 2/3 ≤ x) (hx1 : x ≤ 1)
    (hr0 : rhoMin lam (chartParent lam (lightOmega lam x)) ≤ rho) (hr1 : rho ≤ 1)
    (hphase : rhoStar lam (chartParent lam (lightOmega lam x)) ≤ rho) :
    let p := chartParent lam (lightOmega lam x)
    let q := actQ lam
    let f := sourceSlopeB q*(p*rho)+sourceIntercept q
    O2.src lam p rho = (1+f-sourceSlopeA q*((1-p*rho)*O2.cavH lam p))/2 := by
  dsimp only
  have hb := light_chart_bounds hl (by linarith) hx1
  have hp := chartParent_bounds hl hb.1 hb.2.1
  have hm := light_phase_two_dominant hl hl7 hx hx1 hphase
  have hq : 0 < actQ lam := div_pos hl (by linarith)
  have hq1 : actQ lam < 1 := (div_lt_one (by linarith : 0 < 1+lam)).2 (by linarith)
  have hs := sourceSwitch_mul hq
  have he := source_physical_edges hl hp.1 hp.2.1 hr0 hr1
  have hpi := (div_le_iff₀ hp.1).mp hphase
  have hm2 : (1-chartParent lam (lightOmega lam x)*rho)*
      O2.cavH lam (chartParent lam (lightOmega lam x)) ≤ sourceSwitch (actQ lam) := by
    nlinarith [he.2.2.1]
  rw [source_eq_second hl hp.1 hp.2.1 hr0 hr1,O2.mUp,max_eq_right hm,
    source_phase_two_branch hl hp.1 hphase,fq_lower_branch hq hq1 hm2]

end Erdos993Lean.Analytic.V213.VarianceResponse

#check Erdos993Lean.Analytic.V213.VarianceResponse.source_phase_one_branch
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.source_phase_one_branch
#check Erdos993Lean.Analytic.V213.VarianceResponse.source_phase_two_branch
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.source_phase_two_branch
#check Erdos993Lean.Analytic.V213.VarianceResponse.heavy_source
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.heavy_source
#check Erdos993Lean.Analytic.V213.VarianceResponse.source_phase_two_faces
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.source_phase_two_faces
#check Erdos993Lean.Analytic.V213.VarianceResponse.light_gap_at_switch
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.light_gap_at_switch
#check Erdos993Lean.Analytic.V213.VarianceResponse.light_gap_increasing
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.light_gap_increasing
#check Erdos993Lean.Analytic.V213.VarianceResponse.light_half_numerator
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.light_half_numerator
#check Erdos993Lean.Analytic.V213.VarianceResponse.light_two_thirds_numerator
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.light_two_thirds_numerator
#check Erdos993Lean.Analytic.V213.VarianceResponse.light_phase_one_dominant
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.light_phase_one_dominant
#check Erdos993Lean.Analytic.V213.VarianceResponse.light_phase_two_dominant
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.light_phase_two_dominant
#check Erdos993Lean.Analytic.V213.VarianceResponse.light_phase_one_source
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.light_phase_one_source
#check Erdos993Lean.Analytic.V213.VarianceResponse.light_phase_two_source
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.light_phase_two_source
