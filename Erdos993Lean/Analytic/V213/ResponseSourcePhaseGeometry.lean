module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightGeometry
public import Erdos993Lean.Analytic.V213.ResponseHalfLightQuadraticDefs
public import Erdos993Lean.Analytic.V213.ResponseChartSelection

/-! Actual vacancy phases on the half-light parent region, including H=0. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight

theorem halfParent_cavH {lam H : ℝ} (hl : 0 < lam) (hH : 0 ≤ H)
    (hcap : H ≤ childQ lam/2) : O2.cavH lam (halfParent lam H)=H := by
  have hp := halfParent_bounds hl hH hcap
  have hq0 : 0 < childQ lam := div_pos hl (by linarith)
  have hHm : 0 < 1-H := by linarith [hp.1]
  have hpc : 0 < 1-halfParent lam H := sub_pos.mpr hp.2.2.1
  have hden : 0 < 1+lam*(1-H) := by positivity
  have hi : halfParent lam H/(lam*(1-halfParent lam H))=1-H := by
    apply (div_eq_iff (mul_ne_zero hl.ne' hpc.ne')).2
    unfold halfParent chartParent
    field_simp [hden.ne'] <;> ring
  unfold O2.cavH
  rw [hi]
  have hq : H ≤ actQ lam := by change H ≤ childQ lam; linarith
  simpa using min_eq_right hq

theorem phase_split_bounds {lam H : ℝ} (hl : 0 < lam) (hH : 0 ≤ H)
    (hcap : H ≤ childQ lam/2) :
    0 < rhoMin lam (halfParent lam H) ∧
    rhoMin lam (halfParent lam H) ≤ rhoStar lam (halfParent lam H) ∧
    rhoStar lam (halfParent lam H) < 1 := by
  have hp := halfParent_bounds hl hH hcap
  have hpc : 0 < 1-halfParent lam H := sub_pos.mpr hp.2.2.1
  have hd : 0 < 1+lam*(1-halfParent lam H) := by positivity
  have hq : halfParent lam H*(1+lam) ≤ lam :=
    (le_div_iff₀ (show 0<1+lam by linarith)).mp hp.2.2.2
  have hpstar : sourceSwitch (actQ lam) < pStar lam := by
    rw [sourceSwitch_activity hl]
    unfold pStar
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
    have hpos : 0 < lam^2*(lam+1) := by positivity
    nlinarith
  have hs : sourceSwitch (actQ lam) < halfParent lam H :=
    hpstar.trans_le (pStar_le_halfParent hl hH hcap)
  refine ⟨one_div_pos.mpr hd,?_,(div_lt_one hp.2.1).2 hs⟩
  unfold rhoMin rhoStar
  rw [sourceSwitch_activity hl]
  apply (div_le_div_iff₀ hd hp.2.1).2
  have hn := mul_nonneg (show 0≤1+lam by linarith)
    (show 0≤lam-halfParent lam H*(1+lam) by linarith)
  have hh : halfParent lam H ≤ lam*(1+lam*(1-halfParent lam H))/(1+2*lam) := by
    apply (le_div_iff₀ (show 0<1+2*lam by linarith)).2
    nlinarith
  simpa only [one_mul,div_mul_eq_mul_div] using hh

theorem phase_feasible {phase : ℕ} {lam H rho : ℝ} (hl : 0 < lam)
    (hH : 0 ≤ H) (hcap : H ≤ childQ lam/2) (hphase : phaseDomain phase lam H rho) :
    rhoMin lam (halfParent lam H) ≤ rho ∧ rho ≤ 1 := by
  have hb := phase_split_bounds hl hH hcap
  rcases hphase with h | h
  · exact ⟨h.2.1,h.2.2.trans hb.2.2.le⟩
  · exact ⟨hb.2.1.trans h.2.1,h.2.2⟩

theorem half_phase_one_mUp {lam H rho : ℝ} (hl : 0 < lam)
    (hH : 0 ≤ H) (hcap : H ≤ childQ lam/2)
    (hrho : rho ≤ rhoStar lam (halfParent lam H)) :
    O2.mUp lam (halfParent lam H) rho = 1-rho := by
  have hq : 0 < childQ lam := div_pos hl (by linarith)
  have hx : 0 ≤ H/childQ lam := div_nonneg hH hq.le
  have hxh : H/childQ lam ≤ 1/2 := (div_le_iff₀ hq).2 (by linarith)
  have ho : lightOmega lam (H/childQ lam)=1-H := by
    unfold lightOmega childQ actQ
    field_simp [hl.ne',show 1+lam≠0 by positivity] <;> ring
  have hp : chartParent lam (lightOmega lam (H/childQ lam))=halfParent lam H := by rw [ho]; rfl
  have h := light_phase_one_dominant hl hx hxh (by simpa only [hp] using hrho)
  rw [hp] at h
  exact max_eq_left h

theorem half_phase_one_source {lam H rho : ℝ} (hl : 0 < lam)
    (hH : 0 ≤ H) (hcap : H ≤ childQ lam/2)
    (hr0 : rhoMin lam (halfParent lam H) ≤ rho)
    (hrstar : rho ≤ rhoStar lam (halfParent lam H)) :
    let p := halfParent lam H
    let q := childQ lam
    O2.src lam p rho = min
      ((1+sourceSlopeA q*(p*rho)-sourceSlopeA q*(1-rho))/2)
      ((1+sourceSlopeA q*(p*rho)-sourceSlopeB q*(1-rho)-sourceIntercept q)/2) := by
  have hp := halfParent_bounds hl hH hcap
  have hb := phase_split_bounds hl hH hcap
  have hq : 0 < actQ lam := div_pos hl (by linarith)
  dsimp only
  rw [source_eq_second hl hp.2.1 hp.2.2.2 hr0 (hrstar.trans hb.2.2.le),
    half_phase_one_mUp hl hH hcap hrstar,
    source_phase_one_branch hl hp.2.1 hrstar,fq_branches]
  rcases le_total (sourceSlopeA (actQ lam)*(1-rho))
      (sourceSlopeB (actQ lam)*(1-rho)+sourceIntercept (actQ lam)) with h | h
  · dsimp only [actQ,childQ] at *
    rw [max_eq_right h,min_eq_right (by linarith)] <;> ring
  · dsimp only [actQ,childQ] at *
    rw [max_eq_left h,min_eq_left (by linarith)] <;> ring

theorem half_phase_two_source {lam H rho : ℝ} (hl : 0 < lam)
    (hH : 0 ≤ H) (hcap : H ≤ childQ lam/2)
    (hrstar : rhoStar lam (halfParent lam H) ≤ rho) (hr1 : rho ≤ 1) :
    let p := halfParent lam H
    let q := childQ lam
    let f := sourceSlopeB q*(p*rho)+sourceIntercept q
    O2.src lam p rho = min ((1+f-sourceSlopeA q*(1-rho))/2)
      ((1+f-sourceSlopeA q*((1-p*rho)*H))/2) := by
  have hp := halfParent_bounds hl hH hcap
  have hb := phase_split_bounds hl hH hcap
  have h := source_phase_two_faces hl hp.2.1 hp.2.2.2 (hb.2.1.trans hrstar) hr1 hrstar
  dsimp only at h ⊢
  rw [source_phase_two_branch hl hp.2.1 hrstar,halfParent_cavH hl hH hcap] at h
  exact h

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.halfParent_cavH
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.halfParent_cavH
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.phase_split_bounds
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.phase_split_bounds
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.phase_feasible
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.phase_feasible
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.half_phase_one_mUp
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.half_phase_one_mUp
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.half_phase_one_source
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.half_phase_one_source
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.half_phase_two_source
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.half_phase_two_source
