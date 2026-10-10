module

public import Erdos993Lean.BCFG.FullLightGeometry

/-! The three actual source values on the full closed light region. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Erdos993Lean.BCFG.Analytic

open Erdos993Lean.Analytic Erdos993Lean.Analytic.V213.VarianceResponse

private theorem switch_mul {qv : ℝ} (hq : 0 < qv) :
    sourceSwitch qv*(1+qv) = qv :=
  div_mul_cancel₀ _ (by positivity)

theorem fullLight_source_left {lam omega : ℝ} (hl : 0 < lam)
    (hlo : 1/(1+lam) ≤ omega) (hhi : omega ≤ 1) :
    O2.src lam (occupation lam omega) (rhoZero lam omega) =
      sourceA lam*occupation lam omega*rhoZero lam omega := by
  have hp := fullLight_parent_bounds hl hlo hhi
  have hr := fullLight_phase_bounds hl hlo hhi
  have hq : 0 < actQ lam := div_pos hl (by linarith)
  have hq1 : actQ lam < 1 := (div_lt_one (by linarith : 0 < 1+lam)).2 (by linarith)
  have hs := switch_mul hq
  have hr' : rhoMin lam (occupation lam omega) ≤ rhoStar lam (occupation lam omega) := by
    simpa only [fullLight_rhoZero_eq hl hlo hhi,fullLight_rhoStar_eq hl] using hr.1
  have hpi : occupation lam omega*rhoZero lam omega ≤ sourceSwitch (actQ lam) := by
    have hh := (le_div_iff₀ hp.1).mp hr'
    rw [← fullLight_rhoZero_eq hl hlo hhi] at hh
    nlinarith
  have hid := rhoMin_q_identity hl hp.2.2
  rw [← fullLight_rhoZero_eq hl hlo hhi] at hid
  have hm : 1-rhoZero lam omega = actQ lam*(1-occupation lam omega*rhoZero lam omega) := by
    nlinarith
  have hpr : 0 ≤ 1-occupation lam omega*rhoZero lam omega := by
    have hb := mul_le_mul_of_nonneg_left (hr.1.trans hr.2) hp.1.le
    nlinarith [hp.2.2]
  have hc : O2.cavH lam (occupation lam omega) ≤ actQ lam := min_le_left _ _
  have hm2 : (1-occupation lam omega*rhoZero lam omega)*
      O2.cavH lam (occupation lam omega) ≤ 1-rhoZero lam omega := by
    rw [hm]
    nlinarith [mul_le_mul_of_nonneg_left hc hpr]
  have hmstar : sourceSwitch (actQ lam) ≤ 1-rhoZero lam omega := by
    rw [hm]
    nlinarith [mul_le_mul_of_nonneg_left hpi hq.le]
  have hr0 : rhoMin lam (occupation lam omega) ≤ rhoZero lam omega :=
    (fullLight_rhoZero_eq hl hlo hhi).symm.le
  rw [source_eq_second hl hp.1 hp.2.1 hr0 (hr.1.trans hr.2),O2.mUp,
    max_eq_left hm2,fq_lower_branch hq hq1 hpi,fq_upper_branch hq hq1 hmstar,hm,
    ← (fullLight_coefficients hl).1]
  unfold sourceSlopeA sourceSlopeB sourceIntercept
  field_simp [hq.ne'] <;> ring

theorem fullLight_source_right {lam omega : ℝ} (hl : 0 < lam)
    (hlo : 1/(1+lam) ≤ omega) (hhi : omega ≤ 1) :
    O2.src lam (occupation lam omega) 1 =
      sourceA lam/q lam*occupation lam omega-1/(2*lam) := by
  have hw := fullLight_omega_pos hl hlo
  have hp := fullLight_parent_bounds hl hlo hhi
  have hr := fullLight_phase_bounds hl hlo hhi
  have hq : 0 < actQ lam := div_pos hl (by linarith)
  have hq1 : actQ lam < 1 := (div_lt_one (by linarith : 0 < 1+lam)).2 (by linarith)
  have hs := switch_mul hq
  have hpi := fullLight_parent_ge_switch hl hlo
  have hr0 : rhoMin lam (occupation lam omega) ≤ 1 := by
    rw [← fullLight_rhoZero_eq hl hlo hhi]
    exact hr.1.trans hr.2
  have he := (source_physical_edges hl hp.1 hp.2.1 hr0 le_rfl).2.2.1
  rw [fullLight_cavity hl hlo] at he
  simp only [mul_one] at he
  have hm : (1-occupation lam omega)*(1-omega) ≤ sourceSwitch (actQ lam) := by
    nlinarith
  have hup : O2.mUp lam (occupation lam omega) 1 =
      (1-occupation lam omega)*(1-omega) := by
    rw [O2.mUp,fullLight_cavity hl hlo]
    simp only [mul_one,sub_self]
    exact max_eq_right (mul_nonneg (sub_nonneg.mpr hp.2.2.le) (sub_nonneg.mpr hhi))
  have hid : (1-occupation lam omega)*(1-omega) =
      1-occupation lam omega-occupation lam omega/lam := by
    unfold occupation
    field_simp [hl.ne',show 1+lam*omega ≠ 0 by positivity] <;> ring
  rw [source_eq_second hl hp.1 hp.2.1 hr0 le_rfl,hup,
    show occupation lam omega*1 = occupation lam omega by ring,
    fq_upper_branch hq hq1 hpi,fq_lower_branch hq hq1 hm,hid]
  unfold sourceSlopeA sourceSlopeB sourceIntercept sourceA q actQ
  field_simp [hl.ne',show 1+lam ≠ 0 by positivity] <;> ring

theorem fullLight_source_middle {lam omega : ℝ} (hl : 0 < lam)
    (hlo : 1/(1+lam) ≤ omega) (hhi : omega ≤ 1) :
    O2.src lam (occupation lam omega) (lightRhoStar lam omega) =
      1/2+min ((1-omega)/omega) ((1+lam)*omega-1)/(4*lam) := by
  have hw := fullLight_omega_pos hl hlo
  have hp := fullLight_parent_bounds hl hlo hhi
  have hr := fullLight_phase_bounds hl hlo hhi
  have hr0 : rhoMin lam (occupation lam omega) ≤ lightRhoStar lam omega := by
    rw [← fullLight_rhoZero_eq hl hlo hhi]
    exact hr.1
  have hstar : rhoStar lam (occupation lam omega) ≤ lightRhoStar lam omega :=
    (fullLight_rhoStar_eq hl).symm.le
  have hbranch := source_phase_one_branch hl hp.1 (fullLight_rhoStar_eq hl).le
  rw [source_phase_two_faces hl hp.1 hp.2.1 hr0 hr.2 hstar]
  rw [hbranch,fullLight_cavity hl hlo,(fullLight_coefficients hl).1]
  have hleft :
      (1+sourceA lam*(occupation lam omega*lightRhoStar lam omega)-
        sourceA lam*(1-lightRhoStar lam omega))/2 = 1/2+((1-omega)/omega)/(4*lam) := by
    unfold sourceA lightRhoStar occupation
    field_simp [hl.ne',hw.ne',show 1+lam*omega ≠ 0 by positivity,
      show 1+2*lam ≠ 0 by positivity] <;> ring
  have hright :
      (1+sourceA lam*(occupation lam omega*lightRhoStar lam omega)-
        sourceA lam*((1-occupation lam omega*lightRhoStar lam omega)*(1-omega)))/2 =
      1/2+((1+lam)*omega-1)/(4*lam) := by
    unfold sourceA lightRhoStar occupation
    field_simp [hl.ne',hw.ne',show 1+lam*omega ≠ 0 by positivity,
      show 1+2*lam ≠ 0 by positivity] <;> ring
  rw [hleft,hright]
  rcases le_total ((1-omega)/omega) ((1+lam)*omega-1) with h | h
  · rw [min_eq_left h,min_eq_left (by
      exact add_le_add le_rfl (div_le_div_of_nonneg_right h (by positivity)))]
  · rw [min_eq_right h,min_eq_right (by
      exact add_le_add le_rfl (div_le_div_of_nonneg_right h (by positivity)))]

theorem fullLight_Gh_endpoints {lam omega : ℝ} (hl : 0 < lam)
    (hlo : 1/(1+lam) ≤ omega) (hhi : omega ≤ 1) :
    lightGh lam omega (rhoZero lam omega) = sourceA lam*occupation lam omega*rhoZero lam omega ∧
    lightGh lam omega (lightRhoStar lam omega) =
      1/2+min ((1-omega)/omega) ((1+lam)*omega-1)/(4*lam) ∧
    lightGh lam omega 1 = sourceA lam/q lam*occupation lam omega-1/(2*lam) := by
  have hr := fullLight_phase_bounds hl hlo hhi
  rw [← fullLight_source_eq_Gh hl hlo hhi le_rfl (hr.1.trans hr.2),
    ← fullLight_source_eq_Gh hl hlo hhi hr.1 hr.2,
    ← fullLight_source_eq_Gh hl hlo hhi (hr.1.trans hr.2) le_rfl]
  exact ⟨fullLight_source_left hl hlo hhi,fullLight_source_middle hl hlo hhi,
    fullLight_source_right hl hlo hhi⟩

end Erdos993Lean.BCFG.Analytic

#check Erdos993Lean.BCFG.Analytic.fullLight_source_left
#print axioms Erdos993Lean.BCFG.Analytic.fullLight_source_left
#check Erdos993Lean.BCFG.Analytic.fullLight_source_right
#print axioms Erdos993Lean.BCFG.Analytic.fullLight_source_right
#check Erdos993Lean.BCFG.Analytic.fullLight_source_middle
#print axioms Erdos993Lean.BCFG.Analytic.fullLight_source_middle
#check Erdos993Lean.BCFG.Analytic.fullLight_Gh_endpoints
#print axioms Erdos993Lean.BCFG.Analytic.fullLight_Gh_endpoints
