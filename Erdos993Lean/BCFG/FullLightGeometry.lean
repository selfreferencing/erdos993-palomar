module

public import Erdos993Lean.BCFG.ChartDefinitions
public import Erdos993Lean.Analytic.V213.ResponseChartSelection

/-! Full light geometry for printed Lemma 5.16. No half-light restriction. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Erdos993Lean.BCFG.Analytic

open Erdos993Lean.Analytic Erdos993Lean.Analytic.V213.VarianceResponse

def lightRhoStar (lam omega : ℝ) : ℝ := (lam/(1+2*lam))/occupation lam omega

def lightGh (lam omega rho : ℝ) : ℝ :=
  (1+O2.fq (actQ lam) (occupation lam omega*rho)-
    O2.fq (actQ lam) (O2.mUp lam (occupation lam omega) rho))/2

theorem fullLight_omega_pos {lam omega : ℝ} (hl : 0 < lam)
    (hlo : 1/(1+lam) ≤ omega) : 0 < omega :=
  (one_div_pos.mpr (show 0 < 1+lam by linarith)).trans_le hlo

theorem fullLight_parent_bounds {lam omega : ℝ} (hl : 0 < lam)
    (hlo : 1/(1+lam) ≤ omega) (hhi : omega ≤ 1) :
    0 < occupation lam omega ∧ occupation lam omega ≤ actQ lam ∧
      occupation lam omega < 1 :=
  chartParent_bounds hl (fullLight_omega_pos hl hlo) hhi

theorem fullLight_parent_ge_switch {lam omega : ℝ} (hl : 0 < lam)
    (hlo : 1/(1+lam) ≤ omega) :
    sourceSwitch (actQ lam) ≤ occupation lam omega := by
  have hw := fullLight_omega_pos hl hlo
  have hb := (div_le_iff₀ (show 0 < 1+lam by linarith)).mp hlo
  rw [sourceSwitch_activity hl]
  unfold occupation
  apply (div_le_div_iff₀ (by linarith : 0 < 1+2*lam) (by positivity)).2
  nlinarith

theorem fullLight_cavity {lam omega : ℝ} (hl : 0 < lam)
    (hlo : 1/(1+lam) ≤ omega) :
    O2.cavH lam (occupation lam omega) = 1-omega := by
  have hw := fullLight_omega_pos hl hlo
  have hid : 1-actQ lam = 1/(1+lam) := by
    unfold actQ
    field_simp [ne_of_gt (show 0 < 1+lam by linarith)] <;> ring
  have hc : 1-omega ≤ actQ lam := by rw [← hid] at hlo; linarith
  change O2.cavH lam (chartParent lam omega) = _
  rw [chart_cavity_cap hl hw, min_eq_right hc]

theorem fullLight_rhoZero_eq {lam omega : ℝ} (hl : 0 < lam)
    (hlo : 1/(1+lam) ≤ omega) (hhi : omega ≤ 1) :
    rhoZero lam omega = rhoMin lam (occupation lam omega) := by
  have hw := fullLight_omega_pos hl hlo
  have hp := fullLight_parent_bounds hl hlo hhi
  have hm : 0 < 1-occupation lam omega := sub_pos.mpr hp.2.2
  have hd : 1+lam*omega ≠ 0 := by positivity
  have he : 1+lam+lam*omega ≠ 0 := by positivity
  have hf : 1+lam*(1-occupation lam omega) ≠ 0 := by positivity
  unfold rhoMin
  apply (eq_div_iff hf).2
  unfold rhoZero occupation
  field_simp [hd,he] <;> ring

theorem fullLight_rhoStar_eq {lam omega : ℝ} (hl : 0 < lam) :
    lightRhoStar lam omega = rhoStar lam (occupation lam omega) := by
  unfold lightRhoStar rhoStar
  rw [sourceSwitch_activity hl]

theorem fullLight_phase_bounds {lam omega : ℝ} (hl : 0 < lam)
    (hlo : 1/(1+lam) ≤ omega) (hhi : omega ≤ 1) :
    rhoZero lam omega ≤ lightRhoStar lam omega ∧ lightRhoStar lam omega ≤ 1 := by
  have hp := fullLight_parent_bounds hl hlo hhi
  rw [fullLight_rhoZero_eq hl hlo hhi, fullLight_rhoStar_eq hl]
  exact rhoStar_bounds hl hp.1 (fullLight_parent_ge_switch hl hlo) hp.2.1

theorem fullLight_coefficients {lam : ℝ} (hl : 0 < lam) :
    sourceSlopeA (actQ lam) = sourceA lam ∧
    sourceSlopeB (actQ lam) = sourceA lam/q lam ∧
    sourceIntercept (actQ lam) = -1/(2*lam) := by
  have h1 : 1+lam ≠ 0 := by positivity
  have hq : actQ lam ≠ 0 := ne_of_gt (div_pos hl (by linarith))
  unfold sourceSlopeA sourceSlopeB sourceIntercept sourceA q actQ at *
  constructor
  · field_simp [hl.ne',h1] <;> ring
  constructor <;> field_simp [hl.ne',h1] <;> ring

theorem fullLight_AB_bounds {lam omega : ℝ} (hl : 0 < lam)
    (hlo : 1/(1+lam) ≤ omega) (hhi : omega ≤ 1) :
    0 ≤ (1-omega)/omega ∧ (1-omega)/omega ≤ lam ∧
      0 ≤ (1+lam)*omega-1 ∧ (1+lam)*omega-1 ≤ lam := by
  have hw := fullLight_omega_pos hl hlo
  have hb := (div_le_iff₀ (show 0 < 1+lam by linarith)).mp hlo
  refine ⟨div_nonneg (sub_nonneg.mpr hhi) hw.le,?_,by nlinarith,?_⟩
  · apply (div_le_iff₀ hw).2
    nlinarith
  · nlinarith [mul_le_mul_of_nonneg_left hhi (show 0 ≤ 1+lam by linarith)]

theorem fullLight_source_eq_Gh {lam omega rho : ℝ} (hl : 0 < lam)
    (hlo : 1/(1+lam) ≤ omega) (hhi : omega ≤ 1)
    (hr : rhoZero lam omega ≤ rho) (hr1 : rho ≤ 1) :
    O2.src lam (occupation lam omega) rho = lightGh lam omega rho := by
  have hp := fullLight_parent_bounds hl hlo hhi
  rw [fullLight_rhoZero_eq hl hlo hhi] at hr
  exact source_eq_second hl hp.1 hp.2.1 hr hr1

end Erdos993Lean.BCFG.Analytic

#check Erdos993Lean.BCFG.Analytic.lightRhoStar
#print axioms Erdos993Lean.BCFG.Analytic.lightRhoStar
#check Erdos993Lean.BCFG.Analytic.lightGh
#print axioms Erdos993Lean.BCFG.Analytic.lightGh
#check Erdos993Lean.BCFG.Analytic.fullLight_omega_pos
#print axioms Erdos993Lean.BCFG.Analytic.fullLight_omega_pos
#check Erdos993Lean.BCFG.Analytic.fullLight_parent_bounds
#print axioms Erdos993Lean.BCFG.Analytic.fullLight_parent_bounds
#check Erdos993Lean.BCFG.Analytic.fullLight_parent_ge_switch
#print axioms Erdos993Lean.BCFG.Analytic.fullLight_parent_ge_switch
#check Erdos993Lean.BCFG.Analytic.fullLight_cavity
#print axioms Erdos993Lean.BCFG.Analytic.fullLight_cavity
#check Erdos993Lean.BCFG.Analytic.fullLight_rhoZero_eq
#print axioms Erdos993Lean.BCFG.Analytic.fullLight_rhoZero_eq
#check Erdos993Lean.BCFG.Analytic.fullLight_rhoStar_eq
#print axioms Erdos993Lean.BCFG.Analytic.fullLight_rhoStar_eq
#check Erdos993Lean.BCFG.Analytic.fullLight_phase_bounds
#print axioms Erdos993Lean.BCFG.Analytic.fullLight_phase_bounds
#check Erdos993Lean.BCFG.Analytic.fullLight_coefficients
#print axioms Erdos993Lean.BCFG.Analytic.fullLight_coefficients
#check Erdos993Lean.BCFG.Analytic.fullLight_AB_bounds
#print axioms Erdos993Lean.BCFG.Analytic.fullLight_AB_bounds
#check Erdos993Lean.BCFG.Analytic.fullLight_source_eq_Gh
#print axioms Erdos993Lean.BCFG.Analytic.fullLight_source_eq_Gh
