module

public import Erdos993Lean.Analytic.V213.ResponseSourcePhaseGeometry

/-! The three actual source values in printed Lemma 5.27. All statements
include H=0. They concern O2.src, not a substituted affine-source surrogate. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight

private theorem switch_identity {q : ℝ} (hq : 0 < q) :
    sourceSwitch q*(1+q)=q := by
  unfold sourceSwitch
  exact div_mul_cancel₀ _ (by positivity)

theorem source_at_rhoMin {lam H : ℝ} (hl : 0 < lam) (hH : 0 ≤ H)
    (hcap : H ≤ childQ lam/2) :
    O2.src lam (halfParent lam H) (rhoMin lam (halfParent lam H)) =
      sourceSlopeA (childQ lam)*halfParent lam H*rhoMin lam (halfParent lam H) := by
  have hp := halfParent_bounds hl hH hcap
  have hr := phase_split_bounds hl hH hcap
  have hq : 0 < actQ lam := div_pos hl (by linarith)
  have hq1 : actQ lam < 1 := (div_lt_one (by linarith : 0<1+lam)).2 (by linarith)
  have hs := switch_identity hq
  have hpi : halfParent lam H*rhoMin lam (halfParent lam H) ≤ sourceSwitch (actQ lam) := by
    have hh := (le_div_iff₀ hp.2.1).mp hr.2.1
    change rhoMin lam (halfParent lam H)*halfParent lam H ≤ sourceSwitch (actQ lam) at hh
    nlinarith
  have hid := rhoMin_q_identity hl hp.2.2.1
  have hm : 1-rhoMin lam (halfParent lam H) =
      actQ lam*(1-halfParent lam H*rhoMin lam (halfParent lam H)) := by nlinarith
  have hmstar : sourceSwitch (actQ lam) ≤ 1-rhoMin lam (halfParent lam H) := by
    rw [hm]
    nlinarith [mul_le_mul_of_nonneg_left hpi hq.le]
  rw [source_eq_second hl hp.2.1 hp.2.2.2 le_rfl (hr.2.1.trans hr.2.2.le),
    half_phase_one_mUp hl hH hcap hr.2.1,
    fq_lower_branch hq hq1 hpi,fq_upper_branch hq hq1 hmstar,hm]
  change (1+sourceSlopeA (actQ lam)*
      (halfParent lam H*rhoMin lam (halfParent lam H))-
      (sourceSlopeB (actQ lam)*(actQ lam*(1-halfParent lam H*rhoMin lam (halfParent lam H)))+
        sourceIntercept (actQ lam)))/2 =
      sourceSlopeA (actQ lam)*halfParent lam H*rhoMin lam (halfParent lam H)
  unfold sourceSlopeA sourceSlopeB sourceIntercept
  field_simp [hq.ne']
  ring

theorem source_at_rhoStar {lam H : ℝ} (hl : 0 < lam) (hH : 0 ≤ H)
    (hcap : H ≤ childQ lam/2) :
    O2.src lam (halfParent lam H) (rhoStar lam (halfParent lam H)) =
      (lam-1)/(4*lam)+1/(4*halfParent lam H) := by
  have hp := halfParent_bounds hl hH hcap
  have hr := phase_split_bounds hl hH hcap
  have hq : 0 < actQ lam := div_pos hl (by linarith)
  have hq1 : actQ lam < 1 := (div_lt_one (by linarith : 0<1+lam)).2 (by linarith)
  have hs := switch_identity hq
  have hpi : halfParent lam H*rhoStar lam (halfParent lam H)=sourceSwitch (actQ lam) := by
    unfold rhoStar
    field_simp [hp.2.1.ne']
  have he := (source_physical_edges hl hp.2.1 hp.2.2.2 hr.2.1 hr.2.2.le).1
  have hm : 1-rhoStar lam (halfParent lam H) ≤ sourceSwitch (actQ lam) := by
    rw [hpi] at he
    nlinarith
  rw [source_eq_second hl hp.2.1 hp.2.2.2 hr.2.1 hr.2.2.le,
    half_phase_one_mUp hl hH hcap le_rfl,
    source_phase_one_branch hl hp.2.1 le_rfl,fq_lower_branch hq hq1 hm]
  unfold rhoStar
  rw [sourceSwitch_activity hl]
  unfold sourceSlopeA actQ
  field_simp [hl.ne',hp.2.1.ne',show 1+lam≠0 by positivity,
    show 1+2*lam≠0 by positivity]
  ring

theorem source_at_one {lam H : ℝ} (hl : 0 < lam) (hH : 0 ≤ H)
    (hcap : H ≤ childQ lam/2) :
    O2.src lam (halfParent lam H) 1 =
      sourceSlopeB (childQ lam)*halfParent lam H+sourceIntercept (childQ lam) := by
  have hp := halfParent_bounds hl hH hcap
  have hr := phase_split_bounds hl hH hcap
  have hq : 0 < actQ lam := div_pos hl (by linarith)
  have hq1 : actQ lam < 1 := (div_lt_one (by linarith : 0<1+lam)).2 (by linarith)
  have hs := switch_identity hq
  have hpi : sourceSwitch (actQ lam) ≤ halfParent lam H := by
    have hh := (div_le_one hp.2.1).mp hr.2.2.le
    exact hh
  have he := (source_physical_edges hl hp.2.1 hp.2.2.2
    (hr.2.1.trans hr.2.2.le) le_rfl).2.2.1
  rw [halfParent_cavH hl hH hcap] at he
  simp only [mul_one] at he
  have hm : (1-halfParent lam H)*H ≤ sourceSwitch (actQ lam) := by nlinarith
  have hup : O2.mUp lam (halfParent lam H) 1=(1-halfParent lam H)*H := by
    unfold O2.mUp
    rw [halfParent_cavH hl hH hcap]
    simp only [mul_one,sub_self]
    exact max_eq_right (mul_nonneg (by linarith [hp.2.2.1]) hH)
  have hHm : 0 < 1-H := by linarith [hp.1]
  have hid : (1-halfParent lam H)*H=1-halfParent lam H-halfParent lam H/lam := by
    unfold halfParent chartParent
    field_simp [hl.ne',show 1+lam*(1-H)≠0 by positivity] <;> ring
  rw [source_eq_second hl hp.2.1 hp.2.2.2 (hr.2.1.trans hr.2.2.le) le_rfl,
    hup,source_phase_two_branch hl hp.2.1 hr.2.2.le,fq_lower_branch hq hq1 hm,hid]
  simp only [mul_one]
  unfold sourceSlopeA sourceSlopeB sourceIntercept childQ actQ
  field_simp [hl.ne',show 1+lam≠0 by positivity]
  ring

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.source_at_rhoMin
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.source_at_rhoMin
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.source_at_rhoStar
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.source_at_rhoStar
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.source_at_one
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.source_at_one
