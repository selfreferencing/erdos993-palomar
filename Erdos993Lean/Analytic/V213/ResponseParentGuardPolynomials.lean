module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightDefs
public import Erdos993Lean.Analytic.V213.ResponseParentPolynomialSigns

/-! Literal rational identities and the printed finite parent-guard signs.
No field inequality or parent theorem is taken as an assumption. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows

noncomputable def guardValue (lam «GL» gammaL AU : ℝ) : ℝ :=
  2*«GL»*aStar lam-AU+(lam+2)/((1+lam)*(1+2*lam))+2*gammaL/(1+lam)
noncomputable def parentDUpperC (lam : ℝ) : ℝ :=
  pStar lam*(108/125+8*lam/25-(2+lam/5)*pStar lam)

theorem aStar_of_le_one {lam : ℝ} (hl : lam ≤ 1) :
    aStar lam=(1+lam)/lam := by simp [aStar,hl]

theorem aStar_of_one_le {lam : ℝ} (hl : 1 ≤ lam) :
    aStar lam=2*(lam^2+4*lam+2)/(lam*(3*lam+4)) := by
  by_cases he : lam ≤ 1
  · have h : lam=1 := le_antisymm he hl
    subst lam
    norm_num [aStar]
  · simp [aStar,he]

theorem parentDUpperC_identity {lam : ℝ} (hl : 0 < lam) :
    1/8-parentDUpperC lam = parentQ lam/(1000*(lam^2+4*lam+2)^2) := by
  have hd : 0 < lam^2+4*lam+2 := by positivity
  unfold parentDUpperC pStar parentQ
  field_simp [hd.ne'] <;> ring

theorem parentDUpperC_lt_eighth {lam : ℝ} (hl : 4/5 ≤ lam) (hu : lam ≤ 13/10) :
    parentDUpperC lam < 1/8 := by
  have h := div_pos (parentQ_pos hl hu)
    (show 0 < 1000*(lam^2+4*lam+2)^2 by positivity)
  rw [← parentDUpperC_identity (by linarith)] at h
  linarith

theorem D_minus_guard_identity {lam : ℝ} (hl : 4/5 ≤ lam) (hu : lam ≤ 1) :
    guardValue lam (19*lam/100-7/1000) (lam/5) (lam/10+23/20)-1/8 =
      parentDMinus lam/(1000*lam*(1+lam)*(1+2*lam)) := by
  have hp : 0 < lam := by linarith
  unfold guardValue
  rw [aStar_of_le_one hu]
  unfold parentDMinus
  field_simp [hp.ne',show 1+lam ≠ 0 by positivity,show 1+2*lam ≠ 0 by positivity] <;> ring

theorem D_plus_guard_identity {lam : ℝ} (hl : 1 ≤ lam) (hu : lam ≤ 13/10) :
    guardValue lam (19*lam/100-7/1000) (lam/5) (lam/10+23/20)-1/8 =
      parentDPlus lam/(1000*lam*(1+lam)*(1+2*lam)*(4+3*lam)) := by
  have hp : 0 < lam := by linarith
  unfold guardValue
  rw [aStar_of_one_le hl]
  unfold parentDPlus
  field_simp [hp.ne',show 1+lam ≠ 0 by positivity,show 1+2*lam ≠ 0 by positivity,
    show 3*lam+4 ≠ 0 by positivity] <;> ring

theorem D_guard_gt_eighth {lam : ℝ} (hl : 4/5 ≤ lam) (hu : lam ≤ 13/10) :
    1/8 < guardValue lam (19*lam/100-7/1000) (lam/5) (lam/10+23/20) := by
  have hp : 0 < lam := by linarith
  apply sub_pos.mp
  by_cases he : lam ≤ 1
  · rw [D_minus_guard_identity hl he]
    exact div_pos (parentDMinus_pos hl he) (by positivity)
  · have he' : 1 ≤ lam := by linarith
    rw [D_plus_guard_identity he' hu]
    exact div_pos (parentDPlus_pos he' hu) (by positivity)

theorem E1_guard_identity {lam : ℝ} (hl : 13/10 ≤ lam) (hu : lam ≤ 29/20) :
    guardValue lam ((19*lam-15)/50) ((31*lam-16)/100) (4*lam/3-71/100)-1/8 =
      parentE1 lam/(600*lam*(1+lam)*(1+2*lam)*(4+3*lam)) := by
  have hp : 0 < lam := by linarith
  unfold guardValue
  rw [aStar_of_one_le (by linarith)]
  unfold parentE1
  field_simp [hp.ne',show 1+lam ≠ 0 by positivity,show 1+2*lam ≠ 0 by positivity,
    show 3*lam+4 ≠ 0 by positivity] <;> ring

theorem E1_guard_gt_eighth {lam : ℝ} (hl : 13/10 ≤ lam) (hu : lam ≤ 29/20) :
    1/8 < guardValue lam ((19*lam-15)/50) ((31*lam-16)/100) (4*lam/3-71/100) := by
  have hp : 0 < lam := by linarith
  apply sub_pos.mp
  rw [E1_guard_identity hl hu]
  exact div_pos (parentE1_pos hl hu) (by positivity)

theorem E2_guard_identity {lam : ℝ} (hl : 29/20 ≤ lam) (hu : lam ≤ 8/5) :
    guardValue lam (3*lam/20+1/40) ((21*lam-2)/100) (lam/2+41/100)-1/8 =
      parentE2 lam/(200*lam*(1+lam)*(1+2*lam)*(4+3*lam)) := by
  have hp : 0 < lam := by linarith
  unfold guardValue
  rw [aStar_of_one_le (by linarith)]
  unfold parentE2
  field_simp [hp.ne',show 1+lam ≠ 0 by positivity,show 1+2*lam ≠ 0 by positivity,
    show 3*lam+4 ≠ 0 by positivity] <;> ring

theorem E2_guard_gt_eighth {lam : ℝ} (hl : 29/20 ≤ lam) (hu : lam ≤ 8/5) :
    1/8 < guardValue lam (3*lam/20+1/40) ((21*lam-2)/100) (lam/2+41/100) := by
  have hp : 0 < lam := by linarith
  apply sub_pos.mp
  rw [E2_guard_identity hl hu]
  exact div_pos (parentE2_pos hl hu) (by positivity)

theorem H_guard_identity {lam : ℝ} (hl : 7/4 ≤ lam) (hu : lam ≤ 7/3) :
    guardValue lam (lam/4-1/5) (2/5) (3*lam/4-2/5) =
      parentH lam/(20*lam*(1+lam)*(1+2*lam)*(4+3*lam)) := by
  have hp : 0 < lam := by linarith
  unfold guardValue
  rw [aStar_of_one_le (by linarith)]
  unfold parentH
  field_simp [hp.ne',show 1+lam ≠ 0 by positivity,show 1+2*lam ≠ 0 by positivity,
    show 3*lam+4 ≠ 0 by positivity] <;> ring

theorem H_guard_pos {lam : ℝ} (hl : 7/4 ≤ lam) (hu : lam ≤ 7/3) :
    0 < guardValue lam (lam/4-1/5) (2/5) (3*lam/4-2/5) := by
  have hp : 0 < lam := by linarith
  rw [H_guard_identity hl hu]
  exact div_pos (parentH_pos hl hu) (by positivity)

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.guardValue
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.guardValue
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentDUpperC
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentDUpperC
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.aStar_of_le_one
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.aStar_of_le_one
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.aStar_of_one_le
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.aStar_of_one_le
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentDUpperC_identity
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentDUpperC_identity
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentDUpperC_lt_eighth
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentDUpperC_lt_eighth
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.D_minus_guard_identity
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.D_minus_guard_identity
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.D_plus_guard_identity
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.D_plus_guard_identity
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.D_guard_gt_eighth
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.D_guard_gt_eighth
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E1_guard_identity
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E1_guard_identity
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E1_guard_gt_eighth
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E1_guard_gt_eighth
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E2_guard_identity
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E2_guard_identity
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E2_guard_gt_eighth
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.E2_guard_gt_eighth
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.H_guard_identity
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.H_guard_identity
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.H_guard_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.H_guard_pos
