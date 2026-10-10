module

public import Erdos993Lean.Analytic.V213.ResponseParentCoefficientBounds
public import Erdos993Lean.Analytic.V213.ResponseParentCurvatureBounds

/-! The actual positive parent slope r=c+2dh. The common analytic lower bound
is proved before the four exact rational guard consumers are applied. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows

open FreeCountVariance.Envelopes

theorem row_activity_bounds {i : Fin 4} {lam : ℝ} (hrow : inRow i lam) :
    0 < lam ∧ lam ≤ 7/3 := by
  fin_cases i <;> norm_num [inRow,rowData] at hrow <;> constructor <;> linarith

theorem row_Gamma_pos {i : Fin 4} {lam : ℝ} (hrow : inRow i lam) :
    0 < capitalGamma i lam := by
  fin_cases i
  · exact lt_of_lt_of_le (by norm_num : (0:ℝ)<73/500) (D_Gamma_lower hrow)
  · exact lt_of_lt_of_le (by norm_num : (0:ℝ)<19/100) (E1_Gamma_lower hrow)
  · exact lt_of_lt_of_le (by norm_num : (0:ℝ)<6/25) (E2_Gamma_lower hrow)
  · exact lt_of_lt_of_le (by norm_num : (0:ℝ)<19/80) (H_Gamma_lower hrow)

theorem parentP_lower {i : Fin 4} {lam H rho : ℝ}
    (hl : 0 < lam) (hH : 0 ≤ H) (hcap : H ≤ childQ lam/2)
    (hrho : rhoMin lam (halfParent lam H) ≤ rho) (hg : 0 ≤ gamma i lam) :
    1/(1+2*lam)+2*gamma i lam/(2+lam) ≤ parentP i lam H rho := by
  have hp := halfParent_bounds hl hH hcap
  have hq : halfParent lam H*(1+lam) ≤ lam :=
    (le_div_iff₀ (show 0 < 1+lam by linarith)).mp hp.2.2.2
  have hpm : 0 < 1-halfParent lam H := sub_pos.mpr hp.2.2.1
  have hd : 0 < 1+lam*(1-halfParent lam H) := by positivity
  have h2 : 0 < 2-halfParent lam H := by linarith [hp.2.2.1]
  have hbase : 1/(1+2*lam) ≤ (1-halfParent lam H)/(1+lam*(1-halfParent lam H)) := by
    apply (div_le_div_iff₀ (by linarith) hd).2
    nlinarith
  have hrr := mul_le_mul_of_nonneg_right hrho (show 0 ≤ 1-halfParent lam H by linarith [hp.2.2.1])
  have hrid : rhoMin lam (halfParent lam H)*(1-halfParent lam H) =
      (1-halfParent lam H)/(1+lam*(1-halfParent lam H)) := by unfold rhoMin; ring
  rw [hrid] at hrr
  have ht : 2/(2+lam) ≤ 2*(1-halfParent lam H)/(2-halfParent lam H) := by
    apply (div_le_div_iff₀ (by linarith) h2).2
    nlinarith
  have hh := ht.trans (messageRatio_lower hp.2.1.le hp.2.2.1)
  have hgm := mul_le_mul_of_nonneg_left hh hg
  have hgm' : 2*gamma i lam/(2+lam) ≤ gamma i lam*messageRatio (halfParent lam H) := by
    convert hgm using 1 <;> ring
  unfold parentP
  linarith [hbase.trans hrr]

theorem parent_hY_identity {H : ℝ} (hH : 0 < H) (hH1 : H < 1) :
    messageRatio H*parentY H = H := by
  have hy := (scalarLog_pos hH hH1).ne'
  rw [messageRatio_eq_scalarH hH.ne']
  change (H/scalarLog H)*scalarLog H=H
  exact div_mul_cancel₀ _ hy

theorem parentR_guard_lower {i : Fin 4} {lam H rho u : ℝ}
    (hl : 0 < lam) (hH : 0 < H) (hcap : H ≤ childQ lam/2)
    (hrho : rhoMin lam (halfParent lam H) ≤ rho)
    (hg : 0 ≤ gamma i lam) (hGamma : 0 ≤ capitalGamma i lam)
    (hd : 0 < parentD i lam H rho) (hu : 0 ≤ u) (huH : u ≤ H) :
    guardValue lam (capitalGamma i lam) (gamma i lam) (alpha i lam+beta i lam) ≤
      (parentC i lam H rho+2*parentD i lam H rho*messageRatio u)/halfParent lam H := by
  have hp := halfParent_bounds hl hH.le hcap
  have hH1 : H < 1 := by linarith [hp.1]
  have hmono := messageRatio_antitoneOn ⟨hu,by linarith⟩ ⟨hH.le,hH1⟩ huH
  have hm := mul_le_mul_of_nonneg_left hmono (show 0 ≤ 2*parentD i lam H rho by positivity)
  have hfirst : (parentC i lam H rho+2*parentD i lam H rho*messageRatio H)/halfParent lam H ≤
      (parentC i lam H rho+2*parentD i lam H rho*messageRatio u)/halfParent lam H :=
    div_le_div_of_nonneg_right (by linarith) hp.2.1.le
  have hident : (parentC i lam H rho+2*parentD i lam H rho*messageRatio H)/halfParent lam H =
      2*capitalGamma i lam*(messageRatio H/halfParent lam H)-
      (alpha i lam+beta i lam)+2*parentP i lam H rho*(1-H) := by
    have hy := parent_hY_identity hH hH1
    unfold parentC parentD capitalGamma
    field_simp [hp.2.1.ne']
    nlinarith [congrArg (fun x : ℝ => 2*halfParent lam H*parentP i lam H rho*x) hy]
  have ha := mul_le_mul_of_nonneg_left (aStar_le_parent_ratio hl hH.le hcap)
    (show 0 ≤ 2*capitalGamma i lam by positivity)
  have hP := parentP_lower hl hH.le hcap hrho hg
  have hPl : 0 < 1/(1+2*lam)+2*gamma i lam/(2+lam) := by positivity
  have hq1 : childQ lam < 1 := (div_lt_one (by linarith : 0 < 1+lam)).2 (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hP (show 0 ≤ 2*(1-H) by linarith)
  have hmul2 := mul_le_mul_of_nonneg_right (show 2*(1-childQ lam/2) ≤ 2*(1-H) by linarith) hPl.le
  have hclosed : 2*(1-childQ lam/2)*(1/(1+2*lam)+2*gamma i lam/(2+lam)) =
      (lam+2)/((1+lam)*(1+2*lam))+2*gamma i lam/(1+lam) := by
    unfold childQ
    field_simp [show 1+lam ≠ 0 by positivity,show 1+2*lam ≠ 0 by positivity,
      show 2+lam ≠ 0 by positivity]
    ring
  unfold guardValue
  rw [hident] at hfirst
  rw [hclosed] at hmul2
  nlinarith

theorem guardValue_mono {lam «GL» G gL g AU A : ℝ} (hl : 0 < lam)
    (hG : «GL» ≤ G) (hg : gL ≤ g) (hA : A ≤ AU) :
    guardValue lam «GL» gL AU ≤ guardValue lam G g A := by
  have h1 := mul_le_mul_of_nonneg_right hG (aStar_pos hl).le
  have h2 := div_le_div_of_nonneg_right (show 2*gL ≤ 2*g by linarith)
    (show 0 ≤ 1+lam by linarith)
  unfold guardValue
  linarith

theorem parentR_pos {i : Fin 4} {lam H rho u : ℝ} (hrow : inRow i lam)
    (hH : 0 < H) (hcap : H ≤ childQ lam/2)
    (hrho : rhoMin lam (halfParent lam H) ≤ rho) (hrho1 : rho ≤ 1)
    (hu : 0 ≤ u) (huH : u ≤ H) :
    0 < parentC i lam H rho+2*parentD i lam H rho*messageRatio u := by
  have hl := (row_activity_bounds hrow).1
  have hp := (halfParent_bounds hl hH.le hcap).2.1
  have hg := (all_rows_fields_positive hrow).2.2.1
  have hd := parentD_gt_fortieth hrow hH hcap hrho1
  have hlow := parentR_guard_lower hl hH hcap hrho hg.le (row_Gamma_pos hrow).le
    (by linarith) hu huH
  have hguard : 0 < guardValue lam (capitalGamma i lam) (gamma i lam) (alpha i lam+beta i lam) := by
    fin_cases i
    · have hr : 4/5 ≤ lam ∧ lam ≤ 13/10 := by simpa [inRow,rowData] using hrow
      have h := guardValue_mono hl (D_Gamma_affine_lower hrow) (D_gamma_affine_lower hrow)
        (D_alpha_beta_upper hrow)
      exact lt_of_lt_of_le (lt_trans (by norm_num : (0:ℝ)<1/8)
        (D_guard_gt_eighth hr.1 hr.2)) h
    · have hr : 13/10 ≤ lam ∧ lam ≤ 29/20 := by simpa [inRow,rowData] using hrow
      have h := guardValue_mono hl (E1_Gamma_affine_lower hrow) (E1_gamma_affine_lower hrow)
        (E1_alpha_beta_upper hrow)
      exact lt_of_lt_of_le (lt_trans (by norm_num : (0:ℝ)<1/8)
        (E1_guard_gt_eighth hr.1 hr.2)) h
    · have hr : 29/20 ≤ lam ∧ lam ≤ 8/5 := by simpa [inRow,rowData] using hrow
      have h := guardValue_mono hl (E2_Gamma_affine_lower hrow) (E2_gamma_affine_lower hrow)
        (E2_alpha_beta_upper hrow)
      exact lt_of_lt_of_le (lt_trans (by norm_num : (0:ℝ)<1/8)
        (E2_guard_gt_eighth hr.1 hr.2)) h
    · have hr : 7/4 ≤ lam ∧ lam ≤ 7/3 := by simpa [inRow,rowData] using hrow
      exact (H_guard_pos hr.1 hr.2).trans_le
        (guardValue_mono hl (H_Gamma_affine_lower hrow) (H_gamma_lower hrow) (H_alpha_beta_upper hrow))
  have hratio : 0 < (parentC i lam H rho+2*parentD i lam H rho*messageRatio u)/halfParent lam H :=
    hguard.trans_le hlow
  exact ((div_pos_iff.mp hratio).resolve_right (by intro h; linarith [h.2])).1

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.row_activity_bounds
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.row_activity_bounds
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.row_Gamma_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.row_Gamma_pos
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentP_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentP_lower
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parent_hY_identity
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parent_hY_identity
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentR_guard_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentR_guard_lower
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.guardValue_mono
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.guardValue_mono
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentR_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentR_pos
