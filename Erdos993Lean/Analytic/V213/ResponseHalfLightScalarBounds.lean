module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightQuadraticDefs
public import Erdos993Lean.Analytic.V213.ResponseParentSlopeBounds
public import Erdos993Lean.Analytic.V213.ResponseRatioPolynomials
public import Erdos993Lean.Analytic.V213.ResponseHalfLightChild

/-! The three actual scalar substitutions in printed Eq16, with all positive
factors proved on the closed half-light parent domain. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight

open FreeCountVariance.Envelopes

theorem row_activity_lower {i : Fin 4} {lam : ℝ} (hrow : inRow i lam) : 4/5 ≤ lam := by
  fin_cases i <;> norm_num [inRow,rowData] at hrow <;> linarith

theorem row_price_pos {i : Fin 4} {lam : ℝ} (hrow : inRow i lam) : 0 < price i lam := by
  have hl := (row_activity_bounds hrow).1
  fin_cases i <;> norm_num [price,rowData] <;> positivity

theorem parent_ratio_upper {i : Fin 4} {lam H : ℝ} (hrow : inRow i lam)
    (hH : 0 ≤ H) (hcap : H ≤ childQ lam/2) :
    messageRatio (halfParent lam H) ≤ upperRatio (halfParent lam H) := by
  have hl := (row_activity_bounds hrow).1
  have hp := halfParent_bounds hl hH hcap
  have hm := pStar_monotone (by norm_num : (0:ℝ)<4/5) (row_activity_lower hrow)
  norm_num [pStar] at hm
  change (28/73:ℝ) ≤ pStar lam at hm
  have hp3 : (3/8:ℝ) ≤ halfParent lam H := by
    linarith [pStar_le_halfParent hl hH hcap]
  exact messageRatio_le_U hp3 hp.2.2.1

theorem boundary_child_ratio_lower {H : ℝ} (hH : 0 < H) (hH1 : H < 1) :
    lowerChildRatio H ≤ H/parentY H := by
  have h := messageRatio_lower hH.le hH1
  rw [messageRatio_eq_scalarH hH.ne'] at h
  exact h

theorem responseFactor_den_pos {lam H : ℝ} (hl : 0 < lam)
    (hH : 0 ≤ H) (hcap : H ≤ childQ lam/2) :
    0 < lam^2*(1-H)^2-H^2 := by
  have hp := halfParent_bounds hl hH hcap
  have hHm : 0 < 1-H := by linarith [hp.1]
  have hq0 : 0 < childQ lam := div_pos hl (by linarith)
  have hc : H*(1+lam) < lam :=
    (lt_div_iff₀ (show 0 < 1+lam by linarith)).mp (show H < childQ lam by linarith)
  have hm : 0 < (lam*(1-H)-H)*(lam*(1-H)+H) := mul_pos (by nlinarith) (by positivity)
  nlinarith

theorem responseFactor_pos {i : Fin 4} {lam H : ℝ} (hrow : inRow i lam)
    (hH : 0 ≤ H) (hcap : H ≤ childQ lam/2) : 0 < responseFactor i lam H := by
  have hl := (row_activity_bounds hrow).1
  have hp := halfParent_bounds hl hH hcap
  have hHm : 0 < 1-H := by linarith [hp.1]
  have hd := (all_rows_fields_positive hrow).2.2.2
  unfold responseFactor
  exact div_pos (by positivity) (responseFactor_den_pos hl hH hcap)

theorem boundary_response_lower {i : Fin 4} {lam H : ℝ} (hrow : inRow i lam)
    (hH : 0 < H) (hcap : H ≤ childQ lam/2) :
    H*responseFactor i lam H ≤ delta i lam/(halfParent lam H*childLog lam H) := by
  have hl := (row_activity_bounds hrow).1
  have hp := halfParent_bounds hl hH.le hcap
  have hHm : 0 < 1-H := by linarith [hp.1]
  have hpp := hp.2.1
  have hc := half_child_bounds hl hH hcap
  have hd := (all_rows_fields_positive hrow).2.2.2
  have hR := responseFactor_pos hrow hH.le hcap
  let v := lam*(1-H)/H
  have hv1 : 1 < v := (one_lt_div hH).2 (by
    have hq0 : 0 < childQ lam := div_pos hl (by linarith)
    have hq : H*(1+lam)<lam := (lt_div_iff₀ (show 0<1+lam by linarith)).mp
      (show H<childQ lam by linarith)
    nlinarith)
  have he := (elementary_log_bounds (show 0 ≤ v-1 by linarith)).2
  have hlog : childLog lam H ≤ (v-v⁻¹)/2 := by
    have hi : (v-1)*(2+(v-1))/(2*(1+(v-1))) = (v-v⁻¹)/2 := by
      field_simp [show v≠0 by linarith]
      ring
    have hvlog : Real.log (1+(v-1))=Real.log v := by congr 1; ring
    rw [hvlog,hi] at he
    exact he
  have hmul := mul_le_mul_of_nonneg_left hlog (show 0 ≤ H*responseFactor i lam H*halfParent lam H by positivity)
  have hid : H*responseFactor i lam H*halfParent lam H*((v-v⁻¹)/2)=delta i lam := by
    unfold responseFactor halfParent chartParent v
    field_simp [hH.ne',hl.ne',show 1-H≠0 by linarith [hp.1],
      show 1+lam*(1-H)≠0 by positivity,(responseFactor_den_pos hl hH.le hcap).ne']
    all_goals ring_nf
    all_goals field_simp [show (1+(lam-lam*H):ℝ) ≠ 0 by nlinarith [mul_pos hl hHm]] <;> ring
  apply (le_div_iff₀ (mul_pos hp.2.1 hc.2.2.1)).2
  nlinarith

theorem phaseCorrection_nonneg {i : Fin 4} {phase : ℕ} {lam H : ℝ}
    (hl : 0 < lam) (hH : 0 ≤ H) (hcap : H ≤ childQ lam/2) :
    0 ≤ phaseCorrection i phase lam H := by
  have hq : 0 < childQ lam := div_pos hl (by linarith)
  have hx : halfXi lam H ≤ 1 := (div_le_one hq).2 (by linarith)
  unfold phaseCorrection
  split_ifs <;> linarith

theorem phaseCorrection_product_nonpos {i : Fin 4} {phase : ℕ} {lam H rho : ℝ}
    (hl : 0 < lam) (hH : 0 ≤ H) (hcap : H ≤ childQ lam/2)
    (hphase : phaseDomain phase lam H rho) :
    phaseCorrection i phase lam H*(rho-rhoStar lam (halfParent lam H)) ≤ 0 := by
  have hmu := phaseCorrection_nonneg (i:=i) (phase:=phase) hl hH hcap
  by_cases hm : i=3 ∧ phase=1
  · have hp : rho ≤ rhoStar lam (halfParent lam H) := by
      rcases hphase with h | h
      · exact h.2.2
      · omega
    exact mul_nonpos_of_nonneg_of_nonpos hmu (sub_nonpos.mpr hp)
  · simp [phaseCorrection,hm]

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.row_activity_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.row_activity_lower
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.row_price_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.row_price_pos
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.parent_ratio_upper
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.parent_ratio_upper
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.boundary_child_ratio_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.boundary_child_ratio_lower
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.responseFactor_den_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.responseFactor_den_pos
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.responseFactor_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.responseFactor_pos
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.boundary_response_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.boundary_response_lower
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.phaseCorrection_nonneg
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.phaseCorrection_nonneg
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.phaseCorrection_product_nonpos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.phaseCorrection_product_nonpos
