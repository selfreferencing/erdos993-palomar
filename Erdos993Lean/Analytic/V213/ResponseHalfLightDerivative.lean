module

public import Erdos993Lean.Analytic.V213.ResponseParentSlopeBounds
public import Erdos993Lean.Analytic.V213.ResponseHalfLightAdverse
public import Erdos993Lean.Analytic.V213.ResponseMinimumCurve
public import Erdos993Lean.Analytic.V213.ResponseParentLogFacts

/-! The printed half-light derivative is positive for each of the four actual
rows. All scalar logarithms and parent coefficient guards are discharged here.
No finite response certificate or unproved row-sign hypothesis is retained. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows

private theorem concave_endpoint_pos {b c delta b0 C delta0 : ℝ}
    (hb0 : 0 < b0) (hC : 0 < C) (hd0 : 0 < delta0)
    (hb : b0 ≤ b) (hc : c ≤ C) (hd : delta0 ≤ delta)
    (hend : 0 < b0+C-C^2/(4*delta0)) :
    0 < b+max c 0-(max c 0)^2/(4*delta) := by
  let x := max c 0
  have hx0 : 0 ≤ x := le_max_right _ _
  have hxC : x ≤ C := max_le hc hC.le
  have hw0 : 0 ≤ x/C := div_nonneg hx0 hC.le
  have hw1 : x/C ≤ 1 := (div_le_one hC).2 hxC
  let k := min b0 (b0+C-C^2/(4*delta0))
  have hk : 0 < k := lt_min hb0 hend
  have hwL := mul_le_mul_of_nonneg_left (min_le_left b0 (b0+C-C^2/(4*delta0)))
    (show 0 ≤ 1-x/C by linarith)
  have hwR := mul_le_mul_of_nonneg_left (min_le_right b0 (b0+C-C^2/(4*delta0))) hw0
  have hidentity : b0+x-x^2/(4*delta0)-
      ((1-x/C)*b0+(x/C)*(b0+C-C^2/(4*delta0))) = x*(C-x)/(4*delta0) := by
    field_simp [hC.ne',hd0.ne']
    ring
  have hrest : 0 ≤ x*(C-x)/(4*delta0) :=
    div_nonneg (mul_nonneg hx0 (sub_nonneg.mpr hxC)) (by positivity)
  have hbase : 0 < b0+x-x^2/(4*delta0) := by
    have hsum : (1-x/C)*k+(x/C)*k=k := by ring
    change (1-x/C)*k ≤ (1-x/C)*b0 at hwL
    change (x/C)*k ≤ (x/C)*(b0+C-C^2/(4*delta0)) at hwR
    linarith
  have hdpos : 0 < delta := hd0.trans_le hd
  have hden : x^2/(4*delta) ≤ x^2/(4*delta0) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    have h := mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hd)
    nlinarith
  change 0 < b+x-x^2/(4*delta)
  linarith

theorem parent_c_endpoint_pos {i : Fin 4} {lam H rho : ℝ}
    (hrow : inRow i lam) (hH : 0 < H) (hcap : H ≤ childQ lam/2)
    (hrho : rhoMin lam (halfParent lam H) ≤ rho) (hrho1 : rho ≤ 1) :
    0 < parentB i lam H rho+max (parentC i lam H rho) 0-
      (max (parentC i lam H rho) 0)^2/(4*delta i lam) := by
  fin_cases i
  · exact concave_endpoint_pos (by norm_num : (0:ℝ)<364/2725)
      (by norm_num : (0:ℝ)<1/8) (by norm_num : (0:ℝ)<1/50)
      (D_parentB_lower hrow hH.le hcap hrho) (D_parentC_upper hrow hH.le hcap hrho1)
      (D_delta_lower hrow) (by norm_num)
  · exact concave_endpoint_pos (by norm_num : (0:ℝ)<1/10)
      (by norm_num : (0:ℝ)<1/5) (by norm_num : (0:ℝ)<1/25)
      (E1_parentB_lower hrow hH.le hcap hrho) (E1_parentC_upper hrow hH.le hcap hrho1)
      (E1_delta_lower hrow) (by norm_num)
  · exact concave_endpoint_pos (by norm_num : (0:ℝ)<1/8)
      (by norm_num : (0:ℝ)<4/25) (by norm_num : (0:ℝ)<1/25)
      (E2_parentB_lower hrow hH.le hcap hrho) (E2_parentC_upper hrow hH.le hcap hrho1)
      (E2_delta_lower hrow) (by norm_num)
  · have hl := (row_activity_bounds hrow).1
    have hb := parentB_pos hrow hl hH.le hcap hrho
    have hd := H_delta_pos hrow
    have hc := H_parentC_upper hrow hH.le hcap hrho1
    change 0 < parentB 3 lam H rho at hb
    change 0 < parentB 3 lam H rho+max (parentC 3 lam H rho) 0-
      (max (parentC 3 lam H rho) 0)^2/(4*delta 3 lam)
    by_cases hc0 : 0 ≤ parentC 3 lam H rho
    · rw [max_eq_left hc0]
      have hsq : (parentC 3 lam H rho)^2/(4*delta 3 lam) ≤ parentC 3 lam H rho := by
        apply (div_le_iff₀ (by positivity)).2
        have h := mul_nonneg hc0 (show 0 ≤ 4*delta 3 lam-parentC 3 lam H rho by linarith)
        nlinarith
      linarith
    · rw [max_eq_right (le_of_not_ge hc0)]
      simpa using hb

theorem parent_last_endpoint_pos {i : Fin 4} {lam H rho u : ℝ}
    (hrow : inRow i lam) (hH : 0 < H) (hcap : H ≤ childQ lam/2)
    (hrho : rhoMin lam (halfParent lam H) ≤ rho)
    (hu : 0 < u) (huH : u ≤ H) :
    0 < parentB i lam H rho-delta i lam*(1-messageRatio u*childLog lam u)/
      (u*(childLog lam u)^2*(messageRatio u-1+u)) := by
  have hl := (row_activity_bounds hrow).1
  have huh : u ≤ childQ lam/2 := huH.trans hcap
  have hchild := half_child_bounds hl hu huh
  have hd := (all_rows_fields_positive hrow).2.2.2
  have hb := parentB_pos hrow hl hH.le hcap hrho
  have hT := hchild.2.2.1
  have hgap := hchild.2.2.2.2
  have hden : 0 < u*(childLog lam u)^2*(messageRatio u-1+u) := by positivity
  by_cases hprod : messageRatio u*childLog lam u < 1
  · fin_cases i
    · change 0 < parentB 0 lam H rho-delta 0 lam*(1-messageRatio u*childLog lam u)/
        (u*(childLog lam u)^2*(messageRatio u-1+u))
      have hdD : 0 < delta 0 lam := hd
      have hr : 4/5 ≤ lam ∧ lam ≤ 13/10 := by simpa [inRow,rowData] using hrow
      have hb0 := D_parentB_lower hrow hH.le hcap hrho
      have hbad := child_D_adverse_bound hr.1 hr.2 hu huh hdD
        (D_delta_adverse_upper hrow) hprod log_fourteen_fifths_gt log_sixteen_fifths_gt
      linarith
    · have hr : 13/10 ≤ lam ∧ lam ≤ 29/20 := by simpa [inRow,rowData] using hrow
      have hg := child_product_gt_one_EH hr.1 hu huh log_thirtythree_tenths_gt log_fortysix_thirtythirds_lt
      linarith
    · have hr : 29/20 ≤ lam ∧ lam ≤ 8/5 := by simpa [inRow,rowData] using hrow
      have hg := child_product_gt_one_EH (show 13/10 ≤ lam by linarith) hu huh
        log_thirtythree_tenths_gt log_fortysix_thirtythirds_lt
      linarith
    · have hr : 7/4 ≤ lam ∧ lam ≤ 7/3 := by simpa [inRow,rowData] using hrow
      have hg := child_product_gt_one_EH (show 13/10 ≤ lam by linarith) hu huh
        log_thirtythree_tenths_gt log_fortysix_thirtythirds_lt
      linarith
  · have hn : delta i lam*(1-messageRatio u*childLog lam u)/
        (u*(childLog lam u)^2*(messageRatio u-1+u)) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos hd.le (by linarith)) hden.le
    linarith

theorem parent_minimumCurveDerivative_pos {i : Fin 4} {lam H rho u : ℝ}
    (hrow : inRow i lam) (hH : 0 < H) (hcap : H ≤ childQ lam/2)
    (hrho : rhoMin lam (halfParent lam H) ≤ rho) (hrho1 : rho ≤ 1)
    (hu : 0 < u) (huH : u ≤ H) :
    0 < minimumCurveDerivative (parentB i lam H rho) (parentC i lam H rho)
      (parentD i lam H rho) (delta i lam) lam u := by
  have hl := (row_activity_bounds hrow).1
  have hd := parentD_gt_fortieth hrow hH hcap hrho1
  have hd0 : 0 < parentD i lam H rho := by linarith
  have hdelta := (all_rows_fields_positive hrow).2.2.2
  have hb := parentB_pos hrow hl hH.le hcap hrho
  have hr := parentR_pos hrow hH hcap hrho hrho1 hu.le huH
  have huh : u ≤ childQ lam/2 := huH.trans hcap
  by_cases he : childSlope lam u ≤ 0
  · exact hb.trans (minimumCurveDerivative_gt_b_of_nonpos hd0 hdelta hl hu huh hr he)
  · have hc := parent_c_endpoint_pos hrow hH hcap hrho hrho1
    have hlast := parent_last_endpoint_pos hrow hH hcap hrho hu huH
    exact (lt_min hb (lt_min hc hlast)).trans_le
      (minimumCurveDerivative_lower hd0 hdelta hb hl hu huh hr (lt_of_not_ge he)
        (childSlope_lt_one_half hl hu huh))

/-- Literal derivative in the h coordinate of the actual response minimum. -/
theorem parent_minimum_derivative_ratio_pos {i : Fin 4} {lam H rho u : ℝ}
    (hrow : inRow i lam) (hH : 0 < H) (hcap : H ≤ childQ lam/2)
    (hrho : rhoMin lam (halfParent lam H) ≤ rho) (hrho1 : rho ≤ 1)
    (hu : 0 < u) (huH : u ≤ H) :
    0 < deriv (parentMinimum i lam H rho) u / deriv messageRatio u := by
  have hl := (row_activity_bounds hrow).1
  have hcb := half_child_bounds hl hu (huH.trans hcap)
  have hdelta := (all_rows_fields_positive hrow).2.2.2
  have hd := parentD_gt_fortieth hrow hH hcap hrho1
  have hJ := hcb.2.2.2.1
  have hdpos : 0 < parentD i lam H rho := by linarith
  have hG : 0 < delta i lam+parentD i lam H rho*childJ lam u := by positivity
  change 0 < deriv (minimumAlong (parentA i lam H rho) (parentB i lam H rho)
    (parentC i lam H rho) (parentD i lam H rho) (delta i lam) lam) u / deriv messageRatio u
  rw [minimumCurveDerivative_eq_ratio _ _ _ _ _ hl hu (by linarith [hcb.1]) hdelta.ne' hG.ne']
  exact parent_minimumCurveDerivative_pos hrow hH hcap hrho hrho1 hu huH

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parent_c_endpoint_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parent_c_endpoint_pos
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parent_last_endpoint_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parent_last_endpoint_pos
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parent_minimumCurveDerivative_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parent_minimumCurveDerivative_pos
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parent_minimum_derivative_ratio_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parent_minimum_derivative_ratio_pos
