module

public import Erdos993Lean.Analytic.V213.ResponseChildTangents

/-! Actual half-light child curve. The strict slope estimate and the last
endpoint identity are derived from the printed elementary logarithm bounds.
No row, response certificate, or parent sign is assumed in this module. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse

open FreeCountVariance.Envelopes

theorem childLog_pos {lam u : ℝ} (hl : 0 < lam) (hu : 0 < u)
    (huq : u < childQ lam) : 0 < childLog lam u := by
  have h := (lt_div_iff₀ (show 0 < 1+lam by linarith)).mp huq
  apply Real.log_pos
  exact (lt_div_iff₀ hu).2 (by nlinarith)

theorem half_child_bounds {lam u : ℝ} (hl : 0 < lam) (hu : 0 < u)
    (huh : u ≤ childQ lam/2) :
    u < 1/2 ∧ 0 < messageRatio u ∧ 0 < childLog lam u ∧
      0 < childJ lam u ∧ 0 < messageRatio u-1+u := by
  have hq0 : 0 < childQ lam := div_pos hl (by linarith)
  have hq1 : childQ lam < 1 := (div_lt_one (by linarith : 0 < 1+lam)).2 (by linarith)
  have hu1 : u < 1 := by linarith
  have hh : 0 < messageRatio u := by
    rw [messageRatio_eq_scalarH hu.ne',scalarH]
    exact div_pos hu (scalarLog_pos hu hu1)
  have hT := childLog_pos hl hu (by linarith)
  have hg := messageRatio_strict_lower hu hu1
  exact ⟨by linarith,hh,hT,mul_pos (mul_pos hu hh) hT,by linarith⟩

theorem childSlope_formula {lam u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    childSlope lam u =
      u*(1+(messageRatio u-2*(1-u))*childLog lam u)/(messageRatio u-1+u) := by
  have hphi := (scalarLog_pos hu hu1).ne'
  have hD := (childD_pos hu hu1).ne'
  rw [messageRatio_eq_scalarH hu.ne']
  unfold scalarH childSlope childD at *
  field_simp [hphi,hD]
  ring

theorem child_half_log_lower {lam u : ℝ} (hl : 0 < lam) (hu : 0 < u)
    (huh : u ≤ childQ lam/2) : 2/(3-4*u) ≤ childLog lam u := by
  have hb := half_child_bounds hl hu huh
  have hd : 0 < 1-2*u := by linarith [hb.1]
  have hd3 : 0 < 3-4*u := by linarith [hb.1]
  have hc : 2*u*(1+lam) ≤ lam :=
    (le_div_iff₀ (show 0 < 1+lam by linarith)).mp (show 2*u ≤ childQ lam by linarith)
  have harg : 2*(1-u)/(1-2*u) ≤ lam*(1-u)/u := by
    apply (div_le_div_iff₀ hd hu).2
    have hx := mul_nonneg (show 0 ≤ lam*(1-2*u)-2*u by nlinarith)
      (show 0 ≤ 1-u by linarith [hb.1])
    nlinarith
  have hlog := (elementary_log_bounds (show 0 ≤ 1/(1-2*u) by positivity)).1
  have hi : 1+1/(1-2*u) = 2*(1-u)/(1-2*u) := by
    field_simp [hd.ne']
    ring
  have hj : 2*(1/(1-2*u))/(2+1/(1-2*u)) = 2/(3-4*u) := by
    field_simp [hd.ne',hd3.ne']
    all_goals ring_nf
    all_goals field_simp [show (3-u*4 : ℝ) ≠ 0 by linarith [hb.1]] <;> ring
  rw [hi,hj] at hlog
  exact hlog.trans (Real.log_le_log (div_pos (mul_pos (by norm_num) (by linarith [hb.1])) hd) harg)

theorem childSlope_lt_one_half {lam u : ℝ} (hl : 0 < lam) (hu : 0 < u)
    (huh : u ≤ childQ lam/2) : childSlope lam u < 1 := by
  have hb := half_child_bounds hl hu huh
  have hu1 : u < 1 := by linarith [hb.1]
  have hden : 0 < 3-4*u := by linarith [hb.1]
  have hden2 : 0 < 2-u := by linarith [hb.1]
  have hhlo := messageRatio_lower hu.le hu1
  have hhhi := (messageRatio_weak_bounds hu.le hu1).2
  have hcoef : messageRatio u-2*(1-u) < 0 := by linarith [hb.1]
  have hT := child_half_log_lower hl hu huh
  have hn := mul_le_mul_of_nonpos_left hT hcoef.le
  have hnum : u*(1+(messageRatio u-2*(1-u))*childLog lam u) ≤
      u*(2*messageRatio u-1)/(3-4*u) := by
    have hm := mul_le_mul_of_nonneg_left hn hu.le
    have hi : u*(1+(messageRatio u-2*(1-u))*(2/(3-4*u))) =
        u*(2*messageRatio u-1)/(3-4*u) := by
      field_simp [hden.ne']
      all_goals ring_nf
      all_goals field_simp [show (3-u*4 : ℝ) ≠ 0 by linarith [hb.1]] <;> ring
    linarith
  have hp : 0 < u*(1-2*u)^2/(2-u) := by
    exact div_pos (mul_pos hu (sq_pos_of_pos (by linarith [hb.1]))) hden2
  have hi : 3*(1-2*u)*(2*(1-u)/(2-u))-(3-8*u+4*u^2) =
      u*(1-2*u)^2/(2-u) := by
    field_simp [hden2.ne']
    ring
  have hm := mul_le_mul_of_nonneg_left hhlo (show 0 ≤ 3*(1-2*u) by linarith [hb.1])
  have hcross : u*(2*messageRatio u-1) < (messageRatio u-1+u)*(3-4*u) := by
    nlinarith
  have hquot := (div_lt_iff₀ hden).2 hcross
  rw [childSlope_formula hu hu1]
  apply (div_lt_one hb.2.2.2.2).2
  exact hnum.trans_lt hquot

theorem child_slope_endpoint_identity {lam u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    messageRatio u*childSlope lam u-2*childJ lam u =
      u*messageRatio u*(1-messageRatio u*childLog lam u)/(messageRatio u-1+u) := by
  have hg : messageRatio u-1+u ≠ 0 := by
    have h := messageRatio_strict_lower hu hu1
    linarith
  rw [childSlope_formula hu hu1]
  unfold childJ
  field_simp [hg]
  ring

theorem child_derivative_endpoint (b delta : ℝ) {lam u : ℝ}
    (hl : 0 < lam) (hu : 0 < u) (huh : u ≤ childQ lam/2) (hd : 0 < delta) :
    b+2*delta*messageRatio u/childJ lam u-
      childSlope lam u*(2*delta*messageRatio u/childJ lam u)^2/(4*delta) =
    b-delta*(1-messageRatio u*childLog lam u)/
      (u*(childLog lam u)^2*(messageRatio u-1+u)) := by
  have hb := half_child_bounds hl hu huh
  rw [childSlope_formula hu (by linarith [hb.1])]
  unfold childJ
  field_simp [hu.ne',hb.2.1.ne',hb.2.2.1.ne',hb.2.2.2.2.ne',hd.ne']
  ring

end Erdos993Lean.Analytic.V213.VarianceResponse

#check Erdos993Lean.Analytic.V213.VarianceResponse.childLog_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.childLog_pos
#check Erdos993Lean.Analytic.V213.VarianceResponse.half_child_bounds
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.half_child_bounds
#check Erdos993Lean.Analytic.V213.VarianceResponse.childSlope_formula
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.childSlope_formula
#check Erdos993Lean.Analytic.V213.VarianceResponse.child_half_log_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.child_half_log_lower
#check Erdos993Lean.Analytic.V213.VarianceResponse.childSlope_lt_one_half
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.childSlope_lt_one_half
#check Erdos993Lean.Analytic.V213.VarianceResponse.child_slope_endpoint_identity
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.child_slope_endpoint_identity
#check Erdos993Lean.Analytic.V213.VarianceResponse.child_derivative_endpoint
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.child_derivative_endpoint
