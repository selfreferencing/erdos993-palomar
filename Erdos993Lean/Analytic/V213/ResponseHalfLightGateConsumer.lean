module

public import Erdos993Lean.Analytic.V213.ResponseControlGateCoverage

/-! Whole-activity-interval control and determinant-polynomial positivity.
Every actual length, index-cover and finite gate premise remains explicit.
This module does not establish any of the277 gates or Eq19's analytic link. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates

open Erdos993Lean.BCFG

theorem row_interval_positive (i : Fin 4) :
    (0:ℚ)<(rowData i).low ∧ (rowData i).low<(rowData i).high := by
  fin_cases i <;> norm_num [rowData]

theorem activity_q_in_interval {r : Fin 8} {lam : ℝ}
    (hrow : inRow (productSpec r).rowIndex lam) :
    (qLow r:ℝ)≤lam/(1+lam) ∧ lam/(1+lam)≤(qHigh r:ℝ) := by
  have hlo : (0:ℝ)<((rowData (productSpec r).rowIndex).low:ℝ) := by
    exact_mod_cast (row_interval_positive (productSpec r).rowIndex).1
  have hends : ((rowData (productSpec r).rowIndex).low:ℝ)<
      ((rowData (productSpec r).rowIndex).high:ℝ) := by
    exact_mod_cast (row_interval_positive (productSpec r).rowIndex).2
  change ((rowData (productSpec r).rowIndex).low:ℝ)≤lam ∧
    lam≤((rowData (productSpec r).rowIndex).high:ℝ) at hrow
  have hlam : 0<lam := hlo.trans_le hrow.1
  unfold qLow qHigh
  push_cast
  constructor
  · apply (div_le_div_iff₀ (by linarith) (by linarith)).2
    nlinarith [hrow.1]
  · apply (div_le_div_iff₀ (by linarith) (by linarith)).2
    nlinarith [hrow.2]

theorem controlPolynomial_positive_of_gates (c : Fin 97)
    (hN : 2≤(productSpec (controlSpec c).product).degreeLambda)
    (hcontrol : (controlPolynomial c).length≤(productSpec (controlSpec c).product).degreeLambda+1)
    (hshift : (shiftedControl c).length≤(productSpec (controlSpec c).product).degreeLambda+1)
    (hcoverage : ControlGateCoverage c) (hgates : ∀g,gateHolds g)
    {lam : ℝ} (hrow : inRow (productSpec (controlSpec c).product).rowIndex lam) :
    0<Uni.evalReal (controlPolynomial c) lam := by
  have hlo : (0:ℝ)<((rowData (productSpec (controlSpec c).product).rowIndex).low:ℝ) := by
    exact_mod_cast (row_interval_positive (productSpec (controlSpec c).product).rowIndex).1
  have hlam : 0<lam := hlo.trans_le hrow.1
  have hq := activity_q_in_interval hrow
  have hn := normalized_control_positive_of_gates c hN hshift hcoverage hgates hq
  have hq1 : lam/(1+lam)<1 := (div_lt_one (by linarith : 0<1+lam)).2 (by linarith)
  have hp := controlPolynomial_pos_of_normalized c hcontrol hq1 hn
  have hid : (lam/(1+lam))/(1-lam/(1+lam))=lam := by
    field_simp [show 1+lam≠0 by positivity]
    ring
  simpa only [hid] using hp

theorem determinantPolynomial_positive_of_gates (r : Fin 8)
    (houter : (trimmedDeterminant r).length≤(productSpec r).degreeXi+1)
    (hindex : ∀j≤(productSpec r).degreeXi,∃c:Fin 97,
      (controlSpec c).product=r ∧ (controlSpec c).index=j)
    (hN : ∀c:Fin 97,2≤(productSpec (controlSpec c).product).degreeLambda)
    (hcontrol : ∀c:Fin 97,(controlPolynomial c).length≤
      (productSpec (controlSpec c).product).degreeLambda+1)
    (hshift : ∀c:Fin 97,(shiftedControl c).length≤
      (productSpec (controlSpec c).product).degreeLambda+1)
    (hcoverage : ∀c:Fin 97,ControlGateCoverage c) (hgates : ∀g,gateHolds g)
    {xi lam : ℝ} (hxi : 0≤xi ∧ xi≤1) (hrow : inRow (productSpec r).rowIndex lam) :
    0<Bi.evalReal (HalfLightPolys.determinantPolynomial r) xi lam := by
  apply determinant_positive_of_controls r houter hindex hxi
  intro c hc
  apply controlPolynomial_positive_of_gates c (hN c) (hcontrol c) (hshift c) (hcoverage c) hgates
  simpa only [hc] using hrow

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.row_interval_positive
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.row_interval_positive
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.activity_q_in_interval
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.activity_q_in_interval
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.controlPolynomial_positive_of_gates
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.controlPolynomial_positive_of_gates
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.determinantPolynomial_positive_of_gates
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.determinantPolynomial_positive_of_gates
