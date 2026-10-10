module

public import Erdos993Lean.Analytic.V213.RowADiscriminantMinusZero
public import Erdos993Lean.Analytic.V213.RowADiscriminantMinusOne
public import Erdos993Lean.Analytic.V213.RowADiscriminantMinusTwo
public import Erdos993Lean.Analytic.V213.RowADiscriminantPlusZero
public import Erdos993Lean.Analytic.V213.RowADiscriminantPlusOne
public import Erdos993Lean.Analytic.V213.RowADiscriminantPlusTwo

/-! Row A Step 4: the six concrete squared tests, leading-coefficient sign
continuation, and the full signed-response Bernstein conclusion. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.RowA

theorem kappaMinus_continuous : ContinuousOn kappaMinus (Set.Ico (0:ℝ) 1) := by
  intro x hx
  have hp : 0 < 4+28*x-5*x^2 := minus_factor_pos hx.1 hx.2
  have h1 : 0 < 1-x := sub_pos.mpr hx.2
  have hd : 0 < 20*(1-x)*(4+28*x-5*x^2) := by positivity
  have hn : ContinuousAt (fun x : ℝ => 21*(4-x)*(x+2)) x := by fun_prop
  have hden : ContinuousAt (fun x : ℝ => 20*(1-x)*(4+28*x-5*x^2)) x := by fun_prop
  exact (hn.div hden hd.ne').continuousWithinAt

theorem discriminantMinus_positive (j : Fin 3) {x : ℝ}
    (hx : 0 ≤ x) (hx1 : x < 1) : 0 < discriminantMinus x j := by
  fin_cases j
  · exact discriminant_minus_zero_positive hx hx1
  · exact discriminant_minus_one_positive hx hx1
  · exact discriminant_minus_two_positive hx hx1

theorem leadingMinus_positive (j : Fin 3) {x : ℝ}
    (hx : 0 ≤ x) (hx1 : x < 1) :
    0 < bernsteinK (kappaMinus x) (nuMinus x) (1/4) x j := by
  have hnu : Continuous nuMinus := by unfold nuMinus; fun_prop
  have hlin : Continuous (fun x : ℝ => (1-(1/4)*x)*(3*(j.val:ℝ)/16)) := by fun_prop
  have hk : ContinuousOn (fun x => bernsteinK (kappaMinus x) (nuMinus x) (1/4) x j)
      (Set.Ico (0:ℝ) 1) := by
    exact (kappaMinus_continuous.sub hnu.continuousOn).add hlin.continuousOn
  have h0 : 0 < bernsteinK (kappaMinus 0) (nuMinus 0) (1/4) 0 j := by
    fin_cases j <;> norm_num [bernsteinK,kappaMinus,nuMinus]
  exact positive_leading_from_discriminant hk h0
    (fun y hy => discriminantMinus_positive j hy.1 hy.2) ⟨hx,hx1⟩

theorem quadMinus_pos {x r z : ℝ} (hx : 0 ≤ x) (hx1 : x < 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 3/8) : 0 < quadMinus x r z := by
  unfold quadMinus
  apply quad_positive_of_bernstein hr0 hr1
  intro j
  exact positive_quadratic (leadingMinus_positive j hx hx1)
    (discriminantMinus_positive j hx hx1) z

theorem kappaPlus_continuous : ContinuousOn kappaPlus (Set.Ico (0:ℝ) 1) := by
  intro x hx
  have hp : 0 < 16+88*x-29*x^2 := plus_factor_pos hx.1 hx.2
  have h1 : 0 < 1-x := sub_pos.mpr hx.2
  have hd : 0 < 20*(1-x)*(16+88*x-29*x^2) := by positivity
  have hn : ContinuousAt (fun x : ℝ => 21*(8-3*x)*(x+4)) x := by fun_prop
  have hden : ContinuousAt (fun x : ℝ => 20*(1-x)*(16+88*x-29*x^2)) x := by fun_prop
  exact (hn.div hden hd.ne').continuousWithinAt

theorem discriminantPlus_positive (j : Fin 3) {x : ℝ}
    (hx : 0 ≤ x) (hx1 : x < 1) : 0 < discriminantPlus x j := by
  fin_cases j
  · exact discriminant_plus_zero_positive hx hx1
  · exact discriminant_plus_one_positive hx hx1
  · exact discriminant_plus_two_positive hx hx1

theorem leadingPlus_positive (j : Fin 3) {x : ℝ}
    (hx : 0 ≤ x) (hx1 : x < 1) :
    0 < bernsteinK (kappaPlus x) (nuPlus x) (3/8) x j := by
  have hnu : Continuous nuPlus := by unfold nuPlus; fun_prop
  have hlin : Continuous (fun x : ℝ => (1-(3/8)*x)*(3*(j.val:ℝ)/16)) := by fun_prop
  have hk : ContinuousOn (fun x => bernsteinK (kappaPlus x) (nuPlus x) (3/8) x j)
      (Set.Ico (0:ℝ) 1) := by
    exact (kappaPlus_continuous.sub hnu.continuousOn).add hlin.continuousOn
  have h0 : 0 < bernsteinK (kappaPlus 0) (nuPlus 0) (3/8) 0 j := by
    fin_cases j <;> norm_num [bernsteinK,kappaPlus,nuPlus]
  exact positive_leading_from_discriminant hk h0
    (fun y hy => discriminantPlus_positive j hy.1 hy.2) ⟨hx,hx1⟩

theorem quadPlus_pos {x r z : ℝ} (hx : 0 ≤ x) (hx1 : x < 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 3/8) : 0 < quadPlus x r z := by
  unfold quadPlus
  apply quad_positive_of_bernstein hr0 hr1
  intro j
  exact positive_quadratic (leadingPlus_positive j hx hx1)
    (discriminantPlus_positive j hx hx1) z

end Erdos993Lean.Analytic.V213.VarianceResponse.RowA

#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.kappaMinus_continuous
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.kappaMinus_continuous
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.discriminantMinus_positive
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.discriminantMinus_positive
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.leadingMinus_positive
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.leadingMinus_positive
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.quadMinus_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.quadMinus_pos
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.kappaPlus_continuous
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.kappaPlus_continuous
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.discriminantPlus_positive
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.discriminantPlus_positive
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.leadingPlus_positive
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.leadingPlus_positive
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.quadPlus_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.quadPlus_pos
