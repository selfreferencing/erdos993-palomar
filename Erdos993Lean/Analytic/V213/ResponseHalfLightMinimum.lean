module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightDerivative
public import Erdos993Lean.Analytic.V213.ResponseChildZeroLimit

/-! Current Theorem 5.24: positive derivative in the decreasing h coordinate,
closed-child monotonicity, and the actual y=1 convention at u=0. The parent
source and every parent coefficient stay fixed throughout the child motion. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows

open Set

theorem parentMinimum_hasDerivAt {i : Fin 4} {lam H rho u : ℝ}
    (hrow : inRow i lam) (hH : 0 < H) (hcap : H ≤ childQ lam/2)
    (hrho1 : rho ≤ 1) (hu : 0 < u) (huH : u ≤ H) :
    HasDerivAt (parentMinimum i lam H rho)
      (minimumCurveDerivative (parentB i lam H rho) (parentC i lam H rho)
        (parentD i lam H rho) (delta i lam) lam u*childHDeriv u) u := by
  have hl := (row_activity_bounds hrow).1
  have hc := half_child_bounds hl hu (huH.trans hcap)
  have hdelta := (all_rows_fields_positive hrow).2.2.2
  have hd := parentD_gt_fortieth hrow hH hcap hrho1
  have hJ := hc.2.2.2.1
  have hdpos : 0 < parentD i lam H rho := by linarith
  have hG : 0 < delta i lam+parentD i lam H rho*childJ lam u := by positivity
  exact minimumAlong_hasDerivAt _ _ _ _ _ hl hu (by linarith [hc.1]) hdelta.ne' hG.ne'

theorem parentMinimum_zero (i : Fin 4) (lam H rho : ℝ) :
    parentMinimum i lam H rho 0 =
      parentA i lam H rho+parentB i lam H rho+parentC i lam H rho+parentD i lam H rho := by
  simp [parentMinimum,childJ_zero,messageRatio_zero,responseMinimum]
  ring

theorem parentMinimum_continuousOn {i : Fin 4} {lam H rho : ℝ}
    (hrow : inRow i lam) (hH : 0 < H) (hcap : H ≤ childQ lam/2) (hrho1 : rho ≤ 1) :
    ContinuousOn (parentMinimum i lam H rho) (Icc 0 H) := by
  intro u hu
  by_cases hu0 : u=0
  · subst u
    have hl := (row_activity_bounds hrow).1
    have hb := halfParent_bounds hl hH.le hcap
    have hH1 : H < 1 := by linarith [hb.1]
    have hh : ContinuousWithinAt messageRatio (Icc 0 H) 0 :=
      (messageRatio_continuousOn 0 (show (0:ℝ)∈Ico 0 1 by constructor <;> norm_num)).mono
        (by intro x hx; exact ⟨hx.1,hx.2.trans_lt hH1⟩)
    have hj : ContinuousWithinAt (childJ lam) (Icc 0 H) 0 :=
      (childJ_continuousWithinAt_zero hl).mono (by intro x hx; exact hx.1)
    have hdelta := (all_rows_fields_positive hrow).2.2.2
    have hG : 4*(delta i lam+parentD i lam H rho*childJ lam 0) ≠ 0 := by
      simpa only [childJ_zero,mul_zero,add_zero] using
        (mul_ne_zero (by norm_num : (4:ℝ) ≠ 0) hdelta.ne')
    unfold parentMinimum responseMinimum
    exact ((continuousWithinAt_const.add (continuousWithinAt_const.mul hh)).add
      (continuousWithinAt_const.mul (hh.pow 2))).sub
      ((hj.mul ((continuousWithinAt_const.add (continuousWithinAt_const.mul hh)).pow 2)).div
        (continuousWithinAt_const.mul (continuousWithinAt_const.add (continuousWithinAt_const.mul hj))) hG)
  · have huPos : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
    exact (parentMinimum_hasDerivAt hrow hH hcap hrho1 huPos hu.2).continuousAt.continuousWithinAt

theorem parentMinimum_antitoneOn {i : Fin 4} {lam H rho : ℝ}
    (hrow : inRow i lam) (hH : 0 < H) (hcap : H ≤ childQ lam/2)
    (hrho : rhoMin lam (halfParent lam H) ≤ rho) (hrho1 : rho ≤ 1) :
    AntitoneOn (parentMinimum i lam H rho) (Icc 0 H) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    (parentMinimum_continuousOn hrow hH hcap hrho1)
  · intro u hu
    have hu' : 0 < u ∧ u < H := by simpa only [interior_Icc,mem_Ioo] using hu
    exact (parentMinimum_hasDerivAt hrow hH hcap hrho1 hu'.1 hu'.2.le).differentiableAt.differentiableWithinAt
  · intro u hu
    have hu' : 0 < u ∧ u < H := by simpa only [interior_Icc,mem_Ioo] using hu
    rw [(parentMinimum_hasDerivAt hrow hH hcap hrho1 hu'.1 hu'.2.le).deriv]
    have hcurve := parent_minimumCurveDerivative_pos hrow hH hcap hrho hrho1 hu'.1 hu'.2.le
    have hb := halfParent_bounds (row_activity_bounds hrow).1 hH.le hcap
    exact (mul_neg_of_pos_of_neg hcurve (childHDeriv_neg hu'.1 (by linarith [hb.1]))).le

theorem parentMinimum_at_H_le {i : Fin 4} {lam H rho u : ℝ}
    (hrow : inRow i lam) (hH : 0 < H) (hcap : H ≤ childQ lam/2)
    (hrho : rhoMin lam (halfParent lam H) ≤ rho) (hrho1 : rho ≤ 1)
    (hu : 0 ≤ u) (huH : u ≤ H) :
    parentMinimum i lam H rho H ≤ parentMinimum i lam H rho u :=
  parentMinimum_antitoneOn hrow hH hcap hrho hrho1 ⟨hu,huH⟩ ⟨hH.le,le_rfl⟩ huH

theorem parentMinimum_le_payment {i : Fin 4} {lam H rho u y : ℝ}
    (hrow : inRow i lam) (hH : 0 < H) (hcap : H ≤ childQ lam/2) (hrho1 : rho ≤ 1)
    (hu : 0 ≤ u) (huH : u ≤ H) (hleaf : u=0 → y=1) :
    parentMinimum i lam H rho u ≤ parentPayment i lam H rho u y := by
  by_cases hu0 : u=0
  · have hy := hleaf hu0
    subst u
    subst y
    have h := response_leaf_convention (parentA i lam H rho) (parentB i lam H rho)
      (parentC i lam H rho) (parentD i lam H rho) (delta i lam) 1
    simpa only [parentMinimum,parentPayment,childJ_zero,messageRatio_zero] using h.ge
  · have huPos : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
    have hl := (row_activity_bounds hrow).1
    have hchild := half_child_bounds hl huPos (huH.trans hcap)
    have hdelta := (all_rows_fields_positive hrow).2.2.2
    have hd := parentD_gt_fortieth hrow hH hcap hrho1
    have hJ := hchild.2.2.2.1
    have hdpos : 0 < parentD i lam H rho := by linarith
    have hG : 0 < delta i lam+parentD i lam H rho*childJ lam u := by positivity
    exact responseMinimum_le _ _ _ _ _ _ _ _ hdelta hchild.2.2.2.1 hG

/-- The defined value is an attained real minimum for every positive child. -/
theorem parentMinimum_is_minimum {i : Fin 4} {lam H rho u : ℝ}
    (hrow : inRow i lam) (hH : 0 < H) (hcap : H ≤ childQ lam/2) (hrho1 : rho ≤ 1)
    (hu : 0 < u) (huH : u ≤ H) :
    (∀ y : ℝ, parentMinimum i lam H rho u ≤ parentPayment i lam H rho u y) ∧
    ∃ y : ℝ, parentPayment i lam H rho u y = parentMinimum i lam H rho u := by
  have hl := (row_activity_bounds hrow).1
  have hc := half_child_bounds hl hu (huH.trans hcap)
  have hdelta := (all_rows_fields_positive hrow).2.2.2
  have hd := parentD_gt_fortieth hrow hH hcap hrho1
  have hJ := hc.2.2.2.1
  have hdpos : 0 < parentD i lam H rho := by linarith
  have hG : 0 < delta i lam+parentD i lam H rho*childJ lam u := by positivity
  refine ⟨fun y => responseMinimum_le _ _ _ _ _ _ _ _ hdelta hc.2.2.2.1 hG, ?_⟩
  exact ⟨responseMinimizer (parentC i lam H rho) (parentD i lam H rho) (delta i lam)
    (messageRatio u) (childJ lam u), responseMinimum_attained _ _ _ _ _ _ _ hdelta hc.2.2.2.1 hG⟩

/-- Literal current Theorem 5.24 with the closed child and actual leaf response. -/
theorem half_light_parent_mixed {i : Fin 4} {lam H rho u y : ℝ}
    (hrow : inRow i lam) (hH : 0 < H) (hcap : H ≤ childQ lam/2)
    (hrho : rhoMin lam (halfParent lam H) ≤ rho) (hrho1 : rho ≤ 1)
    (hu : 0 ≤ u) (huH : u ≤ H) (hleaf : u=0 → y=1) :
    1/40 < parentD i lam H rho ∧
    (∀ v : ℝ, 0 < v → v ≤ H →
      0 < deriv (parentMinimum i lam H rho) v / deriv messageRatio v) ∧
    parentMinimum i lam H rho H ≤ parentMinimum i lam H rho u ∧
    parentMinimum i lam H rho u ≤ parentPayment i lam H rho u y := by
  exact ⟨parentD_gt_fortieth hrow hH hcap hrho1,
    fun v hv hvH => parent_minimum_derivative_ratio_pos hrow hH hcap hrho hrho1 hv hvH,
    parentMinimum_at_H_le hrow hH hcap hrho hrho1 hu huH,
    parentMinimum_le_payment hrow hH hcap hrho1 hu huH hleaf⟩

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentMinimum_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentMinimum_hasDerivAt
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentMinimum_zero
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentMinimum_zero
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentMinimum_continuousOn
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentMinimum_continuousOn
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentMinimum_antitoneOn
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentMinimum_antitoneOn
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentMinimum_at_H_le
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentMinimum_at_H_le
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentMinimum_le_payment
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentMinimum_le_payment
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.half_light_parent_mixed
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.half_light_parent_mixed

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentMinimum_is_minimum
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentMinimum_is_minimum
