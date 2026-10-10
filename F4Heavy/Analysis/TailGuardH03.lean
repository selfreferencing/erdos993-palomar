module

public import F4Heavy.Analysis.TailRayH03
public import F4Heavy.Analysis.TailDomain

public import F4Heavy.Analysis.TailIdentityCoordinates

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

def tail_guard_H_03_identity_left_expression : PolynomialExpr :=
  (.mul (.add (.add reflectTailHAlpha reflectTailHBeta) (.mul (.const ⟨(-1), 1⟩) (.mul (.const ⟨(2), 1⟩) reflectTailHGamma))) (.row tail_ray_H_03_denominator_power))

def tail_guard_H_03_identity_right_expression : PolynomialExpr :=
  (.row tail_ray_H_03_numerator_power)

set_option maxRecDepth 4096 in
theorem tail_guard_H_03_identity_coefficients_check : PolynomialExpr.check tail_guard_H_03_identity_left_expression tail_guard_H_03_identity_right_expression = true := by
  decide +kernel

theorem tail_guard_H_03_identity (lam : ℝ) (hr : InRow .H lam) :
    tailGuard .H lam 3 = realHorner (tail_ray_H_03_numerator_power.map fractionValue) lam /
      realHorner (tail_ray_H_03_denominator_power.map fractionValue) lam := by
  have hp := PolynomialExpr.check_sound _ _ tail_guard_H_03_identity_coefficients_check 0 lam
  simp only [tail_guard_H_03_identity_left_expression, tail_guard_H_03_identity_right_expression, PolynomialExpr.value, PolynomialExpr.row_value, reflectTailHAlpha_value, reflectTailHBeta_value, reflectTailHGamma_value, fractionValue, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_one, Nat.cast_ofNat, div_one, sub_eq_add_neg, neg_mul, one_mul] at hp
  have hd := ne_of_gt (tail_ray_H_03_denominator_positive lam hr)
  apply (eq_div_iff hd).mpr
  simpa only [tailGuard, sub_eq_add_neg, neg_mul] using hp


theorem tail_guard_H_03_positive (lam : ℝ) (hr : InRow .H lam) : 0 < tailGuard .H lam 3 := by
  rw [tail_guard_H_03_identity lam hr]
  exact div_pos (tail_ray_H_03_numerator_positive lam hr) (tail_ray_H_03_denominator_positive lam hr)

end F4Heavy.Analysis
