module

public import F4Heavy.Analysis.TailRayE202
public import F4Heavy.Analysis.TailDomain

public import F4Heavy.Analysis.TailIdentityCoordinates

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

def tail_guard_E2_02_identity_left_expression : PolynomialExpr :=
  (.mul (.add reflectTailE2Lo (.mul (.const ⟨(-1), 1⟩) (.const ⟨(3), 2⟩))) (.row tail_ray_E2_02_denominator_power))

def tail_guard_E2_02_identity_right_expression : PolynomialExpr :=
  (.row tail_ray_E2_02_numerator_power)

set_option maxRecDepth 4096 in
theorem tail_guard_E2_02_identity_coefficients_check : PolynomialExpr.check tail_guard_E2_02_identity_left_expression tail_guard_E2_02_identity_right_expression = true := by
  decide +kernel

theorem tail_guard_E2_02_identity (lam : ℝ) (hr : InRow .E2 lam) :
    tailGuard .E2 lam 2 = realHorner (tail_ray_E2_02_numerator_power.map fractionValue) lam /
      realHorner (tail_ray_E2_02_denominator_power.map fractionValue) lam := by
  have hp := PolynomialExpr.check_sound _ _ tail_guard_E2_02_identity_coefficients_check 0 lam
  simp only [tail_guard_E2_02_identity_left_expression, tail_guard_E2_02_identity_right_expression, PolynomialExpr.value, PolynomialExpr.row_value, reflectTailE2Lo_value, fractionValue, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_one, Nat.cast_ofNat, div_one, sub_eq_add_neg, neg_mul, one_mul] at hp
  have hd := ne_of_gt (tail_ray_E2_02_denominator_positive lam hr)
  apply (eq_div_iff hd).mpr
  simpa only [tailGuard, sub_eq_add_neg, neg_mul] using hp


theorem tail_guard_E2_02_positive (lam : ℝ) (hr : InRow .E2 lam) : 0 < tailGuard .E2 lam 2 := by
  rw [tail_guard_E2_02_identity lam hr]
  exact div_pos (tail_ray_E2_02_numerator_positive lam hr) (tail_ray_E2_02_denominator_positive lam hr)

end F4Heavy.Analysis
