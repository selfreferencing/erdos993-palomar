module

public import F4Heavy.Analysis.TailRayE210
public import F4Heavy.Analysis.TailDomain

public import F4Heavy.Analysis.TailExtraCoordinates

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

def tail_guard_E2_10_identity_left_expression : PolynomialExpr :=
  (.mul (.add (.add (.mul (.mul (.const ⟨(2), 1⟩) (.add (.add (.add (.const ⟨(2), 1⟩) (.mul (.const ⟨(2), 1⟩) reflectTailE2Gamma)) (.mul (.const ⟨(-1), 1⟩) reflectTailE2Alpha)) (.mul (.const ⟨(-1), 1⟩) reflectTailE2Beta))) (.pow (.add (.mul reflectTailE2Scale (.add (.const ⟨(1), 1⟩) .parent)) .parent) 2)) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.mul (.const ⟨(4), 1⟩) (.add (.const ⟨(2), 1⟩) reflectTailE2Gamma)) .parent) (.add (.mul reflectTailE2Scale (.add (.const ⟨(1), 1⟩) .parent)) .parent)))) (.mul (.const ⟨(-1), 1⟩) (.mul reflectTailE2Gamma (.pow .parent 2)))) (.row tail_ray_E2_10_denominator_power))

def tail_guard_E2_10_identity_right_expression : PolynomialExpr :=
  (.mul (.row tail_ray_E2_10_numerator_power) (.mul (.const ⟨(2), 1⟩) (.pow (.add (.mul reflectTailE2Scale (.add (.const ⟨(1), 1⟩) .parent)) .parent) 2)))

set_option maxRecDepth 4096 in
theorem tail_guard_E2_10_identity_coefficients_check : PolynomialExpr.check tail_guard_E2_10_identity_left_expression tail_guard_E2_10_identity_right_expression = true := by
  decide +kernel

theorem tail_guard_E2_10_identity (lam : ℝ) (hr : InRow .E2 lam) :
    tailGuard .E2 lam 10 = realHorner (tail_ray_E2_10_numerator_power.map fractionValue) lam /
      realHorner (tail_ray_E2_10_denominator_power.map fractionValue) lam := by
  have hp := PolynomialExpr.check_sound _ _ tail_guard_E2_10_identity_coefficients_check 0 lam
  simp only [tail_guard_E2_10_identity_left_expression, tail_guard_E2_10_identity_right_expression, PolynomialExpr.value, PolynomialExpr.row_value, reflectTailE2Alpha_value, reflectTailE2Beta_value, reflectTailE2Gamma_value, reflectTailE2Scale_value, fractionValue, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_one, Nat.cast_ofNat, div_one, sub_eq_add_neg, neg_mul, one_mul] at hp
  have hd := ne_of_gt (tail_ray_E2_10_denominator_positive lam hr)
  have hl := inRow_activity_pos .E2 lam hr
  have hs := tail_scale_positive .E2
  have hden : tailMiddleDenominator .E2 lam 10 ≠ 0 := by
    simp only [tailMiddleDenominator, tailProbabilityDen]
    positivity
  rw [tail_middle_quotient .E2 lam hl 10 (by omega) (by omega)]
  apply (div_eq_div_iff hden hd).mpr
  simpa only [tailMiddleNumerator, tailMiddleDenominator, tailProbabilityDen,
    tailP1Numerator, tailANumerator, tailLNumerator,
    sub_eq_add_neg, neg_mul, one_mul, div_eq_mul_inv, mul_assoc] using hp


theorem tail_guard_E2_10_positive (lam : ℝ) (hr : InRow .E2 lam) : 0 < tailGuard .E2 lam 10 := by
  rw [tail_guard_E2_10_identity lam hr]
  exact div_pos (tail_ray_E2_10_numerator_positive lam hr) (tail_ray_E2_10_denominator_positive lam hr)

end F4Heavy.Analysis
