module

public import F4Heavy.Analysis.TailRayE109
public import F4Heavy.Analysis.TailDomain

public import F4Heavy.Analysis.TailExtraCoordinates

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

def tail_guard_E1_09_identity_left_expression : PolynomialExpr :=
  (.mul (.add (.add (.add (.mul (.mul (.mul (.add reflectTailE1Gamma (.mul (.const ⟨(-1), 1⟩) reflectTailE1Delta)) reflectTailE1Scale) (.add (.const ⟨(1), 1⟩) .parent)) (.pow (.add (.mul reflectTailE1Scale (.add (.const ⟨(1), 1⟩) .parent)) .parent) 3)) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul .parent (.add (.mul reflectTailE1Scale (.add (.const ⟨(1), 1⟩) .parent)) .parent)) (.add (.add (.pow (.add (.mul reflectTailE1Scale (.add (.const ⟨(1), 1⟩) .parent)) .parent) 2) (.mul (.const ⟨(-1), 1⟩) (.mul .parent (.add (.mul reflectTailE1Scale (.add (.const ⟨(1), 1⟩) .parent)) .parent)))) (.mul reflectTailE1Gamma (.add (.add (.pow (.add (.mul reflectTailE1Scale (.add (.const ⟨(1), 1⟩) .parent)) .parent) 2) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul .parent (.add (.mul reflectTailE1Scale (.add (.const ⟨(1), 1⟩) .parent)) .parent)) (.const ⟨(1), 2⟩)))) (.mul (.const ⟨(-1), 1⟩) (.mul (.pow .parent 2) (.const ⟨(1), 12⟩))))))))) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.mul (.pow .parent 2) reflectTailE1Hi) (.add (.add (.mul reflectTailE1Scale (.add (.const ⟨(1), 1⟩) .parent)) .parent) (.mul (.const ⟨(-1), 1⟩) .parent))) (.add (.mul (.add (.const ⟨(1), 1⟩) (.mul reflectTailE1Gamma (.const ⟨(1), 2⟩))) (.add (.mul reflectTailE1Scale (.add (.const ⟨(1), 1⟩) .parent)) .parent)) (.mul (.mul reflectTailE1Gamma .parent) (.const ⟨(1), 6⟩)))))) (.mul (.mul reflectTailExtraE1Eta .parent) (.pow (.add (.mul reflectTailE1Scale (.add (.const ⟨(1), 1⟩) .parent)) .parent) 3))) (.row tail_ray_E1_09_denominator_power))

def tail_guard_E1_09_identity_right_expression : PolynomialExpr :=
  (.mul (.row tail_ray_E1_09_numerator_power) (.mul .parent (.pow (.add (.mul reflectTailE1Scale (.add (.const ⟨(1), 1⟩) .parent)) .parent) 3)))

set_option maxRecDepth 4096 in
theorem tail_guard_E1_09_identity_coefficients_check : PolynomialExpr.check tail_guard_E1_09_identity_left_expression tail_guard_E1_09_identity_right_expression = true := by
  decide +kernel

theorem tail_guard_E1_09_identity (lam : ℝ) (hr : InRow .E1 lam) :
    tailGuard .E1 lam 9 = realHorner (tail_ray_E1_09_numerator_power.map fractionValue) lam /
      realHorner (tail_ray_E1_09_denominator_power.map fractionValue) lam := by
  have hp := PolynomialExpr.check_sound _ _ tail_guard_E1_09_identity_coefficients_check 0 lam
  simp only [tail_guard_E1_09_identity_left_expression, tail_guard_E1_09_identity_right_expression, PolynomialExpr.value, PolynomialExpr.row_value, reflectTailE1Delta_value, reflectTailE1Gamma_value, reflectTailE1Hi_value, reflectTailE1Scale_value, reflectTailExtraE1Eta_value, fractionValue, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_one, Nat.cast_ofNat, div_one, sub_eq_add_neg, neg_mul, one_mul] at hp
  have hd := ne_of_gt (tail_ray_E1_09_denominator_positive lam hr)
  have hl := inRow_activity_pos .E1 lam hr
  have hs := tail_scale_positive .E1
  have hden : tailMiddleDenominator .E1 lam 9 ≠ 0 := by
    simp only [tailMiddleDenominator, tailProbabilityDen]
    positivity
  rw [tail_middle_quotient .E1 lam hl 9 (by omega) (by omega)]
  apply (div_eq_div_iff hden hd).mpr
  simpa only [tailMiddleNumerator, tailMiddleDenominator, tailProbabilityDen,
    tailP1Numerator, tailANumerator, tailLNumerator,
    sub_eq_add_neg, neg_mul, one_mul, div_eq_mul_inv, mul_assoc] using hp


theorem tail_guard_E1_09_positive (lam : ℝ) (hr : InRow .E1 lam) : 0 < tailGuard .E1 lam 9 := by
  rw [tail_guard_E1_09_identity lam hr]
  exact div_pos (tail_ray_E1_09_numerator_positive lam hr) (tail_ray_E1_09_denominator_positive lam hr)

end F4Heavy.Analysis
