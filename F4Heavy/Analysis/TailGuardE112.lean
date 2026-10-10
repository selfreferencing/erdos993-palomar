module

public import F4Heavy.Analysis.TailRayE112
public import F4Heavy.Analysis.TailDomain

public import F4Heavy.Analysis.TailExtraCoordinates

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

def tail_guard_E1_12_identity_left_expression : PolynomialExpr :=
  (.mul (.add (.mul (.const ⟨(2), 1⟩) (.add (.add (.pow (.add (.mul reflectTailE1Scale (.add (.const ⟨(1), 1⟩) .parent)) .parent) 2) (.mul (.const ⟨(-1), 1⟩) (.mul .parent (.add (.mul reflectTailE1Scale (.add (.const ⟨(1), 1⟩) .parent)) .parent)))) (.mul reflectTailE1Gamma (.add (.add (.pow (.add (.mul reflectTailE1Scale (.add (.const ⟨(1), 1⟩) .parent)) .parent) 2) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul .parent (.add (.mul reflectTailE1Scale (.add (.const ⟨(1), 1⟩) .parent)) .parent)) (.const ⟨(1), 2⟩)))) (.mul (.const ⟨(-1), 1⟩) (.mul (.pow .parent 2) (.const ⟨(1), 12⟩))))))) (.mul (.const ⟨(-1), 1⟩) (.mul (.add reflectTailE1Alpha reflectTailE1Beta) (.pow (.add (.mul reflectTailE1Scale (.add (.const ⟨(1), 1⟩) .parent)) .parent) 2)))) (.row tail_ray_E1_12_denominator_power))

def tail_guard_E1_12_identity_right_expression : PolynomialExpr :=
  (.mul (.row tail_ray_E1_12_numerator_power) (.pow (.add (.mul reflectTailE1Scale (.add (.const ⟨(1), 1⟩) .parent)) .parent) 2))

set_option maxRecDepth 4096 in
theorem tail_guard_E1_12_identity_coefficients_check : PolynomialExpr.check tail_guard_E1_12_identity_left_expression tail_guard_E1_12_identity_right_expression = true := by
  decide +kernel

theorem tail_guard_E1_12_identity (lam : ℝ) (hr : InRow .E1 lam) :
    tailGuard .E1 lam 12 = realHorner (tail_ray_E1_12_numerator_power.map fractionValue) lam /
      realHorner (tail_ray_E1_12_denominator_power.map fractionValue) lam := by
  have hp := PolynomialExpr.check_sound _ _ tail_guard_E1_12_identity_coefficients_check 0 lam
  simp only [tail_guard_E1_12_identity_left_expression, tail_guard_E1_12_identity_right_expression, PolynomialExpr.value, PolynomialExpr.row_value, reflectTailE1Alpha_value, reflectTailE1Beta_value, reflectTailE1Gamma_value, reflectTailE1Scale_value, fractionValue, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_one, Nat.cast_ofNat, div_one, sub_eq_add_neg, neg_mul, one_mul] at hp
  have hd := ne_of_gt (tail_ray_E1_12_denominator_positive lam hr)
  have hl := inRow_activity_pos .E1 lam hr
  have hs := tail_scale_positive .E1
  have hden : tailMiddleDenominator .E1 lam 12 ≠ 0 := by
    simp only [tailMiddleDenominator, tailProbabilityDen]
    positivity
  rw [tail_middle_quotient .E1 lam hl 12 (by omega) (by omega)]
  apply (div_eq_div_iff hden hd).mpr
  simpa only [tailMiddleNumerator, tailMiddleDenominator, tailProbabilityDen,
    tailP1Numerator, tailANumerator, tailLNumerator,
    sub_eq_add_neg, neg_mul, one_mul, div_eq_mul_inv, mul_assoc] using hp


theorem tail_guard_E1_12_positive (lam : ℝ) (hr : InRow .E1 lam) : 0 < tailGuard .E1 lam 12 := by
  rw [tail_guard_E1_12_identity lam hr]
  exact div_pos (tail_ray_E1_12_numerator_positive lam hr) (tail_ray_E1_12_denominator_positive lam hr)

end F4Heavy.Analysis
