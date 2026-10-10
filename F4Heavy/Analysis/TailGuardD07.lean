module

public import F4Heavy.Analysis.TailRayD07
public import F4Heavy.Analysis.TailDomain

public import F4Heavy.Analysis.TailExtraCoordinates

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

def tail_guard_D_07_identity_left_expression : PolynomialExpr :=
  (.mul (.add (.add (.add (.mul (.mul (.const ⟨(8), 1⟩) (.add (.const ⟨(1), 1⟩) .parent)) (.add (.add (.pow (.add (.mul reflectTailDScale (.add (.const ⟨(1), 1⟩) .parent)) .parent) 2) (.mul (.const ⟨(-1), 1⟩) (.mul .parent (.add (.mul reflectTailDScale (.add (.const ⟨(1), 1⟩) .parent)) .parent)))) (.mul reflectTailDGamma (.add (.add (.pow (.add (.mul reflectTailDScale (.add (.const ⟨(1), 1⟩) .parent)) .parent) 2) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul .parent (.add (.mul reflectTailDScale (.add (.const ⟨(1), 1⟩) .parent)) .parent)) (.const ⟨(1), 2⟩)))) (.mul (.const ⟨(-1), 1⟩) (.mul (.pow .parent 2) (.const ⟨(1), 12⟩))))))) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.mul (.const ⟨(3), 1⟩) reflectTailExtraDPrice) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(2), 1⟩) .parent))) (.add (.mul reflectTailDScale (.add (.const ⟨(1), 1⟩) .parent)) .parent)))) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.mul (.mul (.const ⟨(8), 1⟩) (.add (.const ⟨(1), 1⟩) .parent)) .parent) reflectTailDHi) (.add (.mul (.add (.const ⟨(1), 1⟩) (.mul reflectTailDGamma (.const ⟨(1), 2⟩))) (.add (.mul reflectTailDScale (.add (.const ⟨(1), 1⟩) .parent)) .parent)) (.mul (.mul reflectTailDGamma .parent) (.const ⟨(1), 6⟩)))))) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.mul (.mul (.const ⟨(3), 1⟩) reflectTailExtraDPrice) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(2), 1⟩) .parent))) reflectTailDHi) (.add (.mul reflectTailDScale (.add (.const ⟨(1), 1⟩) .parent)) .parent)))) (.row tail_ray_D_07_denominator_power))

def tail_guard_D_07_identity_right_expression : PolynomialExpr :=
  (.mul (.row tail_ray_D_07_numerator_power) (.mul (.mul (.const ⟨(8), 1⟩) (.add (.const ⟨(1), 1⟩) .parent)) (.pow (.add (.mul reflectTailDScale (.add (.const ⟨(1), 1⟩) .parent)) .parent) 2)))

set_option maxRecDepth 4096 in
theorem tail_guard_D_07_identity_coefficients_check : PolynomialExpr.check tail_guard_D_07_identity_left_expression tail_guard_D_07_identity_right_expression = true := by
  decide +kernel

theorem tail_guard_D_07_identity (lam : ℝ) (hr : InRow .D lam) :
    tailGuard .D lam 7 = realHorner (tail_ray_D_07_numerator_power.map fractionValue) lam /
      realHorner (tail_ray_D_07_denominator_power.map fractionValue) lam := by
  have hp := PolynomialExpr.check_sound _ _ tail_guard_D_07_identity_coefficients_check 0 lam
  simp only [tail_guard_D_07_identity_left_expression, tail_guard_D_07_identity_right_expression, PolynomialExpr.value, PolynomialExpr.row_value, reflectTailDGamma_value, reflectTailDHi_value, reflectTailDScale_value, reflectTailExtraDPrice_value, fractionValue, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_one, Nat.cast_ofNat, div_one, sub_eq_add_neg, neg_mul, one_mul] at hp
  have hd := ne_of_gt (tail_ray_D_07_denominator_positive lam hr)
  have hl := inRow_activity_pos .D lam hr
  have hs := tail_scale_positive .D
  have hden : tailMiddleDenominator .D lam 7 ≠ 0 := by
    simp only [tailMiddleDenominator, tailProbabilityDen]
    positivity
  rw [tail_middle_quotient .D lam hl 7 (by omega) (by omega)]
  apply (div_eq_div_iff hden hd).mpr
  simpa only [tailMiddleNumerator, tailMiddleDenominator, tailProbabilityDen,
    tailP1Numerator, tailANumerator, tailLNumerator,
    sub_eq_add_neg, neg_mul, one_mul, div_eq_mul_inv, mul_assoc] using hp


theorem tail_guard_D_07_positive (lam : ℝ) (hr : InRow .D lam) : 0 < tailGuard .D lam 7 := by
  rw [tail_guard_D_07_identity lam hr]
  exact div_pos (tail_ray_D_07_numerator_positive lam hr) (tail_ray_D_07_denominator_positive lam hr)

end F4Heavy.Analysis
