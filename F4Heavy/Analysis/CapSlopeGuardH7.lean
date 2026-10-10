module

public import F4Heavy.Analysis.CapBernstein
public import F4Heavy.Analysis.CapSlopeUpper
public import F4Heavy.Finite.CapSlopes

public import F4Heavy.Analysis.CapPolynomialForms

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

theorem cap_slope_H_7_polynomial_positive (lam : ℝ) (hr : InRow .H lam) :
    0 < realHorner (cap_slope_H_7_numerator.map fractionValue) lam := by
  apply cap_bernstein_positive_values cap_slope_H_7_numerator cap_slope_H_7_controls ⟨7, 4⟩ ⟨7, 3⟩ 3 lam
  · norm_num [cap_slope_H_7_numerator]
  · norm_num
  · norm_num
  · norm_num [cap_slope_H_7_numerator]
  · norm_num [fractionValue]
  · simpa [InRow, rowData, fractionValue] using hr.1
  · simpa [InRow, rowData, fractionValue] using hr.2
  · exact cap_slope_H_7_reconstruct
  · intro c hc
    simp only [cap_slope_H_7_controls, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact lt_trans (by norm_num [fractionValue]) (fraction_lt_sound _ _ cap_slope_H_7_coefficient_0)
    · exact lt_trans (by norm_num [fractionValue]) (fraction_lt_sound _ _ cap_slope_H_7_coefficient_1)
    · exact lt_trans (by norm_num [fractionValue]) (fraction_lt_sound _ _ cap_slope_H_7_coefficient_2)
    · exact lt_trans (by norm_num [fractionValue]) (fraction_lt_sound _ _ cap_slope_H_7_coefficient_3)

def cap_slope_H_7_denominator_factor_left_expression : PolynomialExpr :=
  (.row cap_slope_H_7_denominator)

def cap_slope_H_7_denominator_factor_right_expression : PolynomialExpr :=
  (.mul (.mul (.const ⟨(33554432), 1⟩) .parent) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(2), 1⟩) .parent)))

set_option maxRecDepth 4096 in
theorem cap_slope_H_7_denominator_factor_coefficients_check : PolynomialExpr.check cap_slope_H_7_denominator_factor_left_expression cap_slope_H_7_denominator_factor_right_expression = true := by
  decide +kernel

theorem cap_slope_H_7_denominator_factor (lam : ℝ) :
    realHorner (cap_slope_H_7_denominator.map fractionValue) lam =
      (33554432/1 : ℝ) * lam * (1 + 2 * lam) := by
  have hp := PolynomialExpr.check_sound _ _ cap_slope_H_7_denominator_factor_coefficients_check 0 lam
  simp only [cap_slope_H_7_denominator_factor_left_expression, cap_slope_H_7_denominator_factor_right_expression, PolynomialExpr.value, PolynomialExpr.row_value, fractionValue, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_one, Nat.cast_ofNat, div_one, sub_eq_add_neg, neg_mul, one_mul] at hp
  simpa only [div_one,sub_eq_add_neg,neg_mul,one_mul,mul_one] using hp


theorem cap_slope_H_7_denominator_positive (lam : ℝ) (hr : InRow .H lam) :
    0 < realHorner (cap_slope_H_7_denominator.map fractionValue) lam := by
  rw [cap_slope_H_7_denominator_factor]
  have hl := inRow_activity_pos .H lam hr
  have hG := cap_gamma_minus_delta_pos .H lam hr
  positivity

def cap_slope_H_7_identity_left_expression : PolynomialExpr :=
  (.mul (.add (.mul (.add (.add (.mul (.const ⟨(2), 1⟩) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(2), 1⟩) .parent))) (.mul (.const ⟨(-1), 1⟩) (.mul (.const ⟨(2), 1⟩) .parent))) (.mul reflectTailHGamma (.add (.mul (.const ⟨(2), 1⟩) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(2), 1⟩) .parent))) (.mul (.const ⟨(-1), 1⟩) .parent)))) .parent) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.mul (.const ⟨(2), 1⟩) (.add reflectTailHGamma (.mul (.const ⟨(-1), 1⟩) reflectTailHDelta))) (.add (.const ⟨(1), 1⟩) .parent)) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(2), 1⟩) .parent))))) (.row cap_slope_H_7_denominator))

def cap_slope_H_7_identity_right_expression : PolynomialExpr :=
  (.mul (.row cap_slope_H_7_numerator) (.mul (.mul (.const ⟨(2), 1⟩) .parent) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(2), 1⟩) .parent))))

set_option maxRecDepth 4096 in
theorem cap_slope_H_7_identity_coefficients_check : PolynomialExpr.check cap_slope_H_7_identity_left_expression cap_slope_H_7_identity_right_expression = true := by
  decide +kernel

theorem cap_slope_H_7_identity (lam : ℝ) (hr : InRow .H lam) :
    capParentU .H lam - (gamma .H lam - delta .H lam) * (1 + lam) / lam =
      realHorner (cap_slope_H_7_numerator.map fractionValue) lam /
        realHorner (cap_slope_H_7_denominator.map fractionValue) lam := by
  have hp := PolynomialExpr.check_sound _ _ cap_slope_H_7_identity_coefficients_check 0 lam
  simp only [cap_slope_H_7_identity_left_expression, cap_slope_H_7_identity_right_expression, PolynomialExpr.value, PolynomialExpr.row_value, reflectTailHDelta_value, reflectTailHGamma_value, fractionValue, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_one, Nat.cast_ofNat, div_one, sub_eq_add_neg, neg_mul, one_mul] at hp
  have hl := inRow_activity_pos .H lam hr
  have hd := ne_of_gt (cap_slope_H_7_denominator_positive lam hr)
  have hden : 2*lam*(1+2*lam) ≠ 0 := by
    try simp only [capReflectLambdaD,capReflectMD,capReflectElevenD,capReflectD13D,
      reduceCtorEq,ite_true,ite_false]
    positivity
  have hq := cap_seven_reflect_quotient .H lam hl
  try simp only [div_one] at hq
  rw [hq]
  apply (div_eq_div_iff hden hd).mpr
  simpa only [capReflectLambdaN,capReflectLambdaD,capReflectMN,capReflectMD,
    capReflectUN,capReflectSixN,capReflectSevenN,capReflectElevenN,capReflectElevenD,
    capReflectD13N,capReflectD13D,reduceCtorEq,ite_true,ite_false,
    sub_eq_add_neg,neg_mul,one_mul,mul_one,one_pow,div_eq_mul_inv,mul_assoc] using hp


theorem cap_slope_H_7_positive (lam : ℝ) (hr : InRow .H lam) :
    0 < capParentU .H lam - (gamma .H lam - delta .H lam) * (1 + lam) / lam := by
  rw [cap_slope_H_7_identity lam hr]
  exact div_pos (cap_slope_H_7_polynomial_positive lam hr) (cap_slope_H_7_denominator_positive lam hr)

end F4Heavy.Analysis
