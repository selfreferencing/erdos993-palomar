module

public import F4Heavy.Analysis.CapBernstein
public import F4Heavy.Analysis.CapSlopeUpper
public import F4Heavy.Finite.CapSlopes

public import F4Heavy.Analysis.CapPolynomialForms

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

theorem cap_slope_H_6_polynomial_positive (lam : ℝ) (hr : InRow .H lam) :
    0 < realHorner (cap_slope_H_6_numerator.map fractionValue) lam := by
  apply cap_bernstein_positive_values cap_slope_H_6_numerator cap_slope_H_6_controls ⟨7, 4⟩ ⟨7, 3⟩ 4 lam
  · norm_num [cap_slope_H_6_numerator]
  · norm_num
  · norm_num
  · norm_num [cap_slope_H_6_numerator]
  · norm_num [fractionValue]
  · simpa [InRow, rowData, fractionValue] using hr.1
  · simpa [InRow, rowData, fractionValue] using hr.2
  · exact cap_slope_H_6_reconstruct
  · intro c hc
    simp only [cap_slope_H_6_controls, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    · exact lt_trans (by norm_num [fractionValue]) (fraction_lt_sound _ _ cap_slope_H_6_coefficient_0)
    · exact lt_trans (by norm_num [fractionValue]) (fraction_lt_sound _ _ cap_slope_H_6_coefficient_1)
    · exact lt_trans (by norm_num [fractionValue]) (fraction_lt_sound _ _ cap_slope_H_6_coefficient_2)
    · exact lt_trans (by norm_num [fractionValue]) (fraction_lt_sound _ _ cap_slope_H_6_coefficient_3)
    · exact lt_trans (by norm_num [fractionValue]) (fraction_lt_sound _ _ cap_slope_H_6_coefficient_4)

def cap_slope_H_6_denominator_factor_left_expression : PolynomialExpr :=
  (.row cap_slope_H_6_denominator)

def cap_slope_H_6_denominator_factor_right_expression : PolynomialExpr :=
  (.mul (.mul (.const ⟨(5033164800), 1⟩) .parent) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(2), 1⟩) .parent)))

set_option maxRecDepth 4096 in
theorem cap_slope_H_6_denominator_factor_coefficients_check : PolynomialExpr.check cap_slope_H_6_denominator_factor_left_expression cap_slope_H_6_denominator_factor_right_expression = true := by
  decide +kernel

theorem cap_slope_H_6_denominator_factor (lam : ℝ) :
    realHorner (cap_slope_H_6_denominator.map fractionValue) lam =
      (5033164800/1 : ℝ) * lam * (1 + 2 * lam) := by
  have hp := PolynomialExpr.check_sound _ _ cap_slope_H_6_denominator_factor_coefficients_check 0 lam
  simp only [cap_slope_H_6_denominator_factor_left_expression, cap_slope_H_6_denominator_factor_right_expression, PolynomialExpr.value, PolynomialExpr.row_value, fractionValue, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_one, Nat.cast_ofNat, div_one, sub_eq_add_neg, neg_mul, one_mul] at hp
  simpa only [div_one,sub_eq_add_neg,neg_mul,one_mul,mul_one] using hp


theorem cap_slope_H_6_denominator_positive (lam : ℝ) (hr : InRow .H lam) :
    0 < realHorner (cap_slope_H_6_denominator.map fractionValue) lam := by
  rw [cap_slope_H_6_denominator_factor]
  have hl := inRow_activity_pos .H lam hr
  have hG := cap_gamma_minus_delta_pos .H lam hr
  positivity

def cap_slope_H_6_identity_left_expression : PolynomialExpr :=
  (.mul (.add (.add (.add (.mul (.mul (.const ⟨(600), 1⟩) (.add reflectTailHGamma (.mul (.const ⟨(-1), 1⟩) reflectTailHDelta))) (.pow (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(2), 1⟩) .parent)) 2)) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.mul (.const ⟨(300), 1⟩) (.add reflectTailHAlpha reflectTailHBeta)) .parent) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(2), 1⟩) .parent))))) (.mul (.mul (.mul (.const ⟨(5), 1⟩) (.add (.add (.mul (.const ⟨(2), 1⟩) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(2), 1⟩) .parent))) (.mul (.const ⟨(-1), 1⟩) (.mul (.const ⟨(2), 1⟩) .parent))) (.mul reflectTailHGamma (.add (.mul (.const ⟨(2), 1⟩) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(2), 1⟩) .parent))) (.mul (.const ⟨(-1), 1⟩) .parent))))) .parent) (.add (.const ⟨(41), 1⟩) (.mul (.const ⟨(-1), 1⟩) (.mul (.const ⟨(24), 1⟩) .parent))))) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.const ⟨(3), 1⟩) .parent) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(2), 1⟩) .parent))))) (.row cap_slope_H_6_denominator))

def cap_slope_H_6_identity_right_expression : PolynomialExpr :=
  (.mul (.row cap_slope_H_6_numerator) (.mul (.mul (.const ⟨(300), 1⟩) .parent) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(2), 1⟩) .parent))))

set_option maxRecDepth 4096 in
theorem cap_slope_H_6_identity_coefficients_check : PolynomialExpr.check cap_slope_H_6_identity_left_expression cap_slope_H_6_identity_right_expression = true := by
  decide +kernel

theorem cap_slope_H_6_identity (lam : ℝ) (hr : InRow .H lam) :
    2 * (gamma .H lam - delta .H lam) * (1 + 2 * lam) / lam - alpha .H lam - beta .H lam + 2 * capParentU .H lam * (1 - (19 / 60 + 2 * lam / 5)) - 1 / 100 =
      realHorner (cap_slope_H_6_numerator.map fractionValue) lam /
        realHorner (cap_slope_H_6_denominator.map fractionValue) lam := by
  have hp := PolynomialExpr.check_sound _ _ cap_slope_H_6_identity_coefficients_check 0 lam
  simp only [cap_slope_H_6_identity_left_expression, cap_slope_H_6_identity_right_expression, PolynomialExpr.value, PolynomialExpr.row_value, reflectTailHAlpha_value, reflectTailHBeta_value, reflectTailHDelta_value, reflectTailHGamma_value, fractionValue, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_one, Nat.cast_ofNat, div_one, sub_eq_add_neg, neg_mul, one_mul] at hp
  have hl := inRow_activity_pos .H lam hr
  have hd := ne_of_gt (cap_slope_H_6_denominator_positive lam hr)
  have hden : 300*lam*(1+2*lam) ≠ 0 := by
    try simp only [capReflectLambdaD,capReflectMD,capReflectElevenD,capReflectD13D,
      reduceCtorEq,ite_true,ite_false]
    positivity
  have hq := cap_six_reflect_quotient .H lam hl
  try simp only [div_one] at hq
  rw [hq]
  apply (div_eq_div_iff hden hd).mpr
  simpa only [capReflectLambdaN,capReflectLambdaD,capReflectMN,capReflectMD,
    capReflectUN,capReflectSixN,capReflectSevenN,capReflectElevenN,capReflectElevenD,
    capReflectD13N,capReflectD13D,reduceCtorEq,ite_true,ite_false,
    sub_eq_add_neg,neg_mul,one_mul,mul_one,one_pow,div_eq_mul_inv,mul_assoc] using hp


theorem cap_slope_H_6_positive (lam : ℝ) (hr : InRow .H lam) :
    0 < 2 * (gamma .H lam - delta .H lam) * (1 + 2 * lam) / lam - alpha .H lam - beta .H lam + 2 * capParentU .H lam * (1 - (19 / 60 + 2 * lam / 5)) - 1 / 100 := by
  rw [cap_slope_H_6_identity lam hr]
  exact div_pos (cap_slope_H_6_polynomial_positive lam hr) (cap_slope_H_6_denominator_positive lam hr)

end F4Heavy.Analysis
