module

public import F4Heavy.Analysis.CapBernstein
public import F4Heavy.Analysis.CapSlopeUpper
public import F4Heavy.Finite.CapSlopes

public import F4Heavy.Analysis.CapPolynomialForms

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

theorem cap_slope_D_4_polynomial_positive (lam : ℝ) (hr : InRow .D lam) :
    0 < realHorner (cap_slope_D_4_numerator.map fractionValue) lam := by
  apply cap_bernstein_positive_values cap_slope_D_4_numerator cap_slope_D_4_controls ⟨4, 5⟩ ⟨13, 10⟩ 6 lam
  · norm_num [cap_slope_D_4_numerator]
  · norm_num
  · norm_num
  · norm_num [cap_slope_D_4_numerator]
  · norm_num [fractionValue]
  · simpa [InRow, rowData, fractionValue] using hr.1
  · simpa [InRow, rowData, fractionValue] using hr.2
  · exact cap_slope_D_4_reconstruct
  · intro c hc
    simp only [cap_slope_D_4_controls, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lt_trans (by norm_num [fractionValue]) (fraction_lt_sound _ _ cap_slope_D_4_coefficient_0)
    · exact lt_trans (by norm_num [fractionValue]) (fraction_lt_sound _ _ cap_slope_D_4_coefficient_1)
    · exact lt_trans (by norm_num [fractionValue]) (fraction_lt_sound _ _ cap_slope_D_4_coefficient_2)
    · exact lt_trans (by norm_num [fractionValue]) (fraction_lt_sound _ _ cap_slope_D_4_coefficient_3)
    · exact lt_trans (by norm_num [fractionValue]) (fraction_lt_sound _ _ cap_slope_D_4_coefficient_4)
    · exact lt_trans (by norm_num [fractionValue]) (fraction_lt_sound _ _ cap_slope_D_4_coefficient_5)
    · exact lt_trans (by norm_num [fractionValue]) (fraction_lt_sound _ _ cap_slope_D_4_coefficient_6)

def cap_slope_D_4_denominator_factor_left_expression : PolynomialExpr :=
  (.row cap_slope_D_4_denominator)

def cap_slope_D_4_denominator_factor_right_expression : PolynomialExpr :=
  (.mul (.mul (.mul (.mul (.const ⟨(10555311626649600), 1⟩) (.add (.const ⟨(2), 1⟩) .parent)) (.pow (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(2), 1⟩) .parent)) 2)) (.add (.mul (.const ⟨(3), 1⟩) .parent) (.const ⟨(4), 1⟩))) (.add reflectTailDGamma (.mul (.const ⟨(-1), 1⟩) reflectTailDDelta)))

set_option maxRecDepth 4096 in
theorem cap_slope_D_4_denominator_factor_coefficients_check : PolynomialExpr.check cap_slope_D_4_denominator_factor_left_expression cap_slope_D_4_denominator_factor_right_expression = true := by
  decide +kernel

theorem cap_slope_D_4_denominator_factor (lam : ℝ) :
    realHorner (cap_slope_D_4_denominator.map fractionValue) lam =
      (10555311626649600/1 : ℝ) * (2 + lam) * (1 + 2 * lam) ^ 2 * (3 * lam + 4) * (gamma .D lam - delta .D lam) := by
  have hp := PolynomialExpr.check_sound _ _ cap_slope_D_4_denominator_factor_coefficients_check 0 lam
  simp only [cap_slope_D_4_denominator_factor_left_expression, cap_slope_D_4_denominator_factor_right_expression, PolynomialExpr.value, PolynomialExpr.row_value, reflectTailDDelta_value, reflectTailDGamma_value, fractionValue, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_one, Nat.cast_ofNat, div_one, sub_eq_add_neg, neg_mul, one_mul] at hp
  simpa only [div_one,sub_eq_add_neg,neg_mul,one_mul,mul_one] using hp


theorem cap_slope_D_4_denominator_positive (lam : ℝ) (hr : InRow .D lam) :
    0 < realHorner (cap_slope_D_4_denominator.map fractionValue) lam := by
  rw [cap_slope_D_4_denominator_factor]
  have hl := inRow_activity_pos .D lam hr
  have hG := cap_gamma_minus_delta_pos .D lam hr
  positivity

def cap_slope_D_4_identity_left_expression : PolynomialExpr :=
  (.mul (.add (.add (.add (.add (.add (.mul (.mul (.mul (.const ⟨(600), 1⟩) (.pow (.add reflectTailDGamma (.mul (.const ⟨(-1), 1⟩) reflectTailDDelta)) 2)) (.mul (.const ⟨(2), 1⟩) (.add .parent (.const ⟨(2), 1⟩)))) (.pow (.mul (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(2), 1⟩) .parent)) (.add (.const ⟨(2), 1⟩) .parent)) 2)) (.mul (.mul (.mul (.mul (.const ⟨(600), 1⟩) (.add (.add (.const ⟨(2), 1⟩) .parent) (.mul (.mul (.const ⟨(2), 1⟩) reflectTailDGamma) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(2), 1⟩) .parent))))) (.mul (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(2), 1⟩) .parent)) (.add (.const ⟨(2), 1⟩) .parent))) (.add reflectTailDGamma (.mul (.const ⟨(-1), 1⟩) reflectTailDDelta))) (.add (.mul (.const ⟨(3), 1⟩) .parent) (.const ⟨(4), 1⟩)))) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.mul (.mul (.const ⟨(300), 1⟩) (.add reflectTailDAlpha reflectTailDBeta)) (.pow (.mul (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(2), 1⟩) .parent)) (.add (.const ⟨(2), 1⟩) .parent)) 2)) (.add reflectTailDGamma (.mul (.const ⟨(-1), 1⟩) reflectTailDDelta))) (.add (.mul (.const ⟨(3), 1⟩) .parent) (.const ⟨(4), 1⟩))))) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.mul (.const ⟨(3), 1⟩) (.pow (.mul (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(2), 1⟩) .parent)) (.add (.const ⟨(2), 1⟩) .parent)) 2)) (.add reflectTailDGamma (.mul (.const ⟨(-1), 1⟩) reflectTailDDelta))) (.add (.mul (.const ⟨(3), 1⟩) .parent) (.const ⟨(4), 1⟩))))) (.mul (.mul (.mul (.mul (.const ⟨(650), 1⟩) (.mul (.const ⟨(2), 1⟩) (.add .parent (.const ⟨(2), 1⟩)))) (.add (.add (.const ⟨(2), 1⟩) .parent) (.mul (.mul (.const ⟨(2), 1⟩) reflectTailDGamma) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(2), 1⟩) .parent))))) (.mul (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(2), 1⟩) .parent)) (.add (.const ⟨(2), 1⟩) .parent))) (.add reflectTailDGamma (.mul (.const ⟨(-1), 1⟩) reflectTailDDelta)))) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.mul (.const ⟨(240), 1⟩) (.mul (.const ⟨(2), 1⟩) (.add .parent (.const ⟨(2), 1⟩)))) .parent) (.pow (.add (.add (.const ⟨(2), 1⟩) .parent) (.mul (.mul (.const ⟨(2), 1⟩) reflectTailDGamma) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(2), 1⟩) .parent)))) 2)))) (.row cap_slope_D_4_denominator))

def cap_slope_D_4_identity_right_expression : PolynomialExpr :=
  (.mul (.row cap_slope_D_4_numerator) (.mul (.mul (.mul (.const ⟨(300), 1⟩) (.pow (.mul (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(2), 1⟩) .parent)) (.add (.const ⟨(2), 1⟩) .parent)) 2)) (.add reflectTailDGamma (.mul (.const ⟨(-1), 1⟩) reflectTailDDelta))) (.add (.mul (.const ⟨(3), 1⟩) .parent) (.const ⟨(4), 1⟩))))

set_option maxRecDepth 4096 in
theorem cap_slope_D_4_identity_coefficients_check : PolynomialExpr.check cap_slope_D_4_identity_left_expression cap_slope_D_4_identity_right_expression = true := by
  decide +kernel

theorem cap_slope_D_4_identity (lam : ℝ) (hr : InRow .D lam) :
    capLambda .D lam (2 * (lam + 2) / (3 * lam + 4)) - 1 / 100 =
      realHorner (cap_slope_D_4_numerator.map fractionValue) lam /
        realHorner (cap_slope_D_4_denominator.map fractionValue) lam := by
  have hp := PolynomialExpr.check_sound _ _ cap_slope_D_4_identity_coefficients_check 0 lam
  simp only [cap_slope_D_4_identity_left_expression, cap_slope_D_4_identity_right_expression, PolynomialExpr.value, PolynomialExpr.row_value, reflectTailDAlpha_value, reflectTailDBeta_value, reflectTailDDelta_value, reflectTailDGamma_value, fractionValue, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_one, Nat.cast_ofNat, div_one, sub_eq_add_neg, neg_mul, one_mul] at hp
  have hl := inRow_activity_pos .D lam hr
  have hd := ne_of_gt (cap_slope_D_4_denominator_positive lam hr)
  have hG := cap_gamma_minus_delta_pos .D lam hr
  have hden : capReflectLambdaD .D lam (3*lam+4) ≠ 0 := by
    try simp only [capReflectLambdaD,capReflectMD,capReflectElevenD,capReflectD13D,
      reduceCtorEq,ite_true,ite_false]
    positivity
  have hq := cap_lambda_reflect_quotient .D lam (2*(lam+2)) (3*lam+4) hl (ne_of_gt hG) (by positivity)
  try simp only [div_one] at hq
  rw [hq]
  apply (div_eq_div_iff hden hd).mpr
  simpa only [capReflectLambdaN,capReflectLambdaD,capReflectMN,capReflectMD,
    capReflectUN,capReflectSixN,capReflectSevenN,capReflectElevenN,capReflectElevenD,
    capReflectD13N,capReflectD13D,reduceCtorEq,ite_true,ite_false,
    sub_eq_add_neg,neg_mul,one_mul,mul_one,one_pow,div_eq_mul_inv,mul_assoc] using hp


theorem cap_slope_D_4_positive (lam : ℝ) (hr : InRow .D lam) :
    0 < capLambda .D lam (2 * (lam + 2) / (3 * lam + 4)) - 1 / 100 := by
  rw [cap_slope_D_4_identity lam hr]
  exact div_pos (cap_slope_D_4_polynomial_positive lam hr) (cap_slope_D_4_denominator_positive lam hr)

end F4Heavy.Analysis
