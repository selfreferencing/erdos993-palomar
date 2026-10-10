module

public import F4Heavy.Analysis.CapBernstein
public import F4Heavy.Analysis.CapDLogBounds
public import F4Heavy.Analysis.CapAdverseAlgebra
public import F4Heavy.Finite.CapD13

public import F4Heavy.Analysis.CapPolynomialForms

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

theorem cap_d13_D_13_polynomial_positive (lam : ℝ) (hr : InRow .D lam) :
    0 < realHorner (cap_d13_D_13_numerator.map fractionValue) lam := by
  apply cap_bernstein_positive_values cap_d13_D_13_numerator cap_d13_D_13_controls ⟨4, 5⟩ ⟨13, 10⟩ 7 lam
  · norm_num [cap_d13_D_13_numerator]
  · norm_num
  · norm_num
  · norm_num [cap_d13_D_13_numerator]
  · norm_num [fractionValue]
  · simpa [InRow, rowData, fractionValue] using hr.1
  · simpa [InRow, rowData, fractionValue] using hr.2
  · exact cap_d13_D_13_reconstruct
  · intro c hc
    simp only [cap_d13_D_13_controls, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lt_trans (by norm_num [fractionValue]) (fraction_lt_sound _ _ cap_d13_D_13_coefficient_0)
    · exact lt_trans (by norm_num [fractionValue]) (fraction_lt_sound _ _ cap_d13_D_13_coefficient_1)
    · exact lt_trans (by norm_num [fractionValue]) (fraction_lt_sound _ _ cap_d13_D_13_coefficient_2)
    · exact lt_trans (by norm_num [fractionValue]) (fraction_lt_sound _ _ cap_d13_D_13_coefficient_3)
    · exact lt_trans (by norm_num [fractionValue]) (fraction_lt_sound _ _ cap_d13_D_13_coefficient_4)
    · exact lt_trans (by norm_num [fractionValue]) (fraction_lt_sound _ _ cap_d13_D_13_coefficient_5)
    · exact lt_trans (by norm_num [fractionValue]) (fraction_lt_sound _ _ cap_d13_D_13_coefficient_6)
    · exact lt_trans (by norm_num [fractionValue]) (fraction_lt_sound _ _ cap_d13_D_13_coefficient_7)

def cap_d13_D_13_denominator_factor_left_expression : PolynomialExpr :=
  (.row cap_d13_D_13_denominator)

def cap_d13_D_13_denominator_factor_right_expression : PolynomialExpr :=
  (.mul (.mul (.mul (.mul (.const ⟨(3211264000000000), 1⟩) (.pow .parent 2)) (.add (.const ⟨(2), 1⟩) .parent)) (.add (.add (.pow .parent 2) (.mul (.const ⟨(3), 1⟩) .parent)) (.const ⟨(1), 1⟩))) (.pow reflectCapChord 2))

set_option maxRecDepth 4096 in
theorem cap_d13_D_13_denominator_factor_coefficients_check : PolynomialExpr.check cap_d13_D_13_denominator_factor_left_expression cap_d13_D_13_denominator_factor_right_expression = true := by
  decide +kernel

theorem cap_d13_D_13_denominator_factor (lam : ℝ) :
    realHorner (cap_d13_D_13_denominator.map fractionValue) lam =
      (3211264000000000/1 : ℝ) * lam ^ 2 * (2 + lam) * (lam ^ 2 + 3 * lam + 1) * (capDLogChord lam) ^ 2 := by
  have hp := PolynomialExpr.check_sound _ _ cap_d13_D_13_denominator_factor_coefficients_check 0 lam
  simp only [cap_d13_D_13_denominator_factor_left_expression, cap_d13_D_13_denominator_factor_right_expression, PolynomialExpr.value, PolynomialExpr.row_value, reflectCapChord_value, fractionValue, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_one, Nat.cast_ofNat, div_one, sub_eq_add_neg, neg_mul, one_mul] at hp
  simpa only [div_one,sub_eq_add_neg,neg_mul,one_mul,mul_one] using hp


theorem cap_d13_D_13_denominator_positive (lam : ℝ) (hr : InRow .D lam) :
    0 < realHorner (cap_d13_D_13_denominator.map fractionValue) lam := by
  rw [cap_d13_D_13_denominator_factor]
  have hl := inRow_activity_pos .D lam hr
  have hG := cap_D_log_chord_pos lam hr
  positivity

def cap_d13_D_13_identity_left_expression : PolynomialExpr :=
  (.mul (.add (.add (.mul (.mul (.mul (.mul (.const ⟨(500), 1⟩) reflectTailDBeta) (.pow .parent 3)) (.add (.const ⟨(2), 1⟩) .parent)) (.pow reflectCapChord 2)) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.mul (.mul (.const ⟨(500), 1⟩) reflectTailDDelta) (.add (.add (.mul (.const ⟨(2), 1⟩) (.mul (.const ⟨(2), 1⟩) (.add (.const ⟨(1), 1⟩) .parent))) (.mul (.const ⟨(-1), 1⟩) .parent)) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.const ⟨(2), 1⟩) (.add (.const ⟨(2), 1⟩) .parent)) reflectCapChord)))) (.pow (.mul (.const ⟨(2), 1⟩) (.add (.const ⟨(1), 1⟩) .parent)) 2)) (.add (.add (.pow .parent 2) (.mul (.const ⟨(3), 1⟩) .parent)) (.const ⟨(1), 1⟩))))) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.mul (.add (.add (.pow .parent 2) (.mul (.const ⟨(3), 1⟩) .parent)) (.const ⟨(1), 1⟩)) (.pow .parent 2)) (.add (.const ⟨(2), 1⟩) .parent)) (.pow reflectCapChord 2)))) (.row cap_d13_D_13_denominator))

def cap_d13_D_13_identity_right_expression : PolynomialExpr :=
  (.mul (.row cap_d13_D_13_numerator) (.mul (.mul (.mul (.mul (.const ⟨(500), 1⟩) (.add (.add (.pow .parent 2) (.mul (.const ⟨(3), 1⟩) .parent)) (.const ⟨(1), 1⟩))) (.pow .parent 2)) (.add (.const ⟨(2), 1⟩) .parent)) (.pow reflectCapChord 2)))

set_option maxRecDepth 4096 in
theorem cap_d13_D_13_identity_coefficients_check : PolynomialExpr.check cap_d13_D_13_identity_left_expression cap_d13_D_13_identity_right_expression = true := by
  decide +kernel

theorem cap_d13_D_13_identity (lam : ℝ) (hr : InRow .D lam) :
    beta .D lam * lam / (lam ^ 2 + 3 * lam + 1) - delta .D lam * capAdverseUpper (q lam / 2) (capDLogChord lam) - 1 / 500 =
      realHorner (cap_d13_D_13_numerator.map fractionValue) lam /
        realHorner (cap_d13_D_13_denominator.map fractionValue) lam := by
  have hp := PolynomialExpr.check_sound _ _ cap_d13_D_13_identity_coefficients_check 0 lam
  simp only [cap_d13_D_13_identity_left_expression, cap_d13_D_13_identity_right_expression, PolynomialExpr.value, PolynomialExpr.row_value, reflectCapChord_value, reflectTailDBeta_value, reflectTailDDelta_value, fractionValue, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_one, Nat.cast_ofNat, div_one, sub_eq_add_neg, neg_mul, one_mul] at hp
  have hl := inRow_activity_pos .D lam hr
  have hd := ne_of_gt (cap_d13_D_13_denominator_positive lam hr)
  have hT := cap_D_log_chord_pos lam hr
  have hden : capReflectD13D lam ≠ 0 := by
    try simp only [capReflectLambdaD,capReflectMD,capReflectElevenD,capReflectD13D,
      reduceCtorEq,ite_true,ite_false]
    positivity
  have hq := cap_d13_reflect_quotient lam hl (ne_of_gt hT)
  try simp only [div_one] at hq
  rw [hq]
  apply (div_eq_div_iff hden hd).mpr
  simpa only [capReflectLambdaN,capReflectLambdaD,capReflectMN,capReflectMD,
    capReflectUN,capReflectSixN,capReflectSevenN,capReflectElevenN,capReflectElevenD,
    capReflectD13N,capReflectD13D,reduceCtorEq,ite_true,ite_false,
    sub_eq_add_neg,neg_mul,one_mul,mul_one,one_pow,div_eq_mul_inv,mul_assoc] using hp


theorem cap_d13_D_13_positive (lam : ℝ) (hr : InRow .D lam) :
    0 < beta .D lam * lam / (lam ^ 2 + 3 * lam + 1) - delta .D lam * capAdverseUpper (q lam / 2) (capDLogChord lam) - 1 / 500 := by
  rw [cap_d13_D_13_identity lam hr]
  exact div_pos (cap_d13_D_13_polynomial_positive lam hr) (cap_d13_D_13_denominator_positive lam hr)

end F4Heavy.Analysis
