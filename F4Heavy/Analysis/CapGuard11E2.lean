module

public import F4Heavy.Analysis.CapBernstein
public import F4Heavy.Analysis.CapCoefficientBounds
public import F4Heavy.Finite.CapGuard11

public import F4Heavy.Analysis.CapPolynomialForms

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

theorem cap_guard11_E2_polynomial_positive (lam : ℝ) (hr : InRow .E2 lam) :
    0 < realHorner (cap_guard11_E2_numerator.map fractionValue) lam := by
  apply cap_bernstein_positive_values cap_guard11_E2_numerator cap_guard11_E2_controls ⟨29, 20⟩ ⟨8, 5⟩ 4 lam
  · norm_num [cap_guard11_E2_numerator]
  · norm_num
  · norm_num
  · norm_num [cap_guard11_E2_numerator]
  · norm_num [fractionValue]
  · simpa [InRow, rowData, fractionValue] using hr.1
  · simpa [InRow, rowData, fractionValue] using hr.2
  · exact cap_guard11_E2_reconstruct
  · intro c hc
    simp only [cap_guard11_E2_controls, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    · exact lt_trans (by norm_num [fractionValue]) (fraction_lt_sound _ _ cap_guard11_E2_coefficient_0)
    · exact lt_trans (by norm_num [fractionValue]) (fraction_lt_sound _ _ cap_guard11_E2_coefficient_1)
    · exact lt_trans (by norm_num [fractionValue]) (fraction_lt_sound _ _ cap_guard11_E2_coefficient_2)
    · exact lt_trans (by norm_num [fractionValue]) (fraction_lt_sound _ _ cap_guard11_E2_coefficient_3)
    · exact lt_trans (by norm_num [fractionValue]) (fraction_lt_sound _ _ cap_guard11_E2_coefficient_4)

def cap_guard11_E2_identity_left_expression : PolynomialExpr :=
  (.mul (.add (.mul (.mul (.mul (.const ⟨(2), 1⟩) reflectTailE2Delta) (.pow (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(2), 1⟩) .parent)) 2)) (.add (.const ⟨(6), 1⟩) .parent)) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.const ⟨(2), 1⟩) (.pow .parent 2)) (.add (.mul (.add (.add (.add (.const ⟨(2), 1⟩) (.mul (.const ⟨(2), 1⟩) reflectTailE2Gamma)) (.mul (.const ⟨(-1), 1⟩) reflectTailE2Alpha)) (.mul (.const ⟨(-1), 1⟩) reflectTailE2Beta)) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(2), 1⟩) .parent))) (.mul (.const ⟨(-1), 1⟩) (.mul (.add (.const ⟨(2), 1⟩) reflectTailE2Gamma) .parent)))))) (.row cap_guard11_E2_denominator))

def cap_guard11_E2_identity_right_expression : PolynomialExpr :=
  (.mul (.row cap_guard11_E2_numerator) (.mul (.pow (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(2), 1⟩) .parent)) 2) (.add (.const ⟨(6), 1⟩) .parent)))

set_option maxRecDepth 4096 in
theorem cap_guard11_E2_identity_coefficients_check : PolynomialExpr.check cap_guard11_E2_identity_left_expression cap_guard11_E2_identity_right_expression = true := by
  decide +kernel

theorem cap_guard11_E2_identity (lam : ℝ) (hr : InRow .E2 lam) :
    2 * delta .E2 lam - capCUpper .E2 lam * (2 * lam / (6 + lam)) =
      realHorner (cap_guard11_E2_numerator.map fractionValue) lam /
        realHorner (cap_guard11_E2_denominator.map fractionValue) lam := by
  have hp := PolynomialExpr.check_sound _ _ cap_guard11_E2_identity_coefficients_check 0 lam
  simp only [cap_guard11_E2_identity_left_expression, cap_guard11_E2_identity_right_expression, PolynomialExpr.value, PolynomialExpr.row_value, reflectTailE2Alpha_value, reflectTailE2Beta_value, reflectTailE2Delta_value, reflectTailE2Gamma_value, fractionValue, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_one, Nat.cast_ofNat, div_one, sub_eq_add_neg, neg_mul, one_mul] at hp
  have hl := inRow_activity_pos .E2 lam hr
  have hd : realHorner (cap_guard11_E2_denominator.map fractionValue) lam ≠ 0 := by
    norm_num [cap_guard11_E2_denominator,realHorner,fractionValue]
    positivity
  have hg := row_gamma_pos .E2 lam hr
  have hden : capReflectElevenD .E2 lam ≠ 0 := by
    try simp only [capReflectLambdaD,capReflectMD,capReflectElevenD,capReflectD13D,
      reduceCtorEq,ite_true,ite_false]
    positivity
  have hq := cap_eleven_reflect_quotient .E2 lam hl hg
  try simp only [div_one] at hq
  rw [hq]
  apply (div_eq_div_iff hden hd).mpr
  simpa only [capReflectLambdaN,capReflectLambdaD,capReflectMN,capReflectMD,
    capReflectUN,capReflectSixN,capReflectSevenN,capReflectElevenN,capReflectElevenD,
    capReflectD13N,capReflectD13D,reduceCtorEq,ite_true,ite_false,
    sub_eq_add_neg,neg_mul,one_mul,mul_one,one_pow,div_eq_mul_inv,mul_assoc] using hp


theorem cap_guard11_E2_positive (lam : ℝ) (hr : InRow .E2 lam) :
    capCUpper .E2 lam * (2 * lam / (6 + lam)) < 2 * delta .E2 lam := by
  have hl := inRow_activity_pos .E2 lam hr
  have hd : 0 < realHorner (cap_guard11_E2_denominator.map fractionValue) lam := by
    norm_num [cap_guard11_E2_denominator, realHorner, fractionValue]
    positivity
  have hp := div_pos (cap_guard11_E2_polynomial_positive lam hr) hd
  rw [← cap_guard11_E2_identity lam hr] at hp
  linarith only [hp]

end F4Heavy.Analysis
