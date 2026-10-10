module

public import F4Heavy.Analysis.LeafCore
public import F4Heavy.Analysis.BernsteinSemantics
public import F4Heavy.Finite.LeafCertificates

public import F4Heavy.Analysis.LeafPolynomialForms

@[expose] public section
set_option autoImplicit false
namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

theorem leaf_E1_polynomial_positive (t : ℝ) (ht : (13/23 : ℝ) ≤ t ∧ t ≤ (29/49 : ℝ)) :
    0 < realHorner (leaf_E1_polynomial.map fractionValue) t := by
  apply bernstein_positive_of_allEq leaf_E1_polynomial leaf_E1_controls ⟨13, 23⟩ ⟨29, 49⟩ 9 t
  · norm_num [leaf_E1_polynomial]
  · norm_num
  · norm_num
  · norm_num [leaf_E1_polynomial]
  · norm_num [fractionValue]
  · simpa only [fractionValue, Int.cast_ofNat, Nat.cast_ofNat] using ht.1
  · simpa only [fractionValue, Int.cast_ofNat, Nat.cast_ofNat] using ht.2
  · exact leaf_E1_reconstruction
  · intro c hc
    simp only [leaf_E1_controls, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact leaf_E1_coefficient_00
    · exact leaf_E1_coefficient_01
    · exact leaf_E1_coefficient_02
    · exact leaf_E1_coefficient_03
    · exact leaf_E1_coefficient_04
    · exact leaf_E1_coefficient_05
    · exact leaf_E1_coefficient_06
    · exact leaf_E1_coefficient_07
    · exact leaf_E1_coefficient_08
    · exact leaf_E1_coefficient_09

def leaf_E1_discriminant_identity_left_expression : PolynomialExpr :=
  (.add (.mul (.mul (.const ⟨(4), 1⟩) (.mul (.mul (.mul (.const ⟨(65536), 1⟩) (.const ⟨(17), 10⟩)) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) (.pow .parent 2)))) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .parent)))) (.mul (.mul (.const ⟨(2), 1⟩) .parent) (.add (.add (.mul (.const ⟨(14899), 4⟩) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .parent))) (.mul (.const ⟨(29958), 1⟩) .parent)) (.mul (.const ⟨(-1), 1⟩) (.mul (.add (.mul (.const ⟨(-82745), 8⟩) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .parent))) (.mul (.const ⟨(20483), 1⟩) .parent)) (.add (.add (.add (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) (.mul .parent (.const ⟨(1), 2⟩)))) (.mul (.const ⟨(-1), 1⟩) (.mul (.pow .parent 2) (.const ⟨(1), 12⟩)))) (.mul (.const ⟨(-1), 1⟩) (.mul (.pow .parent 3) (.const ⟨(1), 24⟩)))) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.const ⟨(19), 1⟩) (.pow .parent 4)) (.const ⟨(1), 720⟩))))))))) (.mul (.const ⟨(-1), 1⟩) (.pow (.add (.add (.mul (.mul (.const ⟨(-65536), 1⟩) (.const ⟨(17), 10⟩)) (.pow (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .parent)) 3)) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.const ⟨(2), 1⟩) .parent) (.add (.mul (.const ⟨(14899), 4⟩) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .parent))) (.mul (.const ⟨(29958), 1⟩) .parent))))) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.const ⟨(131072), 1⟩) .parent) (.pow (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .parent)) 2)))) 2)))

set_option maxRecDepth 4096 in
theorem leaf_E1_discriminant_identity_coefficients_check : PolynomialExpr.check leaf_E1_discriminant_identity_left_expression (.row leaf_E1_polynomial) = true := by
  decide +kernel

theorem leaf_E1_discriminant_identity (lam : ℝ) (hr : InRow .E1 lam) :
    4*leafA .E1 lam*leafC .E1 lam-(leafB .E1 lam)^2 =
      realHorner (leaf_E1_polynomial.map fractionValue) (q lam)/(131072*q lam*(1-q lam))^2 := by
  have hl := inRow_activity_pos .E1 lam hr
  have hq := ne_of_gt (q_pos lam hl)
  have hq1 := ne_of_gt (sub_pos.mpr (q_lt_one lam hl))
  have h_alpha : alpha .E1 lam =
      ((14899/4 : ℝ)*(1-q lam)+29958*q lam)/(65536*(1-q lam)) := by
    convert activity_field_q_coordinate 44917 29958 (11/8 : ℝ) lam hl using 1 <;>
      norm_num [alpha, rowData]
  have h_gamma : gamma .E1 lam =
      ((-82745/8 : ℝ)*(1-q lam)+20483*q lam)/(65536*(1-q lam)) := by
    convert activity_field_q_coordinate 17821 20483 (11/8 : ℝ) lam hl using 1 <;>
      norm_num [gamma, rowData]
  have hp := PolynomialExpr.check_sound _ _ leaf_E1_discriminant_identity_coefficients_check 0 (q lam)
  simp only [leaf_E1_discriminant_identity_left_expression,PolynomialExpr.value,PolynomialExpr.row_value,
    fractionValue,Int.cast_ofNat,Int.cast_neg,Int.cast_one,Nat.cast_ofNat,Nat.cast_one,div_one] at hp
  unfold leafA leafB leafC
  rw [h_alpha,h_gamma]
  norm_num only [rowData]
  have hf := leaf_reflect_quotient (rowData .E1).price (q lam) ((14899/4 : ℝ)*(1-q lam)+29958*q lam) ((-82745/8 : ℝ)*(1-q lam)+20483*q lam) hq hq1
  norm_num only [rowData,leafReflectV] at hf
  rw [hf]
  congr 1
  simpa only [leafReflectN,leafReflectV,sub_eq_add_neg,neg_mul,
    one_mul,mul_one,div_eq_mul_inv,mul_assoc] using hp


theorem leafPositive_E1_proved : LeafPositive .E1 := by
  apply leaf_positive_of_discriminant .E1
  intro lam hr
  have hl := inRow_activity_pos .E1 lam hr
  have hq := q_pos lam hl
  have hq1 : 0 < 1-q lam := sub_pos.mpr (q_lt_one lam hl)
  have hrow := hr
  norm_num [InRow, rowData] at hrow
  have hb := activity_q_bounds lam (13/10 : ℝ) (29/20 : ℝ)
    (by norm_num) hrow.1 hrow.2
  have hb' : (13/23 : ℝ) ≤ q lam ∧ q lam ≤ (29/49 : ℝ) := by
    norm_num [q] at hb
    simpa only [q] using hb
  rw [leaf_E1_discriminant_identity lam hr]
  exact div_pos (leaf_E1_polynomial_positive (q lam) hb') (sq_pos_of_pos (by positivity))

end F4Heavy.Analysis
