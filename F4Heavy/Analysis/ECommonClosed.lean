module

public import F4Heavy.Analysis.CommonEndpointSemantics
public import F4Heavy.Analysis.CertificateCoordinates
public import F4Heavy.Analysis.ECommonNumerators

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Heavy.Finite

theorem e_common_E1_r8_H0_last_column_positive (v : ℝ) (hv : |v| ≤ (15/1127 : ℝ)) :
    0 < realHorner ((e_common_E1_r8_H0_columns[6]?.getD []).map fractionValue) v := by
  apply primitiveLowerCheck_column_positive e_common_E1_r8_H0_columns ⟨15, 1127⟩ ⟨75, 675615064408886122350592⟩ e_common_E1_r8_H0 6 v
  · norm_num [e_common_E1_r8_H0]
  · norm_num [e_common_E1_r8_H0_columns]
  · norm_num
  · simpa only [fractionValue, Int.cast_ofNat, Nat.cast_ofNat] using hv
  · norm_num [e_common_E1_r8_H0]
  · exact cert_0275_E1_r8_H0_primitive_lower_polynomial_identity
  · simpa only [e_common_E1_r8_H0, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some] using
      fraction_positive_sound _ cert_0282_E1_r8_H0_strict_lower_coefficient_6

theorem e_common_E1_r8_H0_numerator_endpoint_positive (q : ℝ) (hq : (13/23 : ℝ) ≤ q ∧ q ≤ 29/49) :
    0 < matrixValue numerator_E1_r8_H0 (q/(1-q)) 1 := by
  have hc : fractionValue (commonActivityCenter ⟨13, 10⟩ ⟨29, 20⟩) = (652/1127 : ℝ) := by
    norm_num [commonActivityCenter, Fraction.div, Fraction.add, Fraction.mul,
      Fraction.inv, Fraction.normalize, Fraction.one, Fraction.ofInt, fractionValue]
  apply commonColumns_endpoint_positive numerator_E1_r8_H0 e_common_E1_r8_H0_columns ⟨1, 4⟩ ⟨13, 10⟩ ⟨29, 20⟩ q
  · norm_num [numerator_E1_r8_H0]
  · norm_num
  · norm_num [commonActivityCenter, Fraction.div, Fraction.add, Fraction.mul,
      Fraction.inv, Fraction.normalize, Fraction.one, Fraction.ofInt]
  · norm_num [numerator_E1_r8_H0]
  · norm_num [numerator_E1_r8_H0]
  · linarith only [hq.2]
  · exact reconstruct_154_E1_r8_H0
  · change 0 < realHorner ((e_common_E1_r8_H0_columns[6]?.getD []).map fractionValue) _
    apply e_common_E1_r8_H0_last_column_positive
    rw [hc, abs_le]
    constructor <;> linarith only [hq.1, hq.2]

theorem e_common_E1_r8_H0_numerator_rectangle_positive (lam x : ℝ)
    (hlam : (13/10 : ℝ) ≤ lam ∧ lam ≤ 29/20) (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < matrixValue numerator_E1_r8_H0 lam x := by
  have hd : 0 < 1+lam := by linarith only [hlam.1]
  have hq : (13/23 : ℝ) ≤ lam/(1+lam) ∧ lam/(1+lam) ≤ 29/49 := by
    convert activity_projective_interval (13/10 : ℝ) (29/20 : ℝ) lam (by norm_num) hlam using 1 <;> norm_num
  have ht := parent_interval_parameter (1/4 : ℝ) x (by norm_num) hx
  rcases lt_or_eq_of_le hx.2 with hlt | rfl
  · have ht1 : (x-(1/4 : ℝ))/(1-(1/4 : ℝ)) < 1 := (div_lt_one (by norm_num)).mpr (by linarith only [hlt])
    have h := e_common_E1_r8_H0_numerator_positive (lam/(1+lam)) ((x-(1/4 : ℝ))/(1-(1/4 : ℝ))) hq ht.1 ht1
    rw [activity_projective_inverse lam (ne_of_gt hd), ht.2.2] at h
    exact h
  · have h := e_common_E1_r8_H0_numerator_endpoint_positive (lam/(1+lam)) hq
    rwa [activity_projective_inverse lam (ne_of_gt hd)] at h

theorem e_common_E1_r8_U0_last_column_positive (v : ℝ) (hv : |v| ≤ (15/1127 : ℝ)) :
    0 < realHorner ((e_common_E1_r8_U0_columns[5]?.getD []).map fractionValue) v := by
  apply primitiveLowerCheck_column_positive e_common_E1_r8_U0_columns ⟨15, 1127⟩ ⟨225, 4378154521135684294362423808⟩ e_common_E1_r8_U0 5 v
  · norm_num [e_common_E1_r8_U0]
  · norm_num [e_common_E1_r8_U0_columns]
  · norm_num
  · simpa only [fractionValue, Int.cast_ofNat, Nat.cast_ofNat] using hv
  · norm_num [e_common_E1_r8_U0]
  · exact cert_0285_E1_r8_U0_primitive_lower_polynomial_identity
  · simpa only [e_common_E1_r8_U0, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some] using
      fraction_positive_sound _ cert_0291_E1_r8_U0_strict_lower_coefficient_5

theorem e_common_E1_r8_U0_numerator_endpoint_positive (q : ℝ) (hq : (13/23 : ℝ) ≤ q ∧ q ≤ 29/49) :
    0 < matrixValue numerator_E1_r8_U0 (q/(1-q)) 1 := by
  have hc : fractionValue (commonActivityCenter ⟨13, 10⟩ ⟨29, 20⟩) = (652/1127 : ℝ) := by
    norm_num [commonActivityCenter, Fraction.div, Fraction.add, Fraction.mul,
      Fraction.inv, Fraction.normalize, Fraction.one, Fraction.ofInt, fractionValue]
  apply commonColumns_endpoint_positive numerator_E1_r8_U0 e_common_E1_r8_U0_columns ⟨1, 4⟩ ⟨13, 10⟩ ⟨29, 20⟩ q
  · norm_num [numerator_E1_r8_U0]
  · norm_num
  · norm_num [commonActivityCenter, Fraction.div, Fraction.add, Fraction.mul,
      Fraction.inv, Fraction.normalize, Fraction.one, Fraction.ofInt]
  · norm_num [numerator_E1_r8_U0]
  · norm_num [numerator_E1_r8_U0]
  · linarith only [hq.2]
  · exact reconstruct_155_E1_r8_U0
  · change 0 < realHorner ((e_common_E1_r8_U0_columns[5]?.getD []).map fractionValue) _
    apply e_common_E1_r8_U0_last_column_positive
    rw [hc, abs_le]
    constructor <;> linarith only [hq.1, hq.2]

theorem e_common_E1_r8_U0_numerator_rectangle_positive (lam x : ℝ)
    (hlam : (13/10 : ℝ) ≤ lam ∧ lam ≤ 29/20) (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < matrixValue numerator_E1_r8_U0 lam x := by
  have hd : 0 < 1+lam := by linarith only [hlam.1]
  have hq : (13/23 : ℝ) ≤ lam/(1+lam) ∧ lam/(1+lam) ≤ 29/49 := by
    convert activity_projective_interval (13/10 : ℝ) (29/20 : ℝ) lam (by norm_num) hlam using 1 <;> norm_num
  have ht := parent_interval_parameter (1/4 : ℝ) x (by norm_num) hx
  rcases lt_or_eq_of_le hx.2 with hlt | rfl
  · have ht1 : (x-(1/4 : ℝ))/(1-(1/4 : ℝ)) < 1 := (div_lt_one (by norm_num)).mpr (by linarith only [hlt])
    have h := e_common_E1_r8_U0_numerator_positive (lam/(1+lam)) ((x-(1/4 : ℝ))/(1-(1/4 : ℝ))) hq ht.1 ht1
    rw [activity_projective_inverse lam (ne_of_gt hd), ht.2.2] at h
    exact h
  · have h := e_common_E1_r8_U0_numerator_endpoint_positive (lam/(1+lam)) hq
    rwa [activity_projective_inverse lam (ne_of_gt hd)] at h

theorem e_common_E1_r8_U1_last_column_positive (v : ℝ) (hv : |v| ≤ (15/1127 : ℝ)) :
    0 < realHorner ((e_common_E1_r8_U1_columns[7]?.getD []).map fractionValue) v := by
  apply primitiveLowerCheck_column_positive e_common_E1_r8_U1_columns ⟨15, 1127⟩ ⟨10125, 3814723222310024252180376178338225152⟩ e_common_E1_r8_U1 7 v
  · norm_num [e_common_E1_r8_U1]
  · norm_num [e_common_E1_r8_U1_columns]
  · norm_num
  · simpa only [fractionValue, Int.cast_ofNat, Nat.cast_ofNat] using hv
  · norm_num [e_common_E1_r8_U1]
  · exact cert_0294_E1_r8_U1_primitive_lower_polynomial_identity
  · simpa only [e_common_E1_r8_U1, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some] using
      fraction_positive_sound _ cert_0302_E1_r8_U1_strict_lower_coefficient_7

theorem e_common_E1_r8_U1_numerator_endpoint_positive (q : ℝ) (hq : (13/23 : ℝ) ≤ q ∧ q ≤ 29/49) :
    0 < matrixValue numerator_E1_r8_U1 (q/(1-q)) 1 := by
  have hc : fractionValue (commonActivityCenter ⟨13, 10⟩ ⟨29, 20⟩) = (652/1127 : ℝ) := by
    norm_num [commonActivityCenter, Fraction.div, Fraction.add, Fraction.mul,
      Fraction.inv, Fraction.normalize, Fraction.one, Fraction.ofInt, fractionValue]
  apply commonColumns_endpoint_positive numerator_E1_r8_U1 e_common_E1_r8_U1_columns ⟨1, 4⟩ ⟨13, 10⟩ ⟨29, 20⟩ q
  · norm_num [numerator_E1_r8_U1]
  · norm_num
  · norm_num [commonActivityCenter, Fraction.div, Fraction.add, Fraction.mul,
      Fraction.inv, Fraction.normalize, Fraction.one, Fraction.ofInt]
  · norm_num [numerator_E1_r8_U1]
  · norm_num [numerator_E1_r8_U1]
  · linarith only [hq.2]
  · exact reconstruct_156_E1_r8_U1
  · change 0 < realHorner ((e_common_E1_r8_U1_columns[7]?.getD []).map fractionValue) _
    apply e_common_E1_r8_U1_last_column_positive
    rw [hc, abs_le]
    constructor <;> linarith only [hq.1, hq.2]

theorem e_common_E1_r8_U1_numerator_rectangle_positive (lam x : ℝ)
    (hlam : (13/10 : ℝ) ≤ lam ∧ lam ≤ 29/20) (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < matrixValue numerator_E1_r8_U1 lam x := by
  have hd : 0 < 1+lam := by linarith only [hlam.1]
  have hq : (13/23 : ℝ) ≤ lam/(1+lam) ∧ lam/(1+lam) ≤ 29/49 := by
    convert activity_projective_interval (13/10 : ℝ) (29/20 : ℝ) lam (by norm_num) hlam using 1 <;> norm_num
  have ht := parent_interval_parameter (1/4 : ℝ) x (by norm_num) hx
  rcases lt_or_eq_of_le hx.2 with hlt | rfl
  · have ht1 : (x-(1/4 : ℝ))/(1-(1/4 : ℝ)) < 1 := (div_lt_one (by norm_num)).mpr (by linarith only [hlt])
    have h := e_common_E1_r8_U1_numerator_positive (lam/(1+lam)) ((x-(1/4 : ℝ))/(1-(1/4 : ℝ))) hq ht.1 ht1
    rw [activity_projective_inverse lam (ne_of_gt hd), ht.2.2] at h
    exact h
  · have h := e_common_E1_r8_U1_numerator_endpoint_positive (lam/(1+lam)) hq
    rwa [activity_projective_inverse lam (ne_of_gt hd)] at h

theorem e_common_E1_r8_U3_last_column_positive (v : ℝ) (hv : |v| ≤ (15/1127 : ℝ)) :
    0 < realHorner ((e_common_E1_r8_U3_columns[7]?.getD []).map fractionValue) v := by
  apply primitiveLowerCheck_column_positive e_common_E1_r8_U3_columns ⟨15, 1127⟩ ⟨10125, 27078780637515700104208526554308608⟩ e_common_E1_r8_U3 7 v
  · norm_num [e_common_E1_r8_U3]
  · norm_num [e_common_E1_r8_U3_columns]
  · norm_num
  · simpa only [fractionValue, Int.cast_ofNat, Nat.cast_ofNat] using hv
  · norm_num [e_common_E1_r8_U3]
  · exact cert_0403_E1_r8_U3_primitive_lower_polynomial_identity
  · simpa only [e_common_E1_r8_U3, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some] using
      fraction_positive_sound _ cert_0411_E1_r8_U3_closed_x_1_endpoint

theorem e_common_E1_r8_U3_numerator_endpoint_positive (q : ℝ) (hq : (13/23 : ℝ) ≤ q ∧ q ≤ 29/49) :
    0 < matrixValue numerator_E1_r8_U3 (q/(1-q)) 1 := by
  have hc : fractionValue (commonActivityCenter ⟨13, 10⟩ ⟨29, 20⟩) = (652/1127 : ℝ) := by
    norm_num [commonActivityCenter, Fraction.div, Fraction.add, Fraction.mul,
      Fraction.inv, Fraction.normalize, Fraction.one, Fraction.ofInt, fractionValue]
  apply commonColumns_endpoint_positive numerator_E1_r8_U3 e_common_E1_r8_U3_columns ⟨1, 4⟩ ⟨13, 10⟩ ⟨29, 20⟩ q
  · norm_num [numerator_E1_r8_U3]
  · norm_num
  · norm_num [commonActivityCenter, Fraction.div, Fraction.add, Fraction.mul,
      Fraction.inv, Fraction.normalize, Fraction.one, Fraction.ofInt]
  · norm_num [numerator_E1_r8_U3]
  · norm_num [numerator_E1_r8_U3]
  · linarith only [hq.2]
  · exact reconstruct_158_E1_r8_U3
  · change 0 < realHorner ((e_common_E1_r8_U3_columns[7]?.getD []).map fractionValue) _
    apply e_common_E1_r8_U3_last_column_positive
    rw [hc, abs_le]
    constructor <;> linarith only [hq.1, hq.2]

theorem e_common_E1_r8_U3_numerator_rectangle_positive (lam x : ℝ)
    (hlam : (13/10 : ℝ) ≤ lam ∧ lam ≤ 29/20) (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < matrixValue numerator_E1_r8_U3 lam x := by
  have hd : 0 < 1+lam := by linarith only [hlam.1]
  have hq : (13/23 : ℝ) ≤ lam/(1+lam) ∧ lam/(1+lam) ≤ 29/49 := by
    convert activity_projective_interval (13/10 : ℝ) (29/20 : ℝ) lam (by norm_num) hlam using 1 <;> norm_num
  have ht := parent_interval_parameter (1/4 : ℝ) x (by norm_num) hx
  rcases lt_or_eq_of_le hx.2 with hlt | rfl
  · have ht1 : (x-(1/4 : ℝ))/(1-(1/4 : ℝ)) < 1 := (div_lt_one (by norm_num)).mpr (by linarith only [hlt])
    have h := e_common_E1_r8_U3_numerator_positive (lam/(1+lam)) ((x-(1/4 : ℝ))/(1-(1/4 : ℝ))) hq ht.1 ht1
    rw [activity_projective_inverse lam (ne_of_gt hd), ht.2.2] at h
    exact h
  · have h := e_common_E1_r8_U3_numerator_endpoint_positive (lam/(1+lam)) hq
    rwa [activity_projective_inverse lam (ne_of_gt hd)] at h

theorem e_common_E1_r8_D_last_column_positive (v : ℝ) (hv : |v| ≤ (15/1127 : ℝ)) :
    0 < realHorner ((e_common_E1_r8_D_columns[4]?.getD []).map fractionValue) v := by
  apply primitiveLowerCheck_column_positive e_common_E1_r8_D_columns ⟨15, 1127⟩ ⟨45, 25811642826256⟩ e_common_E1_r8_D 4 v
  · norm_num [e_common_E1_r8_D]
  · norm_num [e_common_E1_r8_D_columns]
  · norm_num
  · simpa only [fractionValue, Int.cast_ofNat, Nat.cast_ofNat] using hv
  · norm_num [e_common_E1_r8_D]
  · exact cert_0415_E1_r8_D_primitive_lower_polynomial_identity
  · simpa only [e_common_E1_r8_D, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some] using
      fraction_positive_sound _ cert_0420_E1_r8_D_strict_lower_coefficient_4

theorem e_common_E1_r8_D_numerator_endpoint_positive (q : ℝ) (hq : (13/23 : ℝ) ≤ q ∧ q ≤ 29/49) :
    0 < matrixValue numerator_E1_r8_D (q/(1-q)) 1 := by
  have hc : fractionValue (commonActivityCenter ⟨13, 10⟩ ⟨29, 20⟩) = (652/1127 : ℝ) := by
    norm_num [commonActivityCenter, Fraction.div, Fraction.add, Fraction.mul,
      Fraction.inv, Fraction.normalize, Fraction.one, Fraction.ofInt, fractionValue]
  apply commonColumns_endpoint_positive numerator_E1_r8_D e_common_E1_r8_D_columns ⟨1, 4⟩ ⟨13, 10⟩ ⟨29, 20⟩ q
  · norm_num [numerator_E1_r8_D]
  · norm_num
  · norm_num [commonActivityCenter, Fraction.div, Fraction.add, Fraction.mul,
      Fraction.inv, Fraction.normalize, Fraction.one, Fraction.ofInt]
  · norm_num [numerator_E1_r8_D]
  · norm_num [numerator_E1_r8_D]
  · linarith only [hq.2]
  · exact reconstruct_159_E1_r8_D
  · change 0 < realHorner ((e_common_E1_r8_D_columns[4]?.getD []).map fractionValue) _
    apply e_common_E1_r8_D_last_column_positive
    rw [hc, abs_le]
    constructor <;> linarith only [hq.1, hq.2]

theorem e_common_E1_r8_D_numerator_rectangle_positive (lam x : ℝ)
    (hlam : (13/10 : ℝ) ≤ lam ∧ lam ≤ 29/20) (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < matrixValue numerator_E1_r8_D lam x := by
  have hd : 0 < 1+lam := by linarith only [hlam.1]
  have hq : (13/23 : ℝ) ≤ lam/(1+lam) ∧ lam/(1+lam) ≤ 29/49 := by
    convert activity_projective_interval (13/10 : ℝ) (29/20 : ℝ) lam (by norm_num) hlam using 1 <;> norm_num
  have ht := parent_interval_parameter (1/4 : ℝ) x (by norm_num) hx
  rcases lt_or_eq_of_le hx.2 with hlt | rfl
  · have ht1 : (x-(1/4 : ℝ))/(1-(1/4 : ℝ)) < 1 := (div_lt_one (by norm_num)).mpr (by linarith only [hlt])
    have h := e_common_E1_r8_D_numerator_positive (lam/(1+lam)) ((x-(1/4 : ℝ))/(1-(1/4 : ℝ))) hq ht.1 ht1
    rw [activity_projective_inverse lam (ne_of_gt hd), ht.2.2] at h
    exact h
  · have h := e_common_E1_r8_D_numerator_endpoint_positive (lam/(1+lam)) hq
    rwa [activity_projective_inverse lam (ne_of_gt hd)] at h

theorem e_common_E2_r8_H0_last_column_positive (v : ℝ) (hv : |v| ≤ (15/1274 : ℝ)) :
    0 < realHorner ((e_common_E2_r8_H0_columns[6]?.getD []).map fractionValue) v := by
  apply primitiveLowerCheck_column_positive e_common_E2_r8_H0_columns ⟨15, 1274⟩ ⟨675, 5578095593581145611698176⟩ e_common_E2_r8_H0 6 v
  · norm_num [e_common_E2_r8_H0]
  · norm_num [e_common_E2_r8_H0_columns]
  · norm_num
  · simpa only [fractionValue, Int.cast_ofNat, Nat.cast_ofNat] using hv
  · norm_num [e_common_E2_r8_H0]
  · exact cert_0424_E2_r8_H0_primitive_lower_polynomial_identity
  · simpa only [e_common_E2_r8_H0, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some] using
      fraction_positive_sound _ cert_0431_E2_r8_H0_strict_lower_coefficient_6

theorem e_common_E2_r8_H0_numerator_endpoint_positive (q : ℝ) (hq : (29/49 : ℝ) ≤ q ∧ q ≤ 8/13) :
    0 < matrixValue numerator_E2_r8_H0 (q/(1-q)) 1 := by
  have hc : fractionValue (commonActivityCenter ⟨29, 20⟩ ⟨8, 5⟩) = (769/1274 : ℝ) := by
    norm_num [commonActivityCenter, Fraction.div, Fraction.add, Fraction.mul,
      Fraction.inv, Fraction.normalize, Fraction.one, Fraction.ofInt, fractionValue]
  apply commonColumns_endpoint_positive numerator_E2_r8_H0 e_common_E2_r8_H0_columns ⟨1, 4⟩ ⟨29, 20⟩ ⟨8, 5⟩ q
  · norm_num [numerator_E2_r8_H0]
  · norm_num
  · norm_num [commonActivityCenter, Fraction.div, Fraction.add, Fraction.mul,
      Fraction.inv, Fraction.normalize, Fraction.one, Fraction.ofInt]
  · norm_num [numerator_E2_r8_H0]
  · norm_num [numerator_E2_r8_H0]
  · linarith only [hq.2]
  · exact reconstruct_160_E2_r8_H0
  · change 0 < realHorner ((e_common_E2_r8_H0_columns[6]?.getD []).map fractionValue) _
    apply e_common_E2_r8_H0_last_column_positive
    rw [hc, abs_le]
    constructor <;> linarith only [hq.1, hq.2]

theorem e_common_E2_r8_H0_numerator_rectangle_positive (lam x : ℝ)
    (hlam : (29/20 : ℝ) ≤ lam ∧ lam ≤ 8/5) (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < matrixValue numerator_E2_r8_H0 lam x := by
  have hd : 0 < 1+lam := by linarith only [hlam.1]
  have hq : (29/49 : ℝ) ≤ lam/(1+lam) ∧ lam/(1+lam) ≤ 8/13 := by
    convert activity_projective_interval (29/20 : ℝ) (8/5 : ℝ) lam (by norm_num) hlam using 1 <;> norm_num
  have ht := parent_interval_parameter (1/4 : ℝ) x (by norm_num) hx
  rcases lt_or_eq_of_le hx.2 with hlt | rfl
  · have ht1 : (x-(1/4 : ℝ))/(1-(1/4 : ℝ)) < 1 := (div_lt_one (by norm_num)).mpr (by linarith only [hlt])
    have h := e_common_E2_r8_H0_numerator_positive (lam/(1+lam)) ((x-(1/4 : ℝ))/(1-(1/4 : ℝ))) hq ht.1 ht1
    rw [activity_projective_inverse lam (ne_of_gt hd), ht.2.2] at h
    exact h
  · have h := e_common_E2_r8_H0_numerator_endpoint_positive (lam/(1+lam)) hq
    rwa [activity_projective_inverse lam (ne_of_gt hd)] at h

theorem e_common_E2_r8_U0_last_column_positive (v : ℝ) (hv : |v| ≤ (15/1274 : ℝ)) :
    0 < realHorner ((e_common_E2_r8_U0_columns[5]?.getD []).map fractionValue) v := by
  apply primitiveLowerCheck_column_positive e_common_E2_r8_U0_columns ⟨15, 1274⟩ ⟨9375, 444155861638898719331467264⟩ e_common_E2_r8_U0 5 v
  · norm_num [e_common_E2_r8_U0]
  · norm_num [e_common_E2_r8_U0_columns]
  · norm_num
  · simpa only [fractionValue, Int.cast_ofNat, Nat.cast_ofNat] using hv
  · norm_num [e_common_E2_r8_U0]
  · exact cert_0434_E2_r8_U0_primitive_lower_polynomial_identity
  · simpa only [e_common_E2_r8_U0, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some] using
      fraction_positive_sound _ cert_0440_E2_r8_U0_strict_lower_coefficient_5

theorem e_common_E2_r8_U0_numerator_endpoint_positive (q : ℝ) (hq : (29/49 : ℝ) ≤ q ∧ q ≤ 8/13) :
    0 < matrixValue numerator_E2_r8_U0 (q/(1-q)) 1 := by
  have hc : fractionValue (commonActivityCenter ⟨29, 20⟩ ⟨8, 5⟩) = (769/1274 : ℝ) := by
    norm_num [commonActivityCenter, Fraction.div, Fraction.add, Fraction.mul,
      Fraction.inv, Fraction.normalize, Fraction.one, Fraction.ofInt, fractionValue]
  apply commonColumns_endpoint_positive numerator_E2_r8_U0 e_common_E2_r8_U0_columns ⟨1, 4⟩ ⟨29, 20⟩ ⟨8, 5⟩ q
  · norm_num [numerator_E2_r8_U0]
  · norm_num
  · norm_num [commonActivityCenter, Fraction.div, Fraction.add, Fraction.mul,
      Fraction.inv, Fraction.normalize, Fraction.one, Fraction.ofInt]
  · norm_num [numerator_E2_r8_U0]
  · norm_num [numerator_E2_r8_U0]
  · linarith only [hq.2]
  · exact reconstruct_161_E2_r8_U0
  · change 0 < realHorner ((e_common_E2_r8_U0_columns[5]?.getD []).map fractionValue) _
    apply e_common_E2_r8_U0_last_column_positive
    rw [hc, abs_le]
    constructor <;> linarith only [hq.1, hq.2]

theorem e_common_E2_r8_U0_numerator_rectangle_positive (lam x : ℝ)
    (hlam : (29/20 : ℝ) ≤ lam ∧ lam ≤ 8/5) (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < matrixValue numerator_E2_r8_U0 lam x := by
  have hd : 0 < 1+lam := by linarith only [hlam.1]
  have hq : (29/49 : ℝ) ≤ lam/(1+lam) ∧ lam/(1+lam) ≤ 8/13 := by
    convert activity_projective_interval (29/20 : ℝ) (8/5 : ℝ) lam (by norm_num) hlam using 1 <;> norm_num
  have ht := parent_interval_parameter (1/4 : ℝ) x (by norm_num) hx
  rcases lt_or_eq_of_le hx.2 with hlt | rfl
  · have ht1 : (x-(1/4 : ℝ))/(1-(1/4 : ℝ)) < 1 := (div_lt_one (by norm_num)).mpr (by linarith only [hlt])
    have h := e_common_E2_r8_U0_numerator_positive (lam/(1+lam)) ((x-(1/4 : ℝ))/(1-(1/4 : ℝ))) hq ht.1 ht1
    rw [activity_projective_inverse lam (ne_of_gt hd), ht.2.2] at h
    exact h
  · have h := e_common_E2_r8_U0_numerator_endpoint_positive (lam/(1+lam)) hq
    rwa [activity_projective_inverse lam (ne_of_gt hd)] at h

theorem e_common_E2_r8_U1_last_column_positive (v : ℝ) (hv : |v| ≤ (15/1274 : ℝ)) :
    0 < realHorner ((e_common_E2_r8_U1_columns[7]?.getD []).map fractionValue) v := by
  apply primitiveLowerCheck_column_positive e_common_E2_r8_U1_columns ⟨15, 1274⟩ ⟨5625, 58779197975655775007277700780396642304⟩ e_common_E2_r8_U1 7 v
  · norm_num [e_common_E2_r8_U1]
  · norm_num [e_common_E2_r8_U1_columns]
  · norm_num
  · simpa only [fractionValue, Int.cast_ofNat, Nat.cast_ofNat] using hv
  · norm_num [e_common_E2_r8_U1]
  · exact cert_0443_E2_r8_U1_primitive_lower_polynomial_identity
  · simpa only [e_common_E2_r8_U1, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some] using
      fraction_positive_sound _ cert_0451_E2_r8_U1_strict_lower_coefficient_7

theorem e_common_E2_r8_U1_numerator_endpoint_positive (q : ℝ) (hq : (29/49 : ℝ) ≤ q ∧ q ≤ 8/13) :
    0 < matrixValue numerator_E2_r8_U1 (q/(1-q)) 1 := by
  have hc : fractionValue (commonActivityCenter ⟨29, 20⟩ ⟨8, 5⟩) = (769/1274 : ℝ) := by
    norm_num [commonActivityCenter, Fraction.div, Fraction.add, Fraction.mul,
      Fraction.inv, Fraction.normalize, Fraction.one, Fraction.ofInt, fractionValue]
  apply commonColumns_endpoint_positive numerator_E2_r8_U1 e_common_E2_r8_U1_columns ⟨1, 4⟩ ⟨29, 20⟩ ⟨8, 5⟩ q
  · norm_num [numerator_E2_r8_U1]
  · norm_num
  · norm_num [commonActivityCenter, Fraction.div, Fraction.add, Fraction.mul,
      Fraction.inv, Fraction.normalize, Fraction.one, Fraction.ofInt]
  · norm_num [numerator_E2_r8_U1]
  · norm_num [numerator_E2_r8_U1]
  · linarith only [hq.2]
  · exact reconstruct_162_E2_r8_U1
  · change 0 < realHorner ((e_common_E2_r8_U1_columns[7]?.getD []).map fractionValue) _
    apply e_common_E2_r8_U1_last_column_positive
    rw [hc, abs_le]
    constructor <;> linarith only [hq.1, hq.2]

theorem e_common_E2_r8_U1_numerator_rectangle_positive (lam x : ℝ)
    (hlam : (29/20 : ℝ) ≤ lam ∧ lam ≤ 8/5) (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < matrixValue numerator_E2_r8_U1 lam x := by
  have hd : 0 < 1+lam := by linarith only [hlam.1]
  have hq : (29/49 : ℝ) ≤ lam/(1+lam) ∧ lam/(1+lam) ≤ 8/13 := by
    convert activity_projective_interval (29/20 : ℝ) (8/5 : ℝ) lam (by norm_num) hlam using 1 <;> norm_num
  have ht := parent_interval_parameter (1/4 : ℝ) x (by norm_num) hx
  rcases lt_or_eq_of_le hx.2 with hlt | rfl
  · have ht1 : (x-(1/4 : ℝ))/(1-(1/4 : ℝ)) < 1 := (div_lt_one (by norm_num)).mpr (by linarith only [hlt])
    have h := e_common_E2_r8_U1_numerator_positive (lam/(1+lam)) ((x-(1/4 : ℝ))/(1-(1/4 : ℝ))) hq ht.1 ht1
    rw [activity_projective_inverse lam (ne_of_gt hd), ht.2.2] at h
    exact h
  · have h := e_common_E2_r8_U1_numerator_endpoint_positive (lam/(1+lam)) hq
    rwa [activity_projective_inverse lam (ne_of_gt hd)] at h

theorem e_common_E2_r8_U2_last_column_positive (v : ℝ) (hv : |v| ≤ (15/1274 : ℝ)) :
    0 < realHorner ((e_common_E2_r8_U2_columns[7]?.getD []).map fractionValue) v := by
  apply primitiveLowerCheck_column_positive e_common_E2_r8_U2_columns ⟨15, 1274⟩ ⟨5625, 58779197975655775007277700780396642304⟩ e_common_E2_r8_U2 7 v
  · norm_num [e_common_E2_r8_U2]
  · norm_num [e_common_E2_r8_U2_columns]
  · norm_num
  · simpa only [fractionValue, Int.cast_ofNat, Nat.cast_ofNat] using hv
  · norm_num [e_common_E2_r8_U2]
  · exact cert_0454_E2_r8_U2_primitive_lower_polynomial_identity
  · simpa only [e_common_E2_r8_U2, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some] using
      fraction_positive_sound _ cert_0462_E2_r8_U2_closed_x_1_endpoint

theorem e_common_E2_r8_U2_numerator_endpoint_positive (q : ℝ) (hq : (29/49 : ℝ) ≤ q ∧ q ≤ 8/13) :
    0 < matrixValue numerator_E2_r8_U2 (q/(1-q)) 1 := by
  have hc : fractionValue (commonActivityCenter ⟨29, 20⟩ ⟨8, 5⟩) = (769/1274 : ℝ) := by
    norm_num [commonActivityCenter, Fraction.div, Fraction.add, Fraction.mul,
      Fraction.inv, Fraction.normalize, Fraction.one, Fraction.ofInt, fractionValue]
  apply commonColumns_endpoint_positive numerator_E2_r8_U2 e_common_E2_r8_U2_columns ⟨1, 4⟩ ⟨29, 20⟩ ⟨8, 5⟩ q
  · norm_num [numerator_E2_r8_U2]
  · norm_num
  · norm_num [commonActivityCenter, Fraction.div, Fraction.add, Fraction.mul,
      Fraction.inv, Fraction.normalize, Fraction.one, Fraction.ofInt]
  · norm_num [numerator_E2_r8_U2]
  · norm_num [numerator_E2_r8_U2]
  · linarith only [hq.2]
  · exact reconstruct_163_E2_r8_U2
  · change 0 < realHorner ((e_common_E2_r8_U2_columns[7]?.getD []).map fractionValue) _
    apply e_common_E2_r8_U2_last_column_positive
    rw [hc, abs_le]
    constructor <;> linarith only [hq.1, hq.2]

theorem e_common_E2_r8_U2_numerator_rectangle_positive (lam x : ℝ)
    (hlam : (29/20 : ℝ) ≤ lam ∧ lam ≤ 8/5) (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < matrixValue numerator_E2_r8_U2 lam x := by
  have hd : 0 < 1+lam := by linarith only [hlam.1]
  have hq : (29/49 : ℝ) ≤ lam/(1+lam) ∧ lam/(1+lam) ≤ 8/13 := by
    convert activity_projective_interval (29/20 : ℝ) (8/5 : ℝ) lam (by norm_num) hlam using 1 <;> norm_num
  have ht := parent_interval_parameter (1/4 : ℝ) x (by norm_num) hx
  rcases lt_or_eq_of_le hx.2 with hlt | rfl
  · have ht1 : (x-(1/4 : ℝ))/(1-(1/4 : ℝ)) < 1 := (div_lt_one (by norm_num)).mpr (by linarith only [hlt])
    have h := e_common_E2_r8_U2_numerator_positive (lam/(1+lam)) ((x-(1/4 : ℝ))/(1-(1/4 : ℝ))) hq ht.1 ht1
    rw [activity_projective_inverse lam (ne_of_gt hd), ht.2.2] at h
    exact h
  · have h := e_common_E2_r8_U2_numerator_endpoint_positive (lam/(1+lam)) hq
    rwa [activity_projective_inverse lam (ne_of_gt hd)] at h

theorem e_common_E2_r8_U3_last_column_positive (v : ℝ) (hv : |v| ≤ (15/1274 : ℝ)) :
    0 < realHorner ((e_common_E2_r8_U3_columns[7]?.getD []).map fractionValue) v := by
  apply primitiveLowerCheck_column_positive e_common_E2_r8_U3_columns ⟨15, 1274⟩ ⟨75, 23068759017133349688884497951490048⟩ e_common_E2_r8_U3 7 v
  · norm_num [e_common_E2_r8_U3]
  · norm_num [e_common_E2_r8_U3_columns]
  · norm_num
  · simpa only [fractionValue, Int.cast_ofNat, Nat.cast_ofNat] using hv
  · norm_num [e_common_E2_r8_U3]
  · exact cert_0465_E2_r8_U3_primitive_lower_polynomial_identity
  · simpa only [e_common_E2_r8_U3, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some] using
      fraction_positive_sound _ cert_0473_E2_r8_U3_closed_x_1_endpoint

theorem e_common_E2_r8_U3_numerator_endpoint_positive (q : ℝ) (hq : (29/49 : ℝ) ≤ q ∧ q ≤ 8/13) :
    0 < matrixValue numerator_E2_r8_U3 (q/(1-q)) 1 := by
  have hc : fractionValue (commonActivityCenter ⟨29, 20⟩ ⟨8, 5⟩) = (769/1274 : ℝ) := by
    norm_num [commonActivityCenter, Fraction.div, Fraction.add, Fraction.mul,
      Fraction.inv, Fraction.normalize, Fraction.one, Fraction.ofInt, fractionValue]
  apply commonColumns_endpoint_positive numerator_E2_r8_U3 e_common_E2_r8_U3_columns ⟨1, 4⟩ ⟨29, 20⟩ ⟨8, 5⟩ q
  · norm_num [numerator_E2_r8_U3]
  · norm_num
  · norm_num [commonActivityCenter, Fraction.div, Fraction.add, Fraction.mul,
      Fraction.inv, Fraction.normalize, Fraction.one, Fraction.ofInt]
  · norm_num [numerator_E2_r8_U3]
  · norm_num [numerator_E2_r8_U3]
  · linarith only [hq.2]
  · exact reconstruct_164_E2_r8_U3
  · change 0 < realHorner ((e_common_E2_r8_U3_columns[7]?.getD []).map fractionValue) _
    apply e_common_E2_r8_U3_last_column_positive
    rw [hc, abs_le]
    constructor <;> linarith only [hq.1, hq.2]

theorem e_common_E2_r8_U3_numerator_rectangle_positive (lam x : ℝ)
    (hlam : (29/20 : ℝ) ≤ lam ∧ lam ≤ 8/5) (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < matrixValue numerator_E2_r8_U3 lam x := by
  have hd : 0 < 1+lam := by linarith only [hlam.1]
  have hq : (29/49 : ℝ) ≤ lam/(1+lam) ∧ lam/(1+lam) ≤ 8/13 := by
    convert activity_projective_interval (29/20 : ℝ) (8/5 : ℝ) lam (by norm_num) hlam using 1 <;> norm_num
  have ht := parent_interval_parameter (1/4 : ℝ) x (by norm_num) hx
  rcases lt_or_eq_of_le hx.2 with hlt | rfl
  · have ht1 : (x-(1/4 : ℝ))/(1-(1/4 : ℝ)) < 1 := (div_lt_one (by norm_num)).mpr (by linarith only [hlt])
    have h := e_common_E2_r8_U3_numerator_positive (lam/(1+lam)) ((x-(1/4 : ℝ))/(1-(1/4 : ℝ))) hq ht.1 ht1
    rw [activity_projective_inverse lam (ne_of_gt hd), ht.2.2] at h
    exact h
  · have h := e_common_E2_r8_U3_numerator_endpoint_positive (lam/(1+lam)) hq
    rwa [activity_projective_inverse lam (ne_of_gt hd)] at h

theorem e_common_E2_r8_D_last_column_positive (v : ℝ) (hv : |v| ≤ (15/1274 : ℝ)) :
    0 < realHorner ((e_common_E2_r8_D_columns[4]?.getD []).map fractionValue) v := by
  apply primitiveLowerCheck_column_positive e_common_E2_r8_D_columns ⟨15, 1274⟩ ⟨5, 21075005614208⟩ e_common_E2_r8_D 4 v
  · norm_num [e_common_E2_r8_D]
  · norm_num [e_common_E2_r8_D_columns]
  · norm_num
  · simpa only [fractionValue, Int.cast_ofNat, Nat.cast_ofNat] using hv
  · norm_num [e_common_E2_r8_D]
  · exact cert_0477_E2_r8_D_primitive_lower_polynomial_identity
  · simpa only [e_common_E2_r8_D, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some] using
      fraction_positive_sound _ cert_0482_E2_r8_D_strict_lower_coefficient_4

theorem e_common_E2_r8_D_numerator_endpoint_positive (q : ℝ) (hq : (29/49 : ℝ) ≤ q ∧ q ≤ 8/13) :
    0 < matrixValue numerator_E2_r8_D (q/(1-q)) 1 := by
  have hc : fractionValue (commonActivityCenter ⟨29, 20⟩ ⟨8, 5⟩) = (769/1274 : ℝ) := by
    norm_num [commonActivityCenter, Fraction.div, Fraction.add, Fraction.mul,
      Fraction.inv, Fraction.normalize, Fraction.one, Fraction.ofInt, fractionValue]
  apply commonColumns_endpoint_positive numerator_E2_r8_D e_common_E2_r8_D_columns ⟨1, 4⟩ ⟨29, 20⟩ ⟨8, 5⟩ q
  · norm_num [numerator_E2_r8_D]
  · norm_num
  · norm_num [commonActivityCenter, Fraction.div, Fraction.add, Fraction.mul,
      Fraction.inv, Fraction.normalize, Fraction.one, Fraction.ofInt]
  · norm_num [numerator_E2_r8_D]
  · norm_num [numerator_E2_r8_D]
  · linarith only [hq.2]
  · exact reconstruct_165_E2_r8_D
  · change 0 < realHorner ((e_common_E2_r8_D_columns[4]?.getD []).map fractionValue) _
    apply e_common_E2_r8_D_last_column_positive
    rw [hc, abs_le]
    constructor <;> linarith only [hq.1, hq.2]

theorem e_common_E2_r8_D_numerator_rectangle_positive (lam x : ℝ)
    (hlam : (29/20 : ℝ) ≤ lam ∧ lam ≤ 8/5) (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < matrixValue numerator_E2_r8_D lam x := by
  have hd : 0 < 1+lam := by linarith only [hlam.1]
  have hq : (29/49 : ℝ) ≤ lam/(1+lam) ∧ lam/(1+lam) ≤ 8/13 := by
    convert activity_projective_interval (29/20 : ℝ) (8/5 : ℝ) lam (by norm_num) hlam using 1 <;> norm_num
  have ht := parent_interval_parameter (1/4 : ℝ) x (by norm_num) hx
  rcases lt_or_eq_of_le hx.2 with hlt | rfl
  · have ht1 : (x-(1/4 : ℝ))/(1-(1/4 : ℝ)) < 1 := (div_lt_one (by norm_num)).mpr (by linarith only [hlt])
    have h := e_common_E2_r8_D_numerator_positive (lam/(1+lam)) ((x-(1/4 : ℝ))/(1-(1/4 : ℝ))) hq ht.1 ht1
    rw [activity_projective_inverse lam (ne_of_gt hd), ht.2.2] at h
    exact h
  · have h := e_common_E2_r8_D_numerator_endpoint_positive (lam/(1+lam)) hq
    rwa [activity_projective_inverse lam (ne_of_gt hd)] at h

end F4Heavy.Analysis
