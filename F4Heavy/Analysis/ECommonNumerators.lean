module

public import F4Heavy.Analysis.CommonTransformSemantics
public import F4Heavy.Analysis.ECommonEnvelopes
public import F4Heavy.Finite.Reconstruction.Function15
public import F4Heavy.Finite.Reconstruction.Function16
public import F4Heavy.Finite.Reconstruction.Function17
public import F4Heavy.Finite.Reconstruction.Function19
public import F4Heavy.Finite.Reconstruction.Function20
public import F4Heavy.Finite.Reconstruction.Function21
public import F4Heavy.Finite.Reconstruction.Function22
public import F4Heavy.Finite.Reconstruction.Function23
public import F4Heavy.Finite.Reconstruction.Function24
public import F4Heavy.Finite.Reconstruction.Function25
public import F4Heavy.Finite.Reconstruction.Function26

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Heavy.Finite

theorem e_common_E1_r8_H0_numerator_positive (q t : ℝ)
    (hq : (13/23 : ℝ) ≤ q ∧ q ≤ 29/49) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    0 < matrixValue numerator_E1_r8_H0 (q/(1-q)) ((1/4 : ℝ)+(1-(1/4 : ℝ))*t) := by
  have hc : fractionValue (commonActivityCenter ⟨13, 10⟩ ⟨29, 20⟩) = (652/1127 : ℝ) := by
    norm_num [commonActivityCenter, Fraction.div, Fraction.add, Fraction.mul,
      Fraction.inv, Fraction.normalize, Fraction.one, Fraction.ofInt, fractionValue]
  have hxl : fractionValue ⟨1, 4⟩ = (1/4 : ℝ) := by norm_num [fractionValue]
  rw [← hxl]
  apply commonColumns_original_positive numerator_E1_r8_H0 e_common_E1_r8_H0_columns ⟨1, 4⟩ ⟨13, 10⟩ ⟨29, 20⟩ q t
  · norm_num [numerator_E1_r8_H0]
  · norm_num
  · norm_num [commonActivityCenter, Fraction.div, Fraction.add, Fraction.mul,
      Fraction.inv, Fraction.normalize, Fraction.one, Fraction.ofInt]
  · norm_num [numerator_E1_r8_H0]
  · norm_num [numerator_E1_r8_H0]
  · linarith only [hq.2]
  · exact ht1
  · exact reconstruct_154_E1_r8_H0
  · unfold matrixValue
    apply e_common_E1_r8_H0_envelope_positive
    · rw [hc, abs_le]
      constructor <;> linarith only [hq.1, hq.2]
    · exact div_nonneg ht0 (by linarith only [ht1])

theorem e_common_E1_r8_U0_numerator_positive (q t : ℝ)
    (hq : (13/23 : ℝ) ≤ q ∧ q ≤ 29/49) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    0 < matrixValue numerator_E1_r8_U0 (q/(1-q)) ((1/4 : ℝ)+(1-(1/4 : ℝ))*t) := by
  have hc : fractionValue (commonActivityCenter ⟨13, 10⟩ ⟨29, 20⟩) = (652/1127 : ℝ) := by
    norm_num [commonActivityCenter, Fraction.div, Fraction.add, Fraction.mul,
      Fraction.inv, Fraction.normalize, Fraction.one, Fraction.ofInt, fractionValue]
  have hxl : fractionValue ⟨1, 4⟩ = (1/4 : ℝ) := by norm_num [fractionValue]
  rw [← hxl]
  apply commonColumns_original_positive numerator_E1_r8_U0 e_common_E1_r8_U0_columns ⟨1, 4⟩ ⟨13, 10⟩ ⟨29, 20⟩ q t
  · norm_num [numerator_E1_r8_U0]
  · norm_num
  · norm_num [commonActivityCenter, Fraction.div, Fraction.add, Fraction.mul,
      Fraction.inv, Fraction.normalize, Fraction.one, Fraction.ofInt]
  · norm_num [numerator_E1_r8_U0]
  · norm_num [numerator_E1_r8_U0]
  · linarith only [hq.2]
  · exact ht1
  · exact reconstruct_155_E1_r8_U0
  · unfold matrixValue
    apply e_common_E1_r8_U0_envelope_positive
    · rw [hc, abs_le]
      constructor <;> linarith only [hq.1, hq.2]
    · exact div_nonneg ht0 (by linarith only [ht1])

theorem e_common_E1_r8_U1_numerator_positive (q t : ℝ)
    (hq : (13/23 : ℝ) ≤ q ∧ q ≤ 29/49) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    0 < matrixValue numerator_E1_r8_U1 (q/(1-q)) ((1/4 : ℝ)+(1-(1/4 : ℝ))*t) := by
  have hc : fractionValue (commonActivityCenter ⟨13, 10⟩ ⟨29, 20⟩) = (652/1127 : ℝ) := by
    norm_num [commonActivityCenter, Fraction.div, Fraction.add, Fraction.mul,
      Fraction.inv, Fraction.normalize, Fraction.one, Fraction.ofInt, fractionValue]
  have hxl : fractionValue ⟨1, 4⟩ = (1/4 : ℝ) := by norm_num [fractionValue]
  rw [← hxl]
  apply commonColumns_original_positive numerator_E1_r8_U1 e_common_E1_r8_U1_columns ⟨1, 4⟩ ⟨13, 10⟩ ⟨29, 20⟩ q t
  · norm_num [numerator_E1_r8_U1]
  · norm_num
  · norm_num [commonActivityCenter, Fraction.div, Fraction.add, Fraction.mul,
      Fraction.inv, Fraction.normalize, Fraction.one, Fraction.ofInt]
  · norm_num [numerator_E1_r8_U1]
  · norm_num [numerator_E1_r8_U1]
  · linarith only [hq.2]
  · exact ht1
  · exact reconstruct_156_E1_r8_U1
  · unfold matrixValue
    apply e_common_E1_r8_U1_envelope_positive
    · rw [hc, abs_le]
      constructor <;> linarith only [hq.1, hq.2]
    · exact div_nonneg ht0 (by linarith only [ht1])

theorem e_common_E1_r8_U3_numerator_positive (q t : ℝ)
    (hq : (13/23 : ℝ) ≤ q ∧ q ≤ 29/49) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    0 < matrixValue numerator_E1_r8_U3 (q/(1-q)) ((1/4 : ℝ)+(1-(1/4 : ℝ))*t) := by
  have hc : fractionValue (commonActivityCenter ⟨13, 10⟩ ⟨29, 20⟩) = (652/1127 : ℝ) := by
    norm_num [commonActivityCenter, Fraction.div, Fraction.add, Fraction.mul,
      Fraction.inv, Fraction.normalize, Fraction.one, Fraction.ofInt, fractionValue]
  have hxl : fractionValue ⟨1, 4⟩ = (1/4 : ℝ) := by norm_num [fractionValue]
  rw [← hxl]
  apply commonColumns_original_positive numerator_E1_r8_U3 e_common_E1_r8_U3_columns ⟨1, 4⟩ ⟨13, 10⟩ ⟨29, 20⟩ q t
  · norm_num [numerator_E1_r8_U3]
  · norm_num
  · norm_num [commonActivityCenter, Fraction.div, Fraction.add, Fraction.mul,
      Fraction.inv, Fraction.normalize, Fraction.one, Fraction.ofInt]
  · norm_num [numerator_E1_r8_U3]
  · norm_num [numerator_E1_r8_U3]
  · linarith only [hq.2]
  · exact ht1
  · exact reconstruct_158_E1_r8_U3
  · unfold matrixValue
    apply e_common_E1_r8_U3_envelope_positive
    · rw [hc, abs_le]
      constructor <;> linarith only [hq.1, hq.2]
    · exact div_nonneg ht0 (by linarith only [ht1])

theorem e_common_E1_r8_D_numerator_positive (q t : ℝ)
    (hq : (13/23 : ℝ) ≤ q ∧ q ≤ 29/49) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    0 < matrixValue numerator_E1_r8_D (q/(1-q)) ((1/4 : ℝ)+(1-(1/4 : ℝ))*t) := by
  have hc : fractionValue (commonActivityCenter ⟨13, 10⟩ ⟨29, 20⟩) = (652/1127 : ℝ) := by
    norm_num [commonActivityCenter, Fraction.div, Fraction.add, Fraction.mul,
      Fraction.inv, Fraction.normalize, Fraction.one, Fraction.ofInt, fractionValue]
  have hxl : fractionValue ⟨1, 4⟩ = (1/4 : ℝ) := by norm_num [fractionValue]
  rw [← hxl]
  apply commonColumns_original_positive numerator_E1_r8_D e_common_E1_r8_D_columns ⟨1, 4⟩ ⟨13, 10⟩ ⟨29, 20⟩ q t
  · norm_num [numerator_E1_r8_D]
  · norm_num
  · norm_num [commonActivityCenter, Fraction.div, Fraction.add, Fraction.mul,
      Fraction.inv, Fraction.normalize, Fraction.one, Fraction.ofInt]
  · norm_num [numerator_E1_r8_D]
  · norm_num [numerator_E1_r8_D]
  · linarith only [hq.2]
  · exact ht1
  · exact reconstruct_159_E1_r8_D
  · unfold matrixValue
    apply e_common_E1_r8_D_envelope_positive
    · rw [hc, abs_le]
      constructor <;> linarith only [hq.1, hq.2]
    · exact div_nonneg ht0 (by linarith only [ht1])

theorem e_common_E2_r8_H0_numerator_positive (q t : ℝ)
    (hq : (29/49 : ℝ) ≤ q ∧ q ≤ 8/13) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    0 < matrixValue numerator_E2_r8_H0 (q/(1-q)) ((1/4 : ℝ)+(1-(1/4 : ℝ))*t) := by
  have hc : fractionValue (commonActivityCenter ⟨29, 20⟩ ⟨8, 5⟩) = (769/1274 : ℝ) := by
    norm_num [commonActivityCenter, Fraction.div, Fraction.add, Fraction.mul,
      Fraction.inv, Fraction.normalize, Fraction.one, Fraction.ofInt, fractionValue]
  have hxl : fractionValue ⟨1, 4⟩ = (1/4 : ℝ) := by norm_num [fractionValue]
  rw [← hxl]
  apply commonColumns_original_positive numerator_E2_r8_H0 e_common_E2_r8_H0_columns ⟨1, 4⟩ ⟨29, 20⟩ ⟨8, 5⟩ q t
  · norm_num [numerator_E2_r8_H0]
  · norm_num
  · norm_num [commonActivityCenter, Fraction.div, Fraction.add, Fraction.mul,
      Fraction.inv, Fraction.normalize, Fraction.one, Fraction.ofInt]
  · norm_num [numerator_E2_r8_H0]
  · norm_num [numerator_E2_r8_H0]
  · linarith only [hq.2]
  · exact ht1
  · exact reconstruct_160_E2_r8_H0
  · unfold matrixValue
    apply e_common_E2_r8_H0_envelope_positive
    · rw [hc, abs_le]
      constructor <;> linarith only [hq.1, hq.2]
    · exact div_nonneg ht0 (by linarith only [ht1])

theorem e_common_E2_r8_U0_numerator_positive (q t : ℝ)
    (hq : (29/49 : ℝ) ≤ q ∧ q ≤ 8/13) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    0 < matrixValue numerator_E2_r8_U0 (q/(1-q)) ((1/4 : ℝ)+(1-(1/4 : ℝ))*t) := by
  have hc : fractionValue (commonActivityCenter ⟨29, 20⟩ ⟨8, 5⟩) = (769/1274 : ℝ) := by
    norm_num [commonActivityCenter, Fraction.div, Fraction.add, Fraction.mul,
      Fraction.inv, Fraction.normalize, Fraction.one, Fraction.ofInt, fractionValue]
  have hxl : fractionValue ⟨1, 4⟩ = (1/4 : ℝ) := by norm_num [fractionValue]
  rw [← hxl]
  apply commonColumns_original_positive numerator_E2_r8_U0 e_common_E2_r8_U0_columns ⟨1, 4⟩ ⟨29, 20⟩ ⟨8, 5⟩ q t
  · norm_num [numerator_E2_r8_U0]
  · norm_num
  · norm_num [commonActivityCenter, Fraction.div, Fraction.add, Fraction.mul,
      Fraction.inv, Fraction.normalize, Fraction.one, Fraction.ofInt]
  · norm_num [numerator_E2_r8_U0]
  · norm_num [numerator_E2_r8_U0]
  · linarith only [hq.2]
  · exact ht1
  · exact reconstruct_161_E2_r8_U0
  · unfold matrixValue
    apply e_common_E2_r8_U0_envelope_positive
    · rw [hc, abs_le]
      constructor <;> linarith only [hq.1, hq.2]
    · exact div_nonneg ht0 (by linarith only [ht1])

theorem e_common_E2_r8_U1_numerator_positive (q t : ℝ)
    (hq : (29/49 : ℝ) ≤ q ∧ q ≤ 8/13) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    0 < matrixValue numerator_E2_r8_U1 (q/(1-q)) ((1/4 : ℝ)+(1-(1/4 : ℝ))*t) := by
  have hc : fractionValue (commonActivityCenter ⟨29, 20⟩ ⟨8, 5⟩) = (769/1274 : ℝ) := by
    norm_num [commonActivityCenter, Fraction.div, Fraction.add, Fraction.mul,
      Fraction.inv, Fraction.normalize, Fraction.one, Fraction.ofInt, fractionValue]
  have hxl : fractionValue ⟨1, 4⟩ = (1/4 : ℝ) := by norm_num [fractionValue]
  rw [← hxl]
  apply commonColumns_original_positive numerator_E2_r8_U1 e_common_E2_r8_U1_columns ⟨1, 4⟩ ⟨29, 20⟩ ⟨8, 5⟩ q t
  · norm_num [numerator_E2_r8_U1]
  · norm_num
  · norm_num [commonActivityCenter, Fraction.div, Fraction.add, Fraction.mul,
      Fraction.inv, Fraction.normalize, Fraction.one, Fraction.ofInt]
  · norm_num [numerator_E2_r8_U1]
  · norm_num [numerator_E2_r8_U1]
  · linarith only [hq.2]
  · exact ht1
  · exact reconstruct_162_E2_r8_U1
  · unfold matrixValue
    apply e_common_E2_r8_U1_envelope_positive
    · rw [hc, abs_le]
      constructor <;> linarith only [hq.1, hq.2]
    · exact div_nonneg ht0 (by linarith only [ht1])

theorem e_common_E2_r8_U2_numerator_positive (q t : ℝ)
    (hq : (29/49 : ℝ) ≤ q ∧ q ≤ 8/13) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    0 < matrixValue numerator_E2_r8_U2 (q/(1-q)) ((1/4 : ℝ)+(1-(1/4 : ℝ))*t) := by
  have hc : fractionValue (commonActivityCenter ⟨29, 20⟩ ⟨8, 5⟩) = (769/1274 : ℝ) := by
    norm_num [commonActivityCenter, Fraction.div, Fraction.add, Fraction.mul,
      Fraction.inv, Fraction.normalize, Fraction.one, Fraction.ofInt, fractionValue]
  have hxl : fractionValue ⟨1, 4⟩ = (1/4 : ℝ) := by norm_num [fractionValue]
  rw [← hxl]
  apply commonColumns_original_positive numerator_E2_r8_U2 e_common_E2_r8_U2_columns ⟨1, 4⟩ ⟨29, 20⟩ ⟨8, 5⟩ q t
  · norm_num [numerator_E2_r8_U2]
  · norm_num
  · norm_num [commonActivityCenter, Fraction.div, Fraction.add, Fraction.mul,
      Fraction.inv, Fraction.normalize, Fraction.one, Fraction.ofInt]
  · norm_num [numerator_E2_r8_U2]
  · norm_num [numerator_E2_r8_U2]
  · linarith only [hq.2]
  · exact ht1
  · exact reconstruct_163_E2_r8_U2
  · unfold matrixValue
    apply e_common_E2_r8_U2_envelope_positive
    · rw [hc, abs_le]
      constructor <;> linarith only [hq.1, hq.2]
    · exact div_nonneg ht0 (by linarith only [ht1])

theorem e_common_E2_r8_U3_numerator_positive (q t : ℝ)
    (hq : (29/49 : ℝ) ≤ q ∧ q ≤ 8/13) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    0 < matrixValue numerator_E2_r8_U3 (q/(1-q)) ((1/4 : ℝ)+(1-(1/4 : ℝ))*t) := by
  have hc : fractionValue (commonActivityCenter ⟨29, 20⟩ ⟨8, 5⟩) = (769/1274 : ℝ) := by
    norm_num [commonActivityCenter, Fraction.div, Fraction.add, Fraction.mul,
      Fraction.inv, Fraction.normalize, Fraction.one, Fraction.ofInt, fractionValue]
  have hxl : fractionValue ⟨1, 4⟩ = (1/4 : ℝ) := by norm_num [fractionValue]
  rw [← hxl]
  apply commonColumns_original_positive numerator_E2_r8_U3 e_common_E2_r8_U3_columns ⟨1, 4⟩ ⟨29, 20⟩ ⟨8, 5⟩ q t
  · norm_num [numerator_E2_r8_U3]
  · norm_num
  · norm_num [commonActivityCenter, Fraction.div, Fraction.add, Fraction.mul,
      Fraction.inv, Fraction.normalize, Fraction.one, Fraction.ofInt]
  · norm_num [numerator_E2_r8_U3]
  · norm_num [numerator_E2_r8_U3]
  · linarith only [hq.2]
  · exact ht1
  · exact reconstruct_164_E2_r8_U3
  · unfold matrixValue
    apply e_common_E2_r8_U3_envelope_positive
    · rw [hc, abs_le]
      constructor <;> linarith only [hq.1, hq.2]
    · exact div_nonneg ht0 (by linarith only [ht1])

theorem e_common_E2_r8_D_numerator_positive (q t : ℝ)
    (hq : (29/49 : ℝ) ≤ q ∧ q ≤ 8/13) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    0 < matrixValue numerator_E2_r8_D (q/(1-q)) ((1/4 : ℝ)+(1-(1/4 : ℝ))*t) := by
  have hc : fractionValue (commonActivityCenter ⟨29, 20⟩ ⟨8, 5⟩) = (769/1274 : ℝ) := by
    norm_num [commonActivityCenter, Fraction.div, Fraction.add, Fraction.mul,
      Fraction.inv, Fraction.normalize, Fraction.one, Fraction.ofInt, fractionValue]
  have hxl : fractionValue ⟨1, 4⟩ = (1/4 : ℝ) := by norm_num [fractionValue]
  rw [← hxl]
  apply commonColumns_original_positive numerator_E2_r8_D e_common_E2_r8_D_columns ⟨1, 4⟩ ⟨29, 20⟩ ⟨8, 5⟩ q t
  · norm_num [numerator_E2_r8_D]
  · norm_num
  · norm_num [commonActivityCenter, Fraction.div, Fraction.add, Fraction.mul,
      Fraction.inv, Fraction.normalize, Fraction.one, Fraction.ofInt]
  · norm_num [numerator_E2_r8_D]
  · norm_num [numerator_E2_r8_D]
  · linarith only [hq.2]
  · exact ht1
  · exact reconstruct_165_E2_r8_D
  · unfold matrixValue
    apply e_common_E2_r8_D_envelope_positive
    · rw [hc, abs_le]
      constructor <;> linarith only [hq.1, hq.2]
    · exact div_nonneg ht0 (by linarith only [ht1])

end F4Heavy.Analysis
