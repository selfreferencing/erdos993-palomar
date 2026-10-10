module

public import F4Heavy.Analysis.EFormulaE1_U0
public import F4Heavy.Analysis.EFormulaE1_U1
public import F4Heavy.Analysis.EFormulaE1_U2
public import F4Heavy.Analysis.EFormulaE1_U3
public import F4Heavy.Analysis.EFormulaE2_U0
public import F4Heavy.Analysis.EFormulaE2_U1
public import F4Heavy.Analysis.EFormulaE2_U2
public import F4Heavy.Analysis.EFormulaE2_U3
public import F4Heavy.Analysis.ESupportResponse
public import F4Heavy.Analysis.EEndpointReduction
public import F4Heavy.Analysis.MixedSupport
public import Mathlib.Tactic.IntervalCases

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

noncomputable def eUpperParentX (r : Row) (lam x : ℝ) : ℝ :=
  eParentBaseX r lam x+1-eProbabilityX lam x
noncomputable def eUpperA (r : Row) (lam x : ℝ) : ℝ :=
  eProbabilityX lam x*((15/16)*eHeavyKX r lam x-eUpperParentX r lam x)/parentLogLower r lam x
noncomputable def eUpperB (r : Row) (lam x : ℝ) : ℝ := eProbabilityX lam x*beta r lam
noncomputable def eUpperC (r : Row) (lam x : ℝ) : ℝ :=
  eProbabilityX lam x*(2*eUpperParentX r lam x-alpha r lam-beta r lam)
noncomputable def eUpperD (r : Row) (lam x : ℝ) : ℝ :=
  gamma r lam-delta r lam-eProbabilityX lam x*parentLogUpper r lam x*eUpperParentX r lam x

theorem eUFormula_response_coefficients (r : Row) (lam x h L : ℝ)
    (hlo : parentLogLower r lam x ≠ 0) :
    eUFormula r lam x h L = parentLogLower r lam x*
      responseNumerator (eUpperA r lam x) (eUpperB r lam x) (eUpperC r lam x)
        (eUpperD r lam x) (delta r lam) L h :=
  eUFormula_response_numerator r lam x h L hlo

theorem e_upper_vertices_positive (r : Row) (lam x : ℝ)
    (he : r = .E1 ∨ r = .E2) (hr : InRow r lam)
    (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) (i : Fin 4) :
    0 < eUFormula r lam x (eSupportVertex r lam i) (eSupportHeight r lam i) := by
  rcases i with ⟨i, hi⟩
  rcases he with rfl | rfl
  · interval_cases i
    · exact e_record_E1_U0_formula_positive lam x hr hx
    · exact e_record_E1_U1_formula_positive lam x hr hx
    · exact e_record_E1_U2_formula_positive lam x hr hx
    · exact e_record_E1_U3_formula_positive lam x hr hx
  · interval_cases i
    · exact e_record_E2_U0_formula_positive lam x hr hx
    · exact e_record_E2_U1_formula_positive lam x hr hx
    · exact e_record_E2_U2_formula_positive lam x hr hx
    · exact e_record_E2_U3_formula_positive lam x hr hx

theorem parentLogLower_positive_on_unit (r : Row) (lam x : ℝ)
    (hr : InRow r lam) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : 0 < parentLogLower r lam x := by
  exact add_pos_of_pos_of_nonneg (activityLogLower_correct r lam hr).1
    (div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hx1)) (by positivity))

theorem row_beta_pos (r : Row) (lam : ℝ) (hr : InRow r lam) : 0 < beta r lam := by
  cases r <;> norm_num [InRow, rowData] at hr <;>
    simp only [beta, field, rowData] <;> nlinarith [hr.1, hr.2]

theorem e_upper_response_vertices_positive (r : Row) (lam x : ℝ)
    (he : r = .E1 ∨ r = .E2) (hr : InRow r lam)
    (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) (i : Fin 4) :
    0 < responseNumerator (eUpperA r lam x) (eUpperB r lam x) (eUpperC r lam x)
      (eUpperD r lam x) (delta r lam) (eSupportHeight r lam i) (eSupportVertex r lam i) := by
  have hlo := parentLogLower_positive_on_unit r lam x hr (by linarith only [hx.1]) hx.2
  have hW := e_upper_vertices_positive r lam x he hr hx i
  rw [eUFormula_response_coefficients r lam x _ _ (ne_of_gt hlo)] at hW
  exact (mul_pos_iff_of_pos_left hlo).mp hW

theorem e_upper_curvature_negative (r : Row) (lam x : ℝ)
    (he : r = .E1 ∨ r = .E2) (hr : InRow r lam)
    (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) : eUpperD r lam x < 0 := by
  have h := eDFormula_positive r lam x he hr hx
  unfold eDFormula at h
  unfold eUpperD eUpperParentX
  linarith only [h]

theorem e_upper_response_vertex_gains (r : Row) (lam x : ℝ)
    (he : r = .E1 ∨ r = .E2) (hr : InRow r lam)
    (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) (i : Fin 4) :
    0 < delta r lam+eUpperD r lam x*eSupportHeight r lam i := by
  have hlam := inRow_activity_pos r lam hr
  have hx0 : 0 ≤ x := by linarith only [hx.1]
  have hb : 0 ≤ eUpperB r lam x := by
    unfold eUpperB eProbabilityX
    exact mul_nonneg (by positivity) (row_beta_pos r lam hr).le
  have hG := e_support_response_gains r lam (eUpperA r lam x) (eUpperB r lam x)
    (eUpperC r lam x) (eUpperD r lam x) (delta r lam) he hr (row_delta_pos r lam hr)
    hb (e_upper_curvature_negative r lam x he hr hx).le
    (e_upper_response_vertices_positive r lam x he hr hx 0)
    (e_upper_response_vertices_positive r lam x he hr hx 1)
    (e_upper_response_vertices_positive r lam x he hr hx 2)
  rcases i with ⟨i, hi⟩
  interval_cases i
  · exact hG.1
  · exact hG.2.1
  · exact hG.2.2.1
  · exact hG.2.2.2

theorem e_upper_response_chord_positive (r : Row) (lam x t : ℝ) (i j : Fin 4)
    (he : r = .E1 ∨ r = .E2) (hr : InRow r lam)
    (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < responseNumerator (eUpperA r lam x) (eUpperB r lam x) (eUpperC r lam x)
      (eUpperD r lam x) (delta r lam)
      ((1-t)*eSupportHeight r lam i+t*eSupportHeight r lam j)
      ((1-t)*eSupportVertex r lam i+t*eSupportVertex r lam j) := by
  exact response_cleared_chord_positive _ _ _ _ _ _ _ _ _ t
    (row_delta_pos r lam hr).le (e_upper_curvature_negative r lam x he hr hx).le ht0 ht1
    (e_upper_response_vertex_gains r lam x he hr hx i)
    (e_upper_response_vertex_gains r lam x he hr hx j)
    (e_upper_response_vertices_positive r lam x he hr hx i)
    (e_upper_response_vertices_positive r lam x he hr hx j)

end F4Heavy.Analysis
