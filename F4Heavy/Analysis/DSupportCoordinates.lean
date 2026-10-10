module

public import F4Heavy.Analysis.DZeroVertexCoordinate
public import Mathlib.Tactic.FinCases

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

noncomputable def dInterceptNum0 (v : ℝ) : ℝ :=
  (-3326942783/2000000000)*dSupportDen v+
    ((-23862523/16000000)-(-3326942783/2000000000))*dSupportNum v
noncomputable def dInterceptNum1 (v : ℝ) : ℝ :=
  (-60258643/1000000000)*dSupportDen v+
    ((174865111/5000000000)-(-60258643/1000000000))*dSupportNum v
noncomputable def dInterceptNum2 (v : ℝ) : ℝ :=
  (3819556393/5000000000)*dSupportDen v+
    ((8346294633/10000000000)-(3819556393/5000000000))*dSupportNum v

noncomputable def dVertexNum (v : ℝ) : Fin 4 → ℝ
  | 0 => dZeroVertexNum v
  | 1 => (dInterceptNum1 v-dInterceptNum0 v)/((11/5)-(3/10))
  | 2 => (dInterceptNum2 v-dInterceptNum1 v)/((3/10)-(-3/5))
  | 3 => dSupportDen v
noncomputable def dHeightNum (v : ℝ) : Fin 4 → ℝ
  | 0 => 0
  | 1 => (11/5)*dVertexNum v 1+dInterceptNum0 v
  | 2 => (3/10)*dVertexNum v 2+dInterceptNum1 v
  | 3 => (-3/5)*dSupportDen v+dInterceptNum2 v

theorem d_intercepts_coordinate (v : ℝ) (hq : 1-v ≠ 0) (hH : dSupportDen v ≠ 0) :
    dSupportIntercept0 (dActivity v) = dInterceptNum0 v/dSupportDen v ∧
    dSupportIntercept1 (dActivity v) = dInterceptNum1 v/dSupportDen v ∧
    dSupportIntercept2 (dActivity v) = dInterceptNum2 v/dSupportDen v := by
  unfold dSupportIntercept0 dSupportIntercept1 dSupportIntercept2
  rw [d_support_weight_coordinate v hq hH]
  unfold dInterceptNum0 dInterceptNum1 dInterceptNum2
  constructor
  · field_simp
    <;> ring
  constructor <;> field_simp <;> ring

theorem d_vertex_coordinate (v : ℝ) (i : Fin 4) (hq : 1-v ≠ 0) (hH : dSupportDen v ≠ 0) :
    dSupportVertex (dActivity v) i = dVertexNum v i/dSupportDen v := by
  obtain ⟨h0, h1, h2⟩ := d_intercepts_coordinate v hq hH
  fin_cases i
  · exact d_zero_vertex_coordinate v hq hH
  · simp only [dSupportVertex, dVertexNum, h0, h1]
    field_simp
    <;> ring
  · simp only [dSupportVertex, dVertexNum, h1, h2]
    field_simp
    <;> ring
  · simp only [dSupportVertex, dVertexNum, div_self hH]

theorem d_height_coordinate (v : ℝ) (i : Fin 4) (hq : 1-v ≠ 0) (hH : dSupportDen v ≠ 0) :
    dSupportHeight (dActivity v) i = dHeightNum v i/dSupportDen v := by
  obtain ⟨h0, h1, h2⟩ := d_intercepts_coordinate v hq hH
  fin_cases i
  · simp only [dSupportHeight, dHeightNum, zero_div]
  · simp only [dSupportHeight, dHeightNum, d_vertex_coordinate v 1 hq hH, h0]
    field_simp
  · simp only [dSupportHeight, dHeightNum, d_vertex_coordinate v 2 hq hH, h1]
    field_simp
  · simp only [dSupportHeight, dHeightNum, h2]
    field_simp

end F4Heavy.Analysis
