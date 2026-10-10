module

public import F4Heavy.Analysis.HFormulaCoordinates
public import F4Heavy.Analysis.DHSupportGeometry
public import Mathlib.Tactic.FinCases

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

noncomputable def hSupportDen (v : ℝ) : ℝ := 3*287682072451*(1-v^2)
noncomputable def hSupportNum (v : ℝ) : ℝ := 1000000000000*(6*v-4*v^3)
noncomputable def hInterceptNum0 (v : ℝ) : ℝ :=
  (-15097571481/10000000000)*hSupportDen v+
    ((-3484969137/2500000000)-(-15097571481/10000000000))*hSupportNum v
noncomputable def hInterceptNum1 (v : ℝ) : ℝ :=
  (516659173/5000000000)*hSupportDen v+
    ((1762035691/10000000000)-(516659173/5000000000))*hSupportNum v
noncomputable def hInterceptNum2 (v : ℝ) : ℝ :=
  (8871047271/10000000000)*hSupportDen v+
    ((9444767991/10000000000)-(8871047271/10000000000))*hSupportNum v
noncomputable def hInterceptNum4 (v : ℝ) : ℝ :=
  (10178601269/2500000000)*hSupportDen v+
    ((10226130853/2500000000)-(10178601269/2500000000))*hSupportNum v
noncomputable def hVertexNum (v : ℝ) : Fin 5 → ℝ
  | 0 => -hInterceptNum0 v/(12/5)
  | 1 => (hInterceptNum1 v-hInterceptNum0 v)/((12/5)-(3/10))
  | 2 => (hInterceptNum2 v-hInterceptNum1 v)/((3/10)-(-3/5))
  | 3 => (hInterceptNum4 v-hInterceptNum2 v)/((-3/5)-(-4))
  | 4 => hSupportDen v
noncomputable def hHeightNum (v : ℝ) : Fin 5 → ℝ
  | 0 => 0
  | 1 => (12/5)*hVertexNum v 1+hInterceptNum0 v
  | 2 => (3/10)*hVertexNum v 2+hInterceptNum1 v
  | 3 => (-3/5)*hVertexNum v 3+hInterceptNum2 v
  | 4 => (-4)*hSupportDen v+hInterceptNum4 v

theorem h_activity_transform_forward (v : ℝ) (hq : 1-v ≠ 0) :
    (hActivity v-(7/4 : ℝ))/(hActivity v+(7/4 : ℝ)) = v := by
  have he : hActivity v+(7/4 : ℝ) = (7/2)/(1-v) := by
    unfold hActivity
    field_simp
    <;> ring
  rw [he]
  unfold hActivity
  field_simp
  <;> ring

theorem h_support_den_positive (v : ℝ) (hv : 0 ≤ v ∧ v ≤ (1/7 : ℝ)) :
    0 < hSupportDen v := by
  have hh : 0 < 1-v^2 := by nlinarith only [hv.1, hv.2, sq_nonneg (1-v)]
  unfold hSupportDen
  positivity

theorem h_support_weight_coordinate (v : ℝ) (hq : 1-v ≠ 0) (hH : hSupportDen v ≠ 0) :
    hSupportWeight (hActivity v) = hSupportNum v/hSupportDen v := by
  unfold hSupportWeight
  rw [h_activity_transform_forward v hq]
  unfold hSupportNum hSupportDen
  have hh : 1-v^2 ≠ 0 := by
    intro hh
    apply hH
    simp only [hSupportDen, hh, mul_zero]
  field_simp
  <;> ring

theorem h_intercepts_coordinate (v : ℝ) (hq : 1-v ≠ 0) (hH : hSupportDen v ≠ 0) :
    hSupportIntercept0 (hActivity v) = hInterceptNum0 v/hSupportDen v ∧
    hSupportIntercept1 (hActivity v) = hInterceptNum1 v/hSupportDen v ∧
    hSupportIntercept2 (hActivity v) = hInterceptNum2 v/hSupportDen v ∧
    hSupportIntercept4 (hActivity v) = hInterceptNum4 v/hSupportDen v := by
  unfold hSupportIntercept0 hSupportIntercept1 hSupportIntercept2 hSupportIntercept4
  rw [h_support_weight_coordinate v hq hH]
  unfold hInterceptNum0 hInterceptNum1 hInterceptNum2 hInterceptNum4
  repeat' constructor
  all_goals field_simp

theorem h_upper_vertex_coordinate (v : ℝ) (i : Fin 5) (hq : 1-v ≠ 0) (hH : hSupportDen v ≠ 0) :
    hUpperSupportVertex (hActivity v) i = hVertexNum v i/hSupportDen v := by
  obtain ⟨h0, h1, h2, h4⟩ := h_intercepts_coordinate v hq hH
  fin_cases i
  · simp only [hUpperSupportVertex, hVertexNum, h0]
    field_simp
    <;> ring
  · simp only [hUpperSupportVertex, hVertexNum, h0, h1]
    field_simp
    <;> ring
  · simp only [hUpperSupportVertex, hVertexNum, h1, h2]
    field_simp
    <;> ring
  · simp only [hUpperSupportVertex, hVertexNum, h2, h4]
    field_simp
    <;> ring
  · simp only [hUpperSupportVertex, hVertexNum, div_self hH]

theorem h_upper_height_coordinate (v : ℝ) (i : Fin 5) (hq : 1-v ≠ 0) (hH : hSupportDen v ≠ 0) :
    hUpperSupportHeight (hActivity v) i = hHeightNum v i/hSupportDen v := by
  obtain ⟨h0, h1, h2, h4⟩ := h_intercepts_coordinate v hq hH
  fin_cases i
  · simp only [hUpperSupportHeight, hHeightNum, zero_div]
  · simp only [hUpperSupportHeight, hHeightNum, h_upper_vertex_coordinate v 1 hq hH, h0]
    field_simp
  · simp only [hUpperSupportHeight, hHeightNum, h_upper_vertex_coordinate v 2 hq hH, h1]
    field_simp
  · simp only [hUpperSupportHeight, hHeightNum, h_upper_vertex_coordinate v 3 hq hH, h2]
    field_simp
  · simp only [hUpperSupportHeight, hHeightNum, h4]
    field_simp

theorem h_lower_zero_vertex_coordinate (v : ℝ) (hq : 1-v ≠ 0) (hH : hSupportDen v ≠ 0) :
    hSupportVertex (hActivity v) 0 = hVertexNum v 0/hSupportDen v := by
  exact h_upper_vertex_coordinate v 0 hq hH

end F4Heavy.Analysis
