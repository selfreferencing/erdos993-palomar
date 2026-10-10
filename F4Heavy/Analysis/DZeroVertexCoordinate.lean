module

public import F4Heavy.Analysis.DUpperLogCoordinate
public import F4Heavy.Analysis.DHSupportGeometry

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

noncomputable def dSupportDen (v : ℝ) : ℝ := 3*485507815781*(1-v^2)
noncomputable def dSupportNum (v : ℝ) : ℝ := 1000000000000*(6*v-4*v^3)
noncomputable def dZeroVertexNum (v : ℝ) : ℝ :=
  -((-3326942783/2000000000)*dSupportDen v+
    ((-23862523/16000000)-(-3326942783/2000000000))*dSupportNum v)/(11/5)

theorem d_activity_transform_forward (v : ℝ) (hq : 1-v ≠ 0) :
    (dActivity v-(4/5 : ℝ))/(dActivity v+(4/5 : ℝ)) = v := by
  have he : dActivity v+(4/5 : ℝ) = (8/5)/(1-v) := by
    unfold dActivity
    field_simp
    <;> ring
  rw [he]
  unfold dActivity
  field_simp
  <;> ring

theorem d_support_den_positive (v : ℝ) (hv : 0 ≤ v ∧ v ≤ (5/21 : ℝ)) :
    0 < dSupportDen v := by
  have hh : 0 < 1-v^2 := by nlinarith only [hv.1, hv.2, sq_nonneg (1-v)]
  unfold dSupportDen
  positivity

theorem d_support_weight_coordinate (v : ℝ) (hq : 1-v ≠ 0) (hH : dSupportDen v ≠ 0) :
    dSupportWeight (dActivity v) = dSupportNum v/dSupportDen v := by
  unfold dSupportWeight
  rw [d_activity_transform_forward v hq]
  unfold dSupportNum dSupportDen
  have hh : 1-v^2 ≠ 0 := by
    intro hh
    apply hH
    simp only [dSupportDen, hh, mul_zero]
  field_simp
  <;> ring


theorem d_zero_vertex_coordinate (v : ℝ) (hq : 1-v ≠ 0) (hH : dSupportDen v ≠ 0) :
    dSupportVertex (dActivity v) 0 = dZeroVertexNum v/dSupportDen v := by
  norm_num only [dSupportVertex, dSupportIntercept0]
  rw [d_support_weight_coordinate v hq hH]
  unfold dZeroVertexNum
  field_simp
  <;> ring

end F4Heavy.Analysis
