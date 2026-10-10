module

public import F4Heavy.Analysis.ChildWeight

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem activity_transform_inverse (a lam : ℝ) (ha : 0 < a) (hl : 0 < lam) :
    a*(1+(lam-a)/(lam+a))/(1-(lam-a)/(lam+a)) = lam := by
  have hd : 0 < lam+a := by positivity
  have ht : (lam-a)/(lam+a) < 1 := (div_lt_one hd).mpr (by linarith only [ha])
  field_simp [ne_of_gt ha, ne_of_gt hd]
  <;> ring

theorem d_activity_coordinates (lam : ℝ) (hr : InRow .D lam) :
    0 ≤ (lam-(4/5 : ℝ))/(lam+(4/5 : ℝ)) ∧
      (lam-(4/5 : ℝ))/(lam+(4/5 : ℝ)) ≤ (5/21 : ℝ) := by
  have h := activity_transform_bounds (4/5 : ℝ) (13/10 : ℝ) lam
    (by norm_num) (by norm_num) hr.1 hr.2
  norm_num at h
  exact ⟨h.1, h.2⟩

theorem h_activity_coordinates (lam : ℝ) (hr : InRow .H lam) :
    0 ≤ (lam-(7/4 : ℝ))/(lam+(7/4 : ℝ)) ∧
      (lam-(7/4 : ℝ))/(lam+(7/4 : ℝ)) ≤ (1/7 : ℝ) := by
  have h := activity_transform_bounds (7/4 : ℝ) (7/3 : ℝ) lam
    (by norm_num) (by norm_num) hr.1 hr.2
  norm_num at h
  exact ⟨h.1, h.2⟩

end F4Heavy.Analysis
