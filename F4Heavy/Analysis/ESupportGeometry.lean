module

public import F4Heavy.Analysis.ESupportData

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem e_support_vertex_order (r : Row) (lam : ℝ) (he : r = .E1 ∨ r = .E2)
    (hr : InRow r lam) :
    0 < eSupportVertex r lam 0 ∧
    eSupportVertex r lam 0 < eSupportVertex r lam 1 ∧
    eSupportVertex r lam 1 < eSupportVertex r lam 2 ∧
    eSupportVertex r lam 2 < eSupportVertex r lam 3 := by
  rcases he with rfl | rfl
  all_goals
    norm_num [eSupportVertex, eSupportIntercept0, eSupportIntercept1, eSupportIntercept2,
      InRow, rowData] at *
    rcases hr with ⟨hl, hu⟩
    repeat' constructor
    all_goals linarith only [hl, hu]

theorem e_support_height_positive (r : Row) (lam : ℝ) (he : r = .E1 ∨ r = .E2)
    (hr : InRow r lam) :
    0 < eSupportHeight r lam 1 ∧ 0 < eSupportHeight r lam 2 ∧
      0 < eSupportHeight r lam 3 := by
  rcases he with rfl | rfl
  all_goals
    norm_num [eSupportHeight, eSupportVertex, eSupportIntercept0, eSupportIntercept1,
      eSupportIntercept2, InRow, rowData] at *
    rcases hr with ⟨hl, hu⟩
    repeat' constructor
    all_goals linarith only [hl, hu]

theorem e_support_first_segment (r : Row) (lam t : ℝ) :
    (1-t)*eSupportHeight r lam 0+t*eSupportHeight r lam 1 =
      (7/3)*((1-t)*eSupportVertex r lam 0+t*eSupportVertex r lam 1)+
        eSupportIntercept0 r lam := by
  simp only [eSupportHeight, eSupportVertex]
  ring

theorem e_support_second_segment (r : Row) (lam t : ℝ) :
    (1-t)*eSupportHeight r lam 1+t*eSupportHeight r lam 2 =
      (3/10)*((1-t)*eSupportVertex r lam 1+t*eSupportVertex r lam 2)+
        eSupportIntercept1 r lam := by
  simp only [eSupportHeight, eSupportVertex]
  ring

theorem e_support_third_segment (r : Row) (lam t : ℝ) :
    (1-t)*eSupportHeight r lam 2+t*eSupportHeight r lam 3 =
      (-8/15)*((1-t)*eSupportVertex r lam 2+t*eSupportVertex r lam 3)+
        eSupportIntercept2 r lam := by
  simp only [eSupportHeight, eSupportVertex]
  ring

theorem e_support_last_height_decreases (r : Row) (lam : ℝ)
    (he : r = .E1 ∨ r = .E2) (hr : InRow r lam) :
    eSupportHeight r lam 3 ≤ eSupportHeight r lam 2 := by
  have hh := (e_support_vertex_order r lam he hr).2.2.2
  have h0 := e_support_third_segment r lam 0
  have h1 := e_support_third_segment r lam 1
  norm_num only [sub_zero, one_mul, zero_mul, add_zero, sub_self, zero_add] at h0 h1
  linarith only [hh, h0, h1]

end F4Heavy.Analysis
