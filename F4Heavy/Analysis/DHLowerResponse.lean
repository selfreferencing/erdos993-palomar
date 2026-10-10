module

public import F4Heavy.Analysis.DHSupportGeometry
public import F4Heavy.Analysis.LowerResponseClosed

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem d_lower_response_of_guards (lam a b c d delta u y : ℝ)
    (hr : InRow .D lam) (hu0 : 0 ≤ u) (huq : u ≤ q lam) (hadm : Admissible lam u y)
    (hdelta : 0 < delta) (hb : 0 ≤ b) (hc : 0 < c+2*d) (hC : 0 < 4*delta-(11/5)*c)
    (hB : 0 < a+(b+c)*dSupportVertex lam 0+d*(dSupportVertex lam 0)^2)
    (hF : 0 ≤ 4*delta*(b+c+2*d*dSupportVertex lam 0)-(11/5)*(c+2*d*dSupportVertex lam 0)^2) :
    0 < responsePolynomial a b c d delta (childJ lam u) (childH u) y := by
  have hJ : 0 ≤ childJ lam u := by
    rcases hadm with hJ | ⟨hJ, _⟩
    · exact hJ.le
    · exact le_of_eq hJ.symm
  have hl := d_child_support_line_0 lam u hr hu0 huq
  have hh := d_support_lower_vertex lam (childH u) (childJ lam u) hJ hl
  have hh0 : (1/2 : ℝ) ≤ dSupportVertex lam 0 := by
    have hw := d_support_weight_bounds lam hr
    norm_num [dSupportVertex, dSupportIntercept0]
    linarith only [hw.1, hw.2]
  have hLs : childJ lam u ≤ (11/5)*(childH u-dSupportVertex lam 0) := by
    change childJ lam u ≤ (11/5)*(childH u-(-dSupportIntercept0 lam/(11/5)))
    linarith only [hl]
  have hy : childJ lam u = 0 → y = childH u := by
    intro hz
    rcases hadm with hj | ⟨_, hy⟩
    · linarith only [hz, hj]
    · exact hy
  exact lower_response_closed_positive a b c d delta (11/5) (dSupportVertex lam 0)
    (childH u) (childJ lam u) y hdelta (by norm_num) hb hh0 hh
    (childH_upper_one u hu0 (huq.trans_lt (q_lt_one lam (inRow_activity_pos .D lam hr))))
    hJ hLs hy hc hC hB hF

theorem h_lower_response_of_guards (lam a b c d delta u y : ℝ)
    (hr : InRow .H lam) (hu0 : 0 ≤ u) (huq : u ≤ q lam) (hadm : Admissible lam u y)
    (hdelta : 0 < delta) (hb : 0 ≤ b) (hc : 0 < c+2*d) (hC : 0 < 4*delta-(12/5)*c)
    (hB : 0 < a+(b+c)*hSupportVertex lam 0+d*(hSupportVertex lam 0)^2)
    (hF : 0 ≤ 4*delta*(b+c+2*d*hSupportVertex lam 0)-(12/5)*(c+2*d*hSupportVertex lam 0)^2) :
    0 < responsePolynomial a b c d delta (childJ lam u) (childH u) y := by
  have hJ : 0 ≤ childJ lam u := by
    rcases hadm with hJ | ⟨hJ, _⟩
    · exact hJ.le
    · exact le_of_eq hJ.symm
  have hl := h_child_support_line_0 lam u hr hu0 huq
  have hh := h_support_lower_vertex lam (childH u) (childJ lam u) hJ hl
  have hh0 : (1/2 : ℝ) ≤ hSupportVertex lam 0 := by
    have hw := h_support_weight_bounds lam hr
    norm_num [hSupportVertex, hSupportIntercept0]
    linarith only [hw.1, hw.2]
  have hLs : childJ lam u ≤ (12/5)*(childH u-hSupportVertex lam 0) := by
    change childJ lam u ≤ (12/5)*(childH u-(-hSupportIntercept0 lam/(12/5)))
    linarith only [hl]
  have hy : childJ lam u = 0 → y = childH u := by
    intro hz
    rcases hadm with hj | ⟨_, hy⟩
    · linarith only [hz, hj]
    · exact hy
  exact lower_response_closed_positive a b c d delta (12/5) (hSupportVertex lam 0)
    (childH u) (childJ lam u) y hdelta (by norm_num) hb hh0 hh
    (childH_upper_one u hu0 (huq.trans_lt (q_lt_one lam (inRow_activity_pos .H lam hr))))
    hJ hLs hy hc hC hB hF

end F4Heavy.Analysis
