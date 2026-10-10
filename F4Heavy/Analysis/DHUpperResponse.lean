module

public import F4Heavy.Analysis.DHSupportGeometry
public import F4Heavy.Analysis.ResponseChord
public import Mathlib.Tactic.IntervalCases

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem d_response_gains (lam a b c d delta : ℝ) (hr : InRow .D lam)
    (hdelta : 0 < delta) (hb : 0 ≤ b) (hd : d ≤ 0)
    (hW : ∀ i : Fin 4, 0 < responseNumerator a b c d delta (dSupportHeight lam i) (dSupportVertex lam i)) :
    ∀ i : Fin 4, 0 < delta+d*dSupportHeight lam i := by
  have hL := d_support_height_positive lam hr
  have hG0 : 0 < delta+d*dSupportHeight lam 0 := by
    simpa only [dSupportHeight, mul_zero, add_zero] using hdelta
  have hs0a := d_support_segment_0 lam 0
  have hs0b := d_support_segment_0 lam 1
  simp only [sub_zero, one_mul, zero_mul, add_zero, sub_self, zero_add] at hs0a hs0b
  have hG1 : 0 < delta+d*dSupportHeight lam 1 := by
    rw [hs0b]
    apply response_segment_denominator_positive a b c d delta (11/5 : ℝ) (dSupportIntercept0 lam)
      (dSupportVertex lam 0) (dSupportVertex lam 1)
    · rw [← hs0a]
      exact le_refl 0
    · rw [← hs0b]
      exact hL.1.le
    · rw [← hs0a]
      exact hG0
    · intro t ht0 ht1
      apply response_numerator_segment_positive a b c d delta (11/5 : ℝ) (dSupportIntercept0 lam)
        (dSupportVertex lam 0) (dSupportVertex lam 1) t hd (by positivity) ht0 ht1
      · rw [← hs0a]
        exact hW 0
      · rw [← hs0b]
        exact hW 1
  have hs1a := d_support_segment_1 lam 0
  have hs1b := d_support_segment_1 lam 1
  simp only [sub_zero, one_mul, zero_mul, add_zero, sub_self, zero_add] at hs1a hs1b
  have hG2 : 0 < delta+d*dSupportHeight lam 2 := by
    rw [hs1b]
    apply response_segment_denominator_positive a b c d delta (3/10 : ℝ) (dSupportIntercept1 lam)
      (dSupportVertex lam 1) (dSupportVertex lam 2)
    · rw [← hs1a]
      exact hL.1.le
    · rw [← hs1b]
      exact hL.2.1.le
    · rw [← hs1a]
      exact hG1
    · intro t ht0 ht1
      apply response_numerator_segment_positive a b c d delta (3/10 : ℝ) (dSupportIntercept1 lam)
        (dSupportVertex lam 1) (dSupportVertex lam 2) t hd (by positivity) ht0 ht1
      · rw [← hs1a]
        exact hW 1
      · rw [← hs1b]
        exact hW 2
  intro i
  rcases i with ⟨i, hi⟩
  interval_cases i
  · exact hG0
  · exact hG1
  · exact hG2
  · have hh : dSupportHeight lam 3 ≤ dSupportHeight lam 2 := by
      have hw := d_support_weight_bounds lam hr
      norm_num [dSupportHeight, dSupportVertex, dSupportIntercept0, dSupportIntercept1, dSupportIntercept2]
      linarith only [hw.1, hw.2]
    have hinc := mul_nonneg_of_nonpos_of_nonpos hd (sub_nonpos.mpr hh)
    change 0 < delta+d*dSupportHeight lam 3
    nlinarith only [hG2, hinc]

theorem d_upper_response_of_vertices (lam a b c d delta u y : ℝ)
    (hr : InRow .D lam) (hu0 : 0 ≤ u) (huq : u ≤ q lam)
    (hadm : Admissible lam u y) (hdelta : 0 < delta) (hb : 0 ≤ b) (hd : d ≤ 0)
    (hW : ∀ i : Fin 4, 0 < responseNumerator a b c d delta (dSupportHeight lam i) (dSupportVertex lam i)) :
    ∃ L : ℝ, childJ lam u ≤ L ∧ 0 < responsePolynomial a b c d delta L (childH u) y := by
  have hJ : 0 ≤ childJ lam u := by
    rcases hadm with hJ | ⟨hJ, _⟩
    · exact hJ.le
    · exact le_of_eq hJ.symm
  have hl0 := d_child_support_line_0 lam u hr hu0 huq
  have hl1 := d_child_support_line_1 lam u hr hu0 huq
  have hl2 := d_child_support_line_2 lam u hr hu0 huq
  have hh0 := d_support_lower_vertex lam (childH u) (childJ lam u) hJ hl0
  have hq1 := q_lt_one lam (inRow_activity_pos .D lam hr)
  obtain ⟨i, j, t, ht0, ht1, hh, hJL⟩ := d_support_chord_coverage lam (childH u)
    (childJ lam u) hr hh0 (childH_upper_one u hu0 (huq.trans_lt hq1)) hl0 hl1 hl2
  have hG := d_response_gains lam a b c d delta hr hdelta hb hd hW
  let L := (1-t)*dSupportHeight lam i+t*dSupportHeight lam j
  have hL0 : 0 ≤ L := hJ.trans hJL
  have hWt := response_cleared_chord_positive a b c d delta (dSupportHeight lam i) (dSupportHeight lam j)
    (dSupportVertex lam i) (dSupportVertex lam j) t hdelta.le hd ht0 ht1 (hG i) (hG j) (hW i) (hW j)
  rw [← hh] at hWt
  refine ⟨L, hJL, ?_⟩
  by_cases hL : 0 < L
  · apply response_positive a b c d delta L (childH u) y hL
    · rw [response_gain_chord]
      exact positive_chord _ _ t (hG i) (hG j) ht0 ht1
    · exact hWt
  · have hzero : L = 0 := le_antisymm (le_of_not_gt hL) hL0
    have hy : y = childH u := by
      rcases hadm with hj | ⟨_, hy⟩
      · change childJ lam u ≤ L at hJL
        linarith only [hj, hJL, hzero]
      · exact hy
    change 0 < responseNumerator a b c d delta L (childH u) at hWt
    rw [hzero] at hWt
    rw [hzero, hy]
    exact response_zero_vertex_positive a b c d delta (childH u) hdelta hWt

theorem hUpper_response_gains (lam a b c d delta : ℝ) (hr : InRow .H lam)
    (hdelta : 0 < delta) (hb : 0 ≤ b) (hd : d ≤ 0)
    (hW : ∀ i : Fin 5, 0 < responseNumerator a b c d delta (hUpperSupportHeight lam i) (hUpperSupportVertex lam i)) :
    ∀ i : Fin 5, 0 < delta+d*hUpperSupportHeight lam i := by
  have hL := hUpper_support_height_positive lam hr
  have hG0 : 0 < delta+d*hUpperSupportHeight lam 0 := by
    simpa only [hUpperSupportHeight, mul_zero, add_zero] using hdelta
  have hs0a := hUpper_support_segment_0 lam 0
  have hs0b := hUpper_support_segment_0 lam 1
  simp only [sub_zero, one_mul, zero_mul, add_zero, sub_self, zero_add] at hs0a hs0b
  have hG1 : 0 < delta+d*hUpperSupportHeight lam 1 := by
    rw [hs0b]
    apply response_segment_denominator_positive a b c d delta (12/5 : ℝ) (hSupportIntercept0 lam)
      (hUpperSupportVertex lam 0) (hUpperSupportVertex lam 1)
    · rw [← hs0a]
      exact le_refl 0
    · rw [← hs0b]
      exact hL.1.le
    · rw [← hs0a]
      exact hG0
    · intro t ht0 ht1
      apply response_numerator_segment_positive a b c d delta (12/5 : ℝ) (hSupportIntercept0 lam)
        (hUpperSupportVertex lam 0) (hUpperSupportVertex lam 1) t hd (by positivity) ht0 ht1
      · rw [← hs0a]
        exact hW 0
      · rw [← hs0b]
        exact hW 1
  have hs1a := hUpper_support_segment_1 lam 0
  have hs1b := hUpper_support_segment_1 lam 1
  simp only [sub_zero, one_mul, zero_mul, add_zero, sub_self, zero_add] at hs1a hs1b
  have hG2 : 0 < delta+d*hUpperSupportHeight lam 2 := by
    rw [hs1b]
    apply response_segment_denominator_positive a b c d delta (3/10 : ℝ) (hSupportIntercept1 lam)
      (hUpperSupportVertex lam 1) (hUpperSupportVertex lam 2)
    · rw [← hs1a]
      exact hL.1.le
    · rw [← hs1b]
      exact hL.2.1.le
    · rw [← hs1a]
      exact hG1
    · intro t ht0 ht1
      apply response_numerator_segment_positive a b c d delta (3/10 : ℝ) (hSupportIntercept1 lam)
        (hUpperSupportVertex lam 1) (hUpperSupportVertex lam 2) t hd (by positivity) ht0 ht1
      · rw [← hs1a]
        exact hW 1
      · rw [← hs1b]
        exact hW 2
  intro i
  rcases i with ⟨i, hi⟩
  interval_cases i
  · exact hG0
  · exact hG1
  · exact hG2
  · have hh : hUpperSupportHeight lam 3 ≤ hUpperSupportHeight lam 2 := by
      have hw := h_support_weight_bounds lam hr
      norm_num [hUpperSupportHeight, hUpperSupportVertex, hSupportIntercept0, hSupportIntercept1, hSupportIntercept2, hSupportIntercept4]
      linarith only [hw.1, hw.2]
    have hinc := mul_nonneg_of_nonpos_of_nonpos hd (sub_nonpos.mpr hh)
    change 0 < delta+d*hUpperSupportHeight lam 3
    nlinarith only [hG2, hinc]
  · have hh : hUpperSupportHeight lam 4 ≤ hUpperSupportHeight lam 2 := by
      have hw := h_support_weight_bounds lam hr
      norm_num [hUpperSupportHeight, hUpperSupportVertex, hSupportIntercept0, hSupportIntercept1, hSupportIntercept2, hSupportIntercept4]
      linarith only [hw.1, hw.2]
    have hinc := mul_nonneg_of_nonpos_of_nonpos hd (sub_nonpos.mpr hh)
    change 0 < delta+d*hUpperSupportHeight lam 4
    nlinarith only [hG2, hinc]

theorem hUpper_upper_response_of_vertices (lam a b c d delta u y : ℝ)
    (hr : InRow .H lam) (hu0 : 0 ≤ u) (huq : u ≤ q lam)
    (hadm : Admissible lam u y) (hdelta : 0 < delta) (hb : 0 ≤ b) (hd : d ≤ 0)
    (hW : ∀ i : Fin 5, 0 < responseNumerator a b c d delta (hUpperSupportHeight lam i) (hUpperSupportVertex lam i)) :
    ∃ L : ℝ, childJ lam u ≤ L ∧ 0 < responsePolynomial a b c d delta L (childH u) y := by
  have hJ : 0 ≤ childJ lam u := by
    rcases hadm with hJ | ⟨hJ, _⟩
    · exact hJ.le
    · exact le_of_eq hJ.symm
  have hl0 := h_child_support_line_0 lam u hr hu0 huq
  have hl1 := h_child_support_line_1 lam u hr hu0 huq
  have hl2 := h_child_support_line_2 lam u hr hu0 huq
  have hl4 := h_child_support_line_4 lam u hr hu0 huq
  have hh0 := hUpper_support_lower_vertex lam (childH u) (childJ lam u) hJ hl0
  have hq1 := q_lt_one lam (inRow_activity_pos .H lam hr)
  obtain ⟨i, j, t, ht0, ht1, hh, hJL⟩ := hUpper_support_chord_coverage lam (childH u)
    (childJ lam u) hr hh0 (childH_upper_one u hu0 (huq.trans_lt hq1)) hl0 hl1 hl2 hl4
  have hG := hUpper_response_gains lam a b c d delta hr hdelta hb hd hW
  let L := (1-t)*hUpperSupportHeight lam i+t*hUpperSupportHeight lam j
  have hL0 : 0 ≤ L := hJ.trans hJL
  have hWt := response_cleared_chord_positive a b c d delta (hUpperSupportHeight lam i) (hUpperSupportHeight lam j)
    (hUpperSupportVertex lam i) (hUpperSupportVertex lam j) t hdelta.le hd ht0 ht1 (hG i) (hG j) (hW i) (hW j)
  rw [← hh] at hWt
  refine ⟨L, hJL, ?_⟩
  by_cases hL : 0 < L
  · apply response_positive a b c d delta L (childH u) y hL
    · rw [response_gain_chord]
      exact positive_chord _ _ t (hG i) (hG j) ht0 ht1
    · exact hWt
  · have hzero : L = 0 := le_antisymm (le_of_not_gt hL) hL0
    have hy : y = childH u := by
      rcases hadm with hj | ⟨_, hy⟩
      · change childJ lam u ≤ L at hJL
        linarith only [hj, hJL, hzero]
      · exact hy
    change 0 < responseNumerator a b c d delta L (childH u) at hWt
    rw [hzero] at hWt
    rw [hzero, hy]
    exact response_zero_vertex_positive a b c d delta (childH u) hdelta hWt

end F4Heavy.Analysis
