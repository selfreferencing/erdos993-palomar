module

public import F4Heavy.Analysis.ESupportGeometry
public import F4Heavy.Analysis.ResponseChord

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem e_support_response_gains (r : Row) (lam a b c d delta : ℝ)
    (he : r = .E1 ∨ r = .E2) (hr : InRow r lam)
    (hdelta : 0 < delta) (hb : 0 ≤ b) (hd : d ≤ 0)
    (hW0 : 0 < responseNumerator a b c d delta (eSupportHeight r lam 0) (eSupportVertex r lam 0))
    (hW1 : 0 < responseNumerator a b c d delta (eSupportHeight r lam 1) (eSupportVertex r lam 1))
    (hW2 : 0 < responseNumerator a b c d delta (eSupportHeight r lam 2) (eSupportVertex r lam 2)) :
    0 < delta+d*eSupportHeight r lam 0 ∧
    0 < delta+d*eSupportHeight r lam 1 ∧
    0 < delta+d*eSupportHeight r lam 2 ∧
    0 < delta+d*eSupportHeight r lam 3 := by
  have hL := e_support_height_positive r lam he hr
  have hf0 := e_support_first_segment r lam 0
  have hf1 := e_support_first_segment r lam 1
  have hs0 := e_support_second_segment r lam 0
  have hs1 := e_support_second_segment r lam 1
  simp only [sub_zero, one_mul, zero_mul, add_zero, sub_self, zero_add] at hf0 hf1 hs0 hs1
  have hG0 : 0 < delta+d*eSupportHeight r lam 0 := by
    simpa only [eSupportHeight, mul_zero, add_zero] using hdelta
  have hG1 : 0 < delta+d*eSupportHeight r lam 1 := by
    rw [hf1]
    apply response_segment_denominator_positive a b c d delta (7/3) (eSupportIntercept0 r lam)
      (eSupportVertex r lam 0) (eSupportVertex r lam 1)
    · rw [← hf0]
      exact le_refl 0
    · rw [← hf1]
      exact hL.1.le
    · rw [← hf0]
      exact hG0
    · intro t ht0 ht1
      apply response_numerator_segment_positive a b c d delta (7/3) (eSupportIntercept0 r lam)
        (eSupportVertex r lam 0) (eSupportVertex r lam 1) t hd (by positivity) ht0 ht1
      · rw [← hf0]
        exact hW0
      · rw [← hf1]
        exact hW1
  have hG2 : 0 < delta+d*eSupportHeight r lam 2 := by
    rw [hs1]
    apply response_segment_denominator_positive a b c d delta (3/10) (eSupportIntercept1 r lam)
      (eSupportVertex r lam 1) (eSupportVertex r lam 2)
    · rw [← hs0]
      exact hL.1.le
    · rw [← hs1]
      exact hL.2.1.le
    · rw [← hs0]
      exact hG1
    · intro t ht0 ht1
      apply response_numerator_segment_positive a b c d delta (3/10) (eSupportIntercept1 r lam)
        (eSupportVertex r lam 1) (eSupportVertex r lam 2) t hd (by positivity) ht0 ht1
      · rw [← hs0]
        exact hW1
      · rw [← hs1]
        exact hW2
  refine ⟨hG0, hG1, hG2, ?_⟩
  have hinc := mul_nonneg_of_nonpos_of_nonpos hd
    (sub_nonpos.mpr (e_support_last_height_decreases r lam he hr))
  nlinarith only [hG2, hinc]

end F4Heavy.Analysis
