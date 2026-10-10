module

public import F4Heavy.Analysis.SupportSegment

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis

-- Round 9 manuscript, response-upper-chord. No division or slope restriction.
theorem response_cleared_chord (a b c d delta L0 L1 h0 h1 t : ℝ) :
    (delta + d * L0) * (delta + d * L1) *
      responseNumerator a b c d delta ((1 - t) * L0 + t * L1)
        ((1 - t) * h0 + t * h1) =
    (delta + d * ((1 - t) * L0 + t * L1)) *
      ((1 - t) * (delta + d * L1) * responseNumerator a b c d delta L0 h0 +
        t * (delta + d * L0) * responseNumerator a b c d delta L1 h1) -
      delta * d * t * (1 - t) *
        (2 * delta * (h1 - h0) - c * (L1 - L0) +
          2 * d * (h1 * L0 - h0 * L1)) ^ 2 := by
  unfold responseNumerator
  ring

theorem response_gain_chord (d delta L0 L1 t : ℝ) :
    delta + d * ((1 - t) * L0 + t * L1) =
      (1 - t) * (delta + d * L0) + t * (delta + d * L1) := by
  ring

theorem response_cleared_chord_positive (a b c d delta L0 L1 h0 h1 t : ℝ)
    (hdelta : 0 ≤ delta) (hd : d ≤ 0) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hG0 : 0 < delta + d * L0) (hG1 : 0 < delta + d * L1)
    (hW0 : 0 < responseNumerator a b c d delta L0 h0)
    (hW1 : 0 < responseNumerator a b c d delta L1 h1) :
    0 < responseNumerator a b c d delta ((1 - t) * L0 + t * L1)
      ((1 - t) * h0 + t * h1) := by
  have hGt : 0 < delta + d * ((1 - t) * L0 + t * L1) := by
    rw [response_gain_chord]
    exact positive_chord _ _ t hG0 hG1 ht0 ht1
  have hweighted := positive_chord _ _ t (mul_pos hG1 hW0)
    (mul_pos hG0 hW1) ht0 ht1
  have hmain : 0 < (delta + d * ((1 - t) * L0 + t * L1)) *
      ((1 - t) * (delta + d * L1) * responseNumerator a b c d delta L0 h0 +
        t * (delta + d * L0) * responseNumerator a b c d delta L1 h1) := by
    simpa only [mul_assoc] using mul_pos hGt hweighted
  have hcorrection : delta * d * t * (1 - t) *
      (2 * delta * (h1 - h0) - c * (L1 - L0) +
        2 * d * (h1 * L0 - h0 * L1)) ^ 2 ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hdelta hd) ht0)
        (sub_nonneg.mpr ht1)) (sq_nonneg _)
  have hproduct : 0 < (delta + d * L0) * (delta + d * L1) *
      responseNumerator a b c d delta ((1 - t) * L0 + t * L1)
        ((1 - t) * h0 + t * h1) := by
    rw [response_cleared_chord]
    linarith only [hmain, hcorrection]
  exact (mul_pos_iff_of_pos_left (mul_pos hG0 hG1)).mp hproduct

theorem response_chord_payment_positive (a b c d delta L0 L1 h0 h1 t y : ℝ)
    (hdelta : 0 ≤ delta) (hd : d ≤ 0) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hG0 : 0 < delta + d * L0) (hG1 : 0 < delta + d * L1)
    (hW0 : 0 < responseNumerator a b c d delta L0 h0)
    (hW1 : 0 < responseNumerator a b c d delta L1 h1)
    (hL : 0 < (1 - t) * L0 + t * L1) :
    0 < responsePolynomial a b c d delta ((1 - t) * L0 + t * L1)
      ((1 - t) * h0 + t * h1) y := by
  apply response_positive _ _ _ _ _ _ _ _ hL
  · rw [response_gain_chord]
    exact positive_chord _ _ t hG0 hG1 ht0 ht1
  · exact response_cleared_chord_positive a b c d delta L0 L1 h0 h1 t
      hdelta hd ht0 ht1 hG0 hG1 hW0 hW1

theorem response_zero_vertex_positive (a b c d delta h : ℝ)
    (hdelta : 0 < delta) (hW : 0 < responseNumerator a b c d delta 0 h) :
    0 < responsePolynomial a b c d delta 0 h h := by
  rw [response_zero_envelope]
  have heq : responseNumerator a b c d delta 0 h =
      (4 * delta) * (a + (b + c) * h + d * h ^ 2) := by
    unfold responseNumerator
    ring
  rw [heq] at hW
  exact (mul_pos_iff_of_pos_left (by positivity : 0 < 4 * delta)).mp hW

end F4Heavy.Analysis
