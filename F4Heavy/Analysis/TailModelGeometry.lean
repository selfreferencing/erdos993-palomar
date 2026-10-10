module

public import F4Heavy.Analysis.ResponseChord

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis

theorem tail_response_envelope_order (a b c d K J L h y : ℝ)
    (hK : 0 ≤ K) (hJ : 0 < J) (hJL : J ≤ L) :
    responsePolynomial a b c d K L h y ≤ responsePolynomial a b c d K J h y := by
  have h := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hK hJ hJL) (sq_nonneg (h - y))
  unfold responsePolynomial
  linarith only [h]

theorem tail_response_positive_curvature (a b c d K C h0 h J y : ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (hK : 0 < K)
    (hh0 : 0 ≤ h0) (hhh : h0 ≤ h) (hJ : 0 < J) (hJC : J ≤ C)
    (hW : 0 < responseNumerator a b c d K C h0) :
    0 < responsePolynomial a b c d K J h y := by
  have hC := hJ.trans_le hJC
  have hG : 0 < K + d * C := add_pos_of_pos_of_nonneg hK (mul_nonneg hd hC.le)
  have hsq : h0 ^ 2 ≤ h ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hhh) (add_nonneg hh0 (hh0.trans hhh))]
  have hm1 := mul_nonneg (mul_nonneg hG.le hb) (sub_nonneg.mpr hhh)
  have hm2 := mul_nonneg (mul_nonneg hK.le hc) (sub_nonneg.mpr hhh)
  have hm3 := mul_nonneg (mul_nonneg hK.le hd) (sub_nonneg.mpr hsq)
  have hWh : 0 < responseNumerator a b c d K C h := by
    unfold responseNumerator at hW ⊢
    nlinarith only [hW, hm1, hm2, hm3]
  exact (response_positive a b c d K C h y hC hG hWh).trans_le
    (tail_response_envelope_order a b c d K J C h y hK.le hJ hJC)

theorem tail_chord_parameter (a b x : ℝ) (hab : a < b) (ha : a ≤ x) (hb : x ≤ b) :
    0 ≤ (x - a) / (b - a) ∧ (x - a) / (b - a) ≤ 1 ∧
      (1 - (x - a) / (b - a)) * a + (x - a) / (b - a) * b = x := by
  have hd := sub_pos.mpr hab
  refine ⟨div_nonneg (sub_nonneg.mpr ha) hd.le, (div_le_one hd).mpr (by linarith only [hb]), ?_⟩
  field_simp
  <;> ring

theorem tail_response_chord_interval (a b c d K L0 L1 h0 h1 h y : ℝ)
    (hK : 0 ≤ K) (hd : d ≤ 0) (h01 : h0 < h1) (hh0 : h0 ≤ h) (hh1 : h ≤ h1)
    (hL0 : 0 < L0) (hL1 : 0 < L1)
    (hG0 : 0 < K + d * L0) (hG1 : 0 < K + d * L1)
    (hW0 : 0 < responseNumerator a b c d K L0 h0)
    (hW1 : 0 < responseNumerator a b c d K L1 h1) :
    0 < responsePolynomial a b c d K
      ((1 - (h - h0) / (h1 - h0)) * L0 + (h - h0) / (h1 - h0) * L1) h y := by
  have ht := tail_chord_parameter h0 h1 h h01 hh0 hh1
  have hq := response_chord_payment_positive a b c d K L0 L1 h0 h1 ((h - h0) / (h1 - h0)) y
    hK hd ht.1 ht.2.1 hG0 hG1 hW0 hW1 (positive_chord L0 L1 _ hL0 hL1 ht.1 ht.2.1)
  rwa [ht.2.2] at hq

end F4Heavy.Analysis
