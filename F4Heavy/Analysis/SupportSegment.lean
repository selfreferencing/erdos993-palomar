module

public import F4Heavy.Analysis.Quadratic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis

theorem response_numerator_chord (a b c d delta s k ha hb t : ℝ) :
    responseNumerator a b c d delta (s * ((1 - t) * ha + t * hb) + k)
      ((1 - t) * ha + t * hb) =
    (1 - t) * responseNumerator a b c d delta (s * ha + k) ha +
      t * responseNumerator a b c d delta (s * hb + k) hb -
      4 * d * (delta + s * b) * t * (1 - t) * (hb - ha) ^ 2 := by
  unfold responseNumerator
  ring

theorem positive_chord (wa wb t : ℝ) (ha : 0 < wa) (hb : 0 < wb)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 0 < (1 - t) * wa + t * wb := by
  by_cases ht : t = 0
  · simp [ht, ha]
  · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr ht1) ha.le)
      (mul_pos (lt_of_le_of_ne ht0 (Ne.symm ht)) hb)

theorem response_numerator_segment_positive (a b c d delta s k ha hb t : ℝ)
    (hd : d ≤ 0) (hs : 0 ≤ delta + s * b) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hWa : 0 < responseNumerator a b c d delta (s * ha + k) ha)
    (hWb : 0 < responseNumerator a b c d delta (s * hb + k) hb) :
    0 < responseNumerator a b c d delta (s * ((1 - t) * ha + t * hb) + k)
      ((1 - t) * ha + t * hb) := by
  rw [response_numerator_chord]
  have hc := positive_chord _ _ t hWa hWb ht0 ht1
  have hn : 4 * d * (delta + s * b) * t * (1 - t) * (hb - ha) ^ 2 ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg (by linarith) hs) ht0)
        (sub_nonneg.mpr ht1)) (sq_nonneg _)
  linarith

theorem affine_positive_of_nonzero (ga gb : ℝ) (ha : 0 < ga)
    (hn : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (1 - t) * ga + t * gb ≠ 0) : 0 < gb := by
  by_contra hb
  have hgb : gb ≤ 0 := le_of_not_gt hb
  have hd : 0 < ga - gb := by linarith
  have ht0 : 0 ≤ ga / (ga - gb) := (div_pos ha hd).le
  have ht1 : ga / (ga - gb) ≤ 1 := (div_le_one hd).2 (by linarith)
  apply hn _ ht0 ht1
  field_simp
  <;> ring

theorem response_segment_denominator_positive (a b c d delta s k ha hb : ℝ)
    (hLa : 0 ≤ s * ha + k) (hLb : 0 ≤ s * hb + k)
    (hGa : 0 < delta + d * (s * ha + k))
    (hW : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      0 < responseNumerator a b c d delta (s * ((1 - t) * ha + t * hb) + k)
        ((1 - t) * ha + t * hb)) : 0 < delta + d * (s * hb + k) := by
  apply affine_positive_of_nonzero _ _ hGa
  intro t ht0 ht1
  have hL : 0 ≤ s * ((1 - t) * ha + t * hb) + k := by
    have hleft := mul_nonneg (sub_nonneg.mpr ht1) hLa
    have hright := mul_nonneg ht0 hLb
    nlinarith only [hleft, hright]
  have hn := response_denominator_ne_zero a b c d delta _ _ hL (hW t ht0 ht1)
  convert hn using 1 <;> ring

end F4Heavy.Analysis
