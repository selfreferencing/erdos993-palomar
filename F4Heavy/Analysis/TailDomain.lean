module

public import F4Heavy.Analysis.TailDefinitions

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem tail_scale_positive (r : Row) : 0 < tailScale r := by
  cases r <;> norm_num [tailScale]

theorem tail_scale_xMin (r : Row) : tailScale r * (rowData r).xMin = 1 := by
  cases r <;> norm_num [tailScale, rowData]

theorem tail_xMin_le_one (r : Row) : (rowData r).xMin ≤ 1 := by
  cases r <;> norm_num [rowData]

theorem tail_mass_lower (r : Row) (lam Y : ℝ) (hl : 0 < lam)
    (hx : parentX lam Y ≤ (rowData r).xMin) : tailTau r lam ≤ Y := by
  have hs := tail_scale_positive r
  have hmul := mul_le_mul_of_nonneg_left hx hs.le
  rw [tail_scale_xMin] at hmul
  change tailScale r * ((1 + lam) * Real.exp (-Y)) ≤ 1 at hmul
  have harg : tailScale r * (1 + lam) ≤ Real.exp Y := by
    have h := mul_le_mul_of_nonneg_right hmul (Real.exp_pos Y).le
    rw [mul_assoc, mul_assoc, ← Real.exp_add] at h
    simpa using h
  have hlog := Real.log_le_log (mul_pos hs (by linarith only [hl])) harg
  simpa only [tailTau, Real.log_exp] using hlog

theorem tail_probability_at_threshold (r : Row) (lam : ℝ) (hl : 0 < lam) :
    p lam (tailTau r lam) = tailPStar r lam := by
  have hs := tail_scale_positive r
  have hd : 0 < tailScale r * (1 + lam) := by positivity
  have hid : Real.exp (-tailTau r lam) = 1 / (tailScale r * (1 + lam)) := by
    rw [tailTau, Real.exp_neg, Real.exp_log hd]
    simp only [one_div]
  unfold p tailPStar
  rw [hid]
  field_simp
  <;> ring

theorem tail_probability_upper (r : Row) (lam Y : ℝ) (hl : 0 < lam)
    (hx : parentX lam Y ≤ (rowData r).xMin) : p lam Y ≤ tailPStar r lam := by
  have hs := tail_scale_positive r
  have ht := tail_mass_lower r lam Y hl hx
  have he := Real.exp_le_exp.mpr (neg_le_neg ht)
  have hb : p lam Y ≤ p lam (tailTau r lam) := by
    unfold p
    apply (div_le_div_iff₀ (by positivity : 0 < 1 + lam * Real.exp (-Y))
      (by positivity : 0 < 1 + lam * Real.exp (-tailTau r lam))).mpr
    nlinarith only [mul_le_mul_of_nonneg_left he hl.le]
  simpa only [tail_probability_at_threshold r lam hl] using hb

theorem tail_parent_probability_derivative (lam Y : ℝ) (hl : 0 < lam) :
    HasDerivAt (p lam) (-p lam Y * (1 - p lam Y)) Y := by
  have he := (hasDerivAt_id Y).neg.exp.const_mul lam
  have hd : 1 + lam * Real.exp (-Y) ≠ 0 := by positivity
  have h := he.div (he.const_add 1) hd
  convert h using 1
  · rfl
  · dsimp
    unfold p
    field_simp
    <;> ring

theorem tailS_positive (r : Row) (lam : ℝ) (hl : 0 < lam) : 0 < tailS r lam := by
  have hq := q_pos lam hl
  have hp := row_price_pos r
  unfold tailS
  positivity

end F4Heavy.Analysis
