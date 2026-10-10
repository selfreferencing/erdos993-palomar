module

public import F4Heavy.Analysis.TailDefinitions

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis

noncomputable def tailLogRemainder (v : ℝ) : ℝ := Real.log (1 + v) - v + v ^ 2 / 2

theorem tail_log_remainder_derivative (v : ℝ) (hv : -1 < v) :
    HasDerivAt tailLogRemainder (v ^ 2 / (1 + v)) v := by
  have hi := hasDerivAt_id v
  have h := (((hi.const_add 1).log (by linarith : 1 + v ≠ 0)).sub hi).add ((hi.pow 2).div_const 2)
  convert h using 1
  · rfl
  · dsimp
    field_simp [show 1 + v ≠ 0 by linarith only [hv]]
    <;> ring

theorem tail_log_remainder_monotone : MonotoneOn tailLogRemainder (Set.Ioi (-1)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioi (-1 : ℝ))
  · intro v hv
    exact (tail_log_remainder_derivative v hv).continuousAt.continuousWithinAt
  · intro v hv
    have hv' : -1 < v := interior_subset hv
    exact (tail_log_remainder_derivative v hv').differentiableAt.differentiableWithinAt
  · intro v hv
    have hv' : -1 < v := interior_subset hv
    rw [(tail_log_remainder_derivative v hv').deriv]
    exact div_nonneg (sq_nonneg _) (by linarith only [hv'])

theorem tail_log_cubic_majorant_antitone (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    AntitoneOn (fun v => tailLogRemainder v - v ^ 3 / (3 * (1 - r))) (Set.Ici (-r)) := by
  have hd (v : ℝ) (hv : -r ≤ v) :
      HasDerivAt (fun x => tailLogRemainder x - x ^ 3 / (3 * (1 - r)))
        (v ^ 2 / (1 + v) - v ^ 2 / (1 - r)) v := by
    have h := (tail_log_remainder_derivative v (by linarith only [hv, hr1])).sub
      (((hasDerivAt_id v).pow 3).div_const (3 * (1 - r)))
    convert h using 1
    · rfl
    · dsimp
      field_simp
      <;> ring
  apply antitoneOn_of_deriv_nonpos (convex_Ici (-r))
  · intro v hv
    exact (hd v hv).continuousAt.continuousWithinAt
  · intro v hv
    have hv' : -r ≤ v := interior_subset hv
    exact (hd v hv').differentiableAt.differentiableWithinAt
  · intro v hv
    have hv' : -r ≤ v := interior_subset hv
    rw [(hd v hv').deriv]
    apply sub_nonpos.mpr
    exact div_le_div_of_nonneg_left (sq_nonneg _) (sub_pos.mpr hr1) (by linarith only [hv'])

theorem tail_log_quadratic_enclosure (r e v : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (he : r / (3 * (1 - r)) ≤ e) (hv : -r ≤ v ∧ v ≤ r) :
    v - (1 / 2 + e) * v ^ 2 ≤ Real.log (1 + v) ∧
      Real.log (1 + v) ≤ v - (1 / 2 - e) * v ^ 2 := by
  have hd : 0 < 3 * (1 - r) := by positivity
  have he0 : 0 ≤ e := (div_nonneg hr hd.le).trans he
  have heprod := (div_le_iff₀ hd).mp he
  have heq : tailLogRemainder 0 = 0 := by norm_num [tailLogRemainder]
  have hzero : (0 : ℝ) ∈ Set.Ici (-r) := by simpa using hr
  have hvi : v ∈ Set.Ici (-r) := hv.1
  have hv1 : -1 < v := by linarith only [hv.1, hr1]
  have hm := tail_log_cubic_majorant_antitone r hr hr1
  by_cases hv0 : 0 ≤ v
  · have hmaj := hm hzero hvi hv0
    dsimp only at hmaj
    rw [heq] at hmaj
    norm_num at hmaj
    have hpos := tail_log_remainder_monotone (show (0 : ℝ) ∈ Set.Ioi (-1) by norm_num) hv1 hv0
    rw [heq] at hpos
    have hcube : v ^ 3 / (3 * (1 - r)) ≤ e * v ^ 2 := by
      apply (div_le_iff₀ hd).mpr
      have h := mul_le_mul_of_nonneg_right (show v ≤ e * (3 * (1 - r)) from hv.2.trans heprod) (sq_nonneg v)
      nlinarith only [h]
    have hevv := mul_nonneg he0 (sq_nonneg v)
    unfold tailLogRemainder at hmaj hpos
    constructor <;> nlinarith only [hmaj, hpos, hcube, hevv]
  · have hvn := le_of_not_ge hv0
    have hmaj := hm hvi hzero hvn
    dsimp only at hmaj
    rw [heq] at hmaj
    norm_num at hmaj
    have hneg := tail_log_remainder_monotone hv1 (show (0 : ℝ) ∈ Set.Ioi (-1) by norm_num) hvn
    rw [heq] at hneg
    have hcube : -(e * v ^ 2) ≤ v ^ 3 / (3 * (1 - r)) := by
      apply (le_div_iff₀ hd).mpr
      have h := mul_le_mul_of_nonneg_right (show -(e * (3 * (1 - r))) ≤ v by linarith only [hv.1, heprod]) (sq_nonneg v)
      nlinarith only [h]
    have hevv := mul_nonneg he0 (sq_nonneg v)
    unfold tailLogRemainder at hmaj hneg
    constructor <;> nlinarith only [hmaj, hneg, hcube, hevv]

end F4Heavy.Analysis
