module

public import F4Heavy.Analysis.LogBounds

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis

noncomputable def rationalLog (x : ℝ) : ℝ :=
  3 * (9 * x ^ 2 - 1) / (9 * x ^ 2 + 12 * x + 1)

noncomputable def negativeLogUpper (x : ℝ) : ℝ :=
  (1386294361120 : ℝ) / 1000000000000 - 21 / 73 - rationalLog x

theorem rationalLog_denominator_positive (x : ℝ) (hx : 0 < x) :
    0 < 9 * x ^ 2 + 12 * x + 1 := by positivity

theorem rationalLog_remainder_derivative (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y => Real.log y - rationalLog y)
      ((3 * x - 1) ^ 4 / (x * (9 * x ^ 2 + 12 * x + 1) ^ 2)) x := by
  have hid := hasDerivAt_id x
  have hpow := (hid.pow 2).const_mul 9
  have hn := (hpow.sub_const 1).const_mul 3
  have hd := (hpow.add (hid.const_mul 12)).add_const 1
  have hden := ne_of_gt (rationalLog_denominator_positive x hx)
  have hder := (Real.hasDerivAt_log (ne_of_gt hx)).sub (hn.div hd hden)
  convert hder using 1
  · rfl
  · dsimp
    field_simp
    ring

theorem rationalLog_remainder_monotone :
    MonotoneOn (fun x => Real.log x - rationalLog x) (Set.Ioi 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
  · intro x hx
    exact (rationalLog_remainder_derivative x hx).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : 0 < x := by simpa only [interior_Ioi, Set.mem_Ioi] using hx
    exact (rationalLog_remainder_derivative x hx').differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : 0 < x := by simpa only [interior_Ioi, Set.mem_Ioi] using hx
    rw [(rationalLog_remainder_derivative x hx').deriv]
    exact div_nonneg (by positivity)
      (mul_pos hx' (sq_pos_of_pos (rationalLog_denominator_positive x hx'))).le

theorem rationalLog_endpoints : rationalLog (1 / 4) = -(21 / 73 : ℝ) ∧
    rationalLog 1 = (12 / 11 : ℝ) := by norm_num [rationalLog]

theorem negative_log_rational_upper (x : ℝ) (hx : (1 / 4 : ℝ) ≤ x) :
    -Real.log x < negativeLogUpper x := by
  have hx' : 0 < x := by linarith
  have h := rationalLog_remainder_monotone (show (1 / 4 : ℝ) ∈ Set.Ioi 0 by norm_num)
    hx' hx
  dsimp only at h
  rw [rationalLog_endpoints.1, Real.log_div (by norm_num) (by norm_num), Real.log_one] at h
  unfold negativeLogUpper
  linarith only [h, log_four_lt_certificate_constant]

theorem negative_log_enclosure (x : ℝ) (hx : (1 / 4 : ℝ) ≤ x) (hx1 : x ≤ 1) :
    2 * (1 - x) / (1 + x) ≤ -Real.log x ∧ -Real.log x ≤ negativeLogUpper x :=
  ⟨negative_log_lower_bound x (by linarith) hx1, (negative_log_rational_upper x hx).le⟩

end F4Heavy.Analysis
