module

public import F4Heavy.Analysis.TailLinearBounds

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem tail_childC_range (r : Row) (lam : ℝ) (hr : InRow r lam) :
    8 / 37 ≤ tailChildC lam ∧ tailChildC lam ≤ 70 / 157 := by
  have hb := cap_row_activity_bounds r lam hr
  have hd : 0 < 29 + 10 * lam := by linarith only [hb.1]
  unfold tailChildC
  constructor
  · apply (le_div_iff₀ hd).mpr
    linarith only [hb.1]
  · apply (div_le_iff₀ hd).mpr
    linarith only [hb.2]

theorem tail_exponential_product_derivative (x : ℝ) :
    HasDerivAt (fun z => Real.exp (1 + 3 * z / 2) * (1 - z))
      (Real.exp (1 + 3 * x / 2) * (1 - 3 * x) / 2) x := by
  have hi := hasDerivAt_id x
  convert ((((hi.const_mul 3).div_const 2).const_add 1).exp).mul (hi.const_sub 1) using 1
  · rfl
  · dsimp
    ring

theorem tail_exponential_product_monotone :
    MonotoneOn (fun x : ℝ => Real.exp (1 + 3 * x / 2) * (1 - x)) (Set.Iic (1 / 3)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Iic (1 / 3 : ℝ))
  · intro x _
    exact (tail_exponential_product_derivative x).continuousAt.continuousWithinAt
  · intro x _
    exact (tail_exponential_product_derivative x).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : x ∈ Set.Iic (1 / 3) := interior_subset hx
    change x ≤ 1 / 3 at hx'
    rw [(tail_exponential_product_derivative x).deriv]
    have h : 0 ≤ 1 - 3 * x := by linarith only [hx']
    positivity

theorem tail_exponential_product_antitone :
    AntitoneOn (fun x : ℝ => Real.exp (1 + 3 * x / 2) * (1 - x)) (Set.Ici (1 / 3)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici (1 / 3 : ℝ))
  · intro x _
    exact (tail_exponential_product_derivative x).continuousAt.continuousWithinAt
  · intro x _
    exact (tail_exponential_product_derivative x).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : 1 / 3 ≤ x := interior_subset hx
    rw [(tail_exponential_product_derivative x).deriv]
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by linarith only [hx'])) (by norm_num)

theorem tail_exponential_product_left :
    (29 : ℝ) / 10 < Real.exp (1 + 3 * (8 / 37) / 2) * (1 - 8 / 37) := by
  have h1 := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num) 6
  have h2 := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 3 * (8 / 37) / 2 by norm_num) 6
  norm_num [Finset.sum_range_succ] at h1 h2
  rw [Real.exp_add]
  nlinarith only [mul_le_mul h1 h2 (by norm_num) (Real.exp_pos 1).le]

theorem tail_exponential_product_right :
    (29 : ℝ) / 10 < Real.exp (1 + 3 * (70 / 157) / 2) * (1 - 70 / 157) := by
  have h1 := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num) 6
  have h2 := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 3 * (70 / 157) / 2 by norm_num) 6
  norm_num [Finset.sum_range_succ] at h1 h2
  rw [Real.exp_add]
  nlinarith only [mul_le_mul h1 h2 (by norm_num) (Real.exp_pos 1).le]

theorem tail_childC_log_bound (r : Row) (lam : ℝ) (hr : InRow r lam) :
    Real.log (lam / tailChildC lam) < 1 + 3 * tailChildC lam / 2 := by
  have hl := inRow_activity_pos r lam hr
  have hb := tail_childC_range r lam hr
  have hC : 0 < tailChildC lam := by linarith only [hb.1]
  have hC1 : tailChildC lam < 1 := by linarith only [hb.2]
  have hprod : 29 / 10 < Real.exp (1 + 3 * tailChildC lam / 2) * (1 - tailChildC lam) := by
    by_cases hc : tailChildC lam ≤ 1 / 3
    · exact tail_exponential_product_left.trans_le
        (tail_exponential_product_monotone (by norm_num) hc hb.1)
    · exact tail_exponential_product_right.trans_le
        (tail_exponential_product_antitone (le_of_not_ge hc) (by norm_num) hb.2)
  have hid : lam * (1 - tailChildC lam) = 29 / 10 * tailChildC lam := by
    unfold tailChildC
    field_simp
    <;> ring
  have hm := mul_lt_mul_of_pos_left hprod hC
  have hclear : lam < tailChildC lam * Real.exp (1 + 3 * tailChildC lam / 2) := by
    nlinarith only [hm, hid, hC1]
  have hdiv : lam / tailChildC lam < Real.exp (1 + 3 * tailChildC lam / 2) := by
    apply (div_lt_iff₀ hC).mpr
    nlinarith only [hclear]
  have hlog := Real.log_lt_log (div_pos hl hC) hdiv
  simpa only [Real.log_exp] using hlog

theorem tail_childJ_constant_upper (r : Row) (lam u : ℝ) (hr : InRow r lam)
    (hu : 0 ≤ u) (hu1 : u < 1) : childJ lam u ≤ tailChildC lam := by
  have hl := inRow_activity_pos r lam hr
  have hC : 0 < tailChildC lam := by have hb := tail_childC_range r lam hr; linarith only [hb.1]
  by_cases hz : u = 0
  · subst u
    simpa [childJ] using hC.le
  have hup : 0 < u := lt_of_le_of_ne hu (Ne.symm hz)
  have hzpos : 0 < tailChildC lam * (1 - u) / u := div_pos (mul_pos hC (sub_pos.mpr hu1)) hup
  have ht1 := tail_childC_log_bound r lam hr
  have ht2 := Real.log_le_sub_one_of_pos hzpos
  have hid : lam * (1 - u) / u = (lam / tailChildC lam) * (tailChildC lam * (1 - u) / u) := by field_simp
  have hlog : Real.log (lam * (1 - u) / u) ≤
      tailChildC lam / 2 + tailChildC lam / u := by
    rw [hid, Real.log_mul (ne_of_gt (div_pos hl hC)) (ne_of_gt hzpos)]
    have heq : 3 * tailChildC lam / 2 + tailChildC lam * (1 - u) / u =
        tailChildC lam / 2 + tailChildC lam / u := by field_simp <;> ring
    linarith only [ht1, ht2, heq]
  have huT := mul_le_mul_of_nonneg_left hlog hu
  have hclear : u * (tailChildC lam / 2 + tailChildC lam / u) = tailChildC lam * (1 + u / 2) := by
    field_simp
    <;> ring
  rw [hclear] at huT
  have hh := childH_nonnegative u hu hu1
  have hJ := mul_le_mul_of_nonneg_right huT hh
  have hH := mul_le_mul_of_nonneg_left (childH_linear_upper u hu hu1)
    (show 0 ≤ tailChildC lam * (1 + u / 2) by positivity)
  simp only [childJ, if_neg hz]
  nlinarith only [hJ, hH, mul_nonneg hC.le (sq_nonneg u)]

end F4Heavy.Analysis
