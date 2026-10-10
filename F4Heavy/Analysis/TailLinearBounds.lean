module

public import F4Heavy.Analysis.TailSourceBounds
public import F4Heavy.Analysis.CapReserveUpper

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem tail_weighted_linear_derivative (r : Row) (lam x : ℝ) :
    HasDerivAt (fun z => z * (2 * tailP1 r lam z - alpha r lam - beta r lam))
      (2 + 2 * gamma r lam - alpha r lam - beta r lam -
        2 * (2 + gamma r lam) * x - gamma r lam * x ^ 2 / 2) x := by
  have hi := hasDerivAt_id x
  have hv := ((hi.div_const 2).const_sub 1).sub ((hi.pow 2).div_const 12)
  have hP := (hi.const_sub 1).add (hv.const_mul (gamma r lam))
  convert hi.mul (((hP.const_mul 2).sub_const (alpha r lam)).sub_const (beta r lam)) using 1
  · rfl
  · dsimp
    ring

theorem tail_weighted_linear_monotone (r : Row) (lam : ℝ) (hr : InRow r lam)
    (h10 : 0 < tailGuard r lam 10) :
    MonotoneOn (fun x => x * (2 * tailP1 r lam x - alpha r lam - beta r lam))
      (Set.Icc 0 (tailPStar r lam)) := by
  have hg := row_gamma_pos r lam hr
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 (tailPStar r lam))
  · intro x _
    exact (tail_weighted_linear_derivative r lam x).continuousAt.continuousWithinAt
  · intro x _
    exact (tail_weighted_linear_derivative r lam x).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : x ∈ Set.Icc 0 (tailPStar r lam) := interior_subset hx
    have hs : x ^ 2 ≤ (tailPStar r lam) ^ 2 := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr hx'.2) (add_nonneg hx'.1 (hx'.1.trans hx'.2))]
    have hm1 := mul_le_mul_of_nonneg_left hx'.2 (show 0 ≤ 2 * (2 + gamma r lam) by positivity)
    have hm2 := mul_le_mul_of_nonneg_left hs hg.le
    rw [(tail_weighted_linear_derivative r lam x).deriv]
    change 0 < 2 + 2 * gamma r lam - alpha r lam - beta r lam -
      2 * (2 + gamma r lam) * tailPStar r lam - gamma r lam * (tailPStar r lam) ^ 2 / 2 at h10
    linarith only [hm1, hm2, h10]

theorem tail_weighted_linear_upper (r : Row) (lam Y : ℝ) (hr : InRow r lam)
    (hY : tailTau r lam ≤ Y) (h10 : 0 < tailGuard r lam 10) :
    p lam Y * (2 * tailP1 r lam (p lam Y) - alpha r lam - beta r lam) ≤
      tailPStar r lam * tailC r lam := by
  have hl := inRow_activity_pos r lam hr
  have hp := p_pos lam Y hl
  have hpstar : p lam Y ≤ tailPStar r lam := by
    rw [← tail_probability_at_threshold r lam hl]
    exact tail_probability_antitone lam (tailTau r lam) Y hl hY
  exact tail_weighted_linear_monotone r lam hr h10 ⟨hp.le, hpstar⟩
    ⟨hp.le.trans hpstar, le_rfl⟩ hpstar

theorem tail_child_reserve_upper (r : Row) (lam u : ℝ) (hr : InRow r lam)
    (hu : 0 < u) (hu1 : u < 1) : childJ lam u ≤ tailChildB lam * childH u := by
  have bounds := cap_row_activity_bounds r lam hr
  have h := mul_le_mul_of_nonneg_right
    (cap_child_u_log_upper lam u bounds.1 bounds.2 hu hu1) (childH_nonnegative u hu.le hu1)
  simp only [childJ, if_neg (ne_of_gt hu), tailChildB]
  convert h using 1 <;> ring

theorem tail_response_positive_numerator (r : Row) (lam Y u : ℝ) (hr : InRow r lam)
    (hY : tailTau r lam ≤ Y) (hu : 0 < u) (hu1 : u < 1)
    (h10 : 0 < tailGuard r lam 10) (h11 : 0 < tailGuard r lam 11)
    (h12 : 0 < tailGuard r lam 12) :
    0 < 2 * (delta r lam / p lam Y) * childH u -
      (2 * tailP1 r lam (p lam Y) - alpha r lam - beta r lam) * childJ lam u := by
  have hl := inRow_activity_pos r lam hr
  have hp := p_pos lam Y hl
  have hh : 0 < childH u := by
    simp only [childH, if_neg (ne_of_gt hu)]
    exact div_pos hu (phi_positive u hu hu1)
  have hc : 0 < 2 * tailP1 r lam (p lam Y) - alpha r lam - beta r lam :=
    lt_of_lt_of_le h12 (tail_linear_lower r lam Y hr hY)
  have hB : 0 ≤ tailChildB lam := by unfold tailChildB; positivity
  have hJ := mul_le_mul_of_nonneg_left (tail_child_reserve_upper r lam u hr hu hu1)
    (mul_pos hp hc).le
  have hweighted := mul_le_mul_of_nonneg_right (tail_weighted_linear_upper r lam Y hr hY h10)
    (mul_nonneg hB hh.le)
  have hguard := mul_pos h11 hh
  change 0 < (2 * delta r lam - tailPStar r lam * tailC r lam * tailChildB lam) * childH u at hguard
  have hnum : 0 < 2 * delta r lam * childH u - p lam Y *
      (2 * tailP1 r lam (p lam Y) - alpha r lam - beta r lam) * childJ lam u := by
    nlinarith only [hJ, hweighted, hguard]
  have hid : 2 * (delta r lam / p lam Y) * childH u -
      (2 * tailP1 r lam (p lam Y) - alpha r lam - beta r lam) * childJ lam u =
      (2 * delta r lam * childH u - p lam Y *
        (2 * tailP1 r lam (p lam Y) - alpha r lam - beta r lam) * childJ lam u) / p lam Y := by
    field_simp
    <;> ring
  rw [hid]
  exact div_pos hnum hp

end F4Heavy.Analysis
