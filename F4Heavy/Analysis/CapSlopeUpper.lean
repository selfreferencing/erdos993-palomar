module

public import F4Heavy.Analysis.CapSlopeLower

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified
noncomputable section

def capParentU (r : Row) (lam : ℝ) : ℝ :=
  1 - lam / (1 + 2 * lam) + gamma r lam * (1 - (lam / (1 + 2 * lam)) / 2)

theorem cap_exp_secant_upper (a b : ℝ) : Real.exp b - Real.exp a ≤ Real.exp b * (b - a) := by
  have h := Real.add_one_le_exp (a - b)
  have hm := mul_le_mul_of_nonneg_left h (Real.exp_pos b).le
  rw [← Real.exp_add, add_sub_cancel] at hm
  linarith only [hm]

theorem cap_upper_parent_decreases (lam G U a b : ℝ) (hl : 0 < lam) (hG : 0 ≤ G)
    (hab : a ≤ b) (hU : G * Real.exp b / lam ≤ U) :
    2 * G * (1 + Real.exp b / lam) + 2 * U * (1 - b) ≤
      2 * G * (1 + Real.exp a / lam) + 2 * U * (1 - a) := by
  have hs := mul_le_mul_of_nonneg_left (cap_exp_secant_upper a b)
    (div_nonneg hG hl.le)
  have hu := mul_le_mul_of_nonneg_right hU (sub_nonneg.mpr hab)
  simp only [div_eq_mul_inv] at hs hu ⊢
  nlinarith only [hs, hu]

theorem cap_parentU_pos (r : Row) (lam : ℝ) (hr : InRow r lam) : 0 < capParentU r lam := by
  have hl := inRow_activity_pos r lam hr
  have hg := row_gamma_pos r lam hr
  have hp : lam / (1 + 2 * lam) < 1 :=
    (div_lt_one (by linarith)).mpr (by linarith)
  unfold capParentU
  exact add_pos (sub_pos.mpr hp) (mul_pos hg (by linarith only [hp]))

theorem cap_response_upper_parent_lower (r : Row) (lam Y rho : ℝ) (hr : InRow r lam)
    (hH : parentH Y ≤ q lam) (hrho : FeasibleVacancy lam Y rho) (hY : 1 ≤ Y) :
    2 * (gamma r lam - delta r lam) * (1 + Real.exp Y / lam) - alpha r lam - beta r lam +
      2 * capParentU r lam * (1 - Y) ≤
      (capC r lam Y rho + 2 * capD r lam Y rho) / p lam Y := by
  have hP : parentP r lam Y rho ≤ capParentU r lam := cap_parentP_upper r lam Y rho hr hH hrho
  have hm := mul_le_mul_of_nonpos_right hP (show 2 * (1 - Y) ≤ 0 by linarith only [hY])
  have hid := cap_response_slope_exp_identity r lam Y rho 1 (inRow_activity_pos r lam hr)
  simp only [mul_one] at hid
  simp only [div_eq_mul_inv] at hid ⊢
  nlinarith only [hm, hid]

theorem cap_upper_endpoint_response_positive_ge_one (r : Row) (lam Y rho : ℝ)
    (hr : InRow r lam) (hH : parentH Y ≤ q lam) (hrho : FeasibleVacancy lam Y rho)
    (hY : 1 ≤ Y)
    (hU : (gamma r lam - delta r lam) * (1 + lam) / lam ≤ capParentU r lam)
    (hF : 0 < 2 * (gamma r lam - delta r lam) * (1 + 2 * lam) / lam - alpha r lam - beta r lam +
      2 * capParentU r lam * (1 - (19 / 60 + 2 * lam / 5))) :
    0 < capC r lam Y rho + 2 * capD r lam Y rho := by
  have hl := inRow_activity_pos r lam hr
  have hG := cap_gamma_minus_delta_pos r lam hr
  have hp := p_pos lam Y hl
  have hUP := cap_parentU_pos r lam hr
  have hb := cap_parent_mass_log_upper lam Y hl hH
  have hlog : Real.log (1 + lam) ≤ 19 / 60 + 2 * lam / 5 := by
    have h := cap_log_tangent (1 + lam) (by linarith) cap_log_five_halves_upper
    linarith only [h]
  have hUb : (gamma r lam - delta r lam) * Real.exp (Real.log (1 + lam)) / lam ≤ capParentU r lam := by
    simpa only [Real.exp_log (show 0 < 1 + lam by linarith)] using hU
  have hmono := cap_upper_parent_decreases lam (gamma r lam - delta r lam) (capParentU r lam)
    Y (Real.log (1 + lam)) hl hG.le hb hUb
  rw [Real.exp_log (show 0 < 1 + lam by linarith)] at hmono
  have hweight := mul_le_mul_of_nonneg_left
    (show 1 - (19 / 60 + 2 * lam / 5) ≤ 1 - Real.log (1 + lam) by linarith only [hlog])
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hUP.le)
  have hid : 2 * (gamma r lam - delta r lam) * (1 + 2 * lam) / lam =
      2 * (gamma r lam - delta r lam) * (1 + (1 + lam) / lam) := by
    field_simp
    <;> ring
  rw [hid] at hF
  have hparent := cap_response_upper_parent_lower r lam Y rho hr hH hrho hY
  have hpos : 0 < (capC r lam Y rho + 2 * capD r lam Y rho) / p lam Y := by
    linarith only [hF, hweight, hmono, hparent]
  exact (div_pos_iff.mp hpos).resolve_right (fun hn => (not_lt_of_ge hp.le) hn.2) |>.1

end
end F4Heavy.Analysis
