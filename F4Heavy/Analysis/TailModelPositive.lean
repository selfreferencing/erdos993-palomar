module

public import F4Heavy.Analysis.TailModelGeometry
public import F4Heavy.Analysis.TailOneEndpoint
public import F4Heavy.Analysis.TailChildSupport

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem tail_reserveK_positive (r : Row) (lam : ℝ) (hr : InRow r lam) :
    0 < tailReserveK r lam := by
  have hl := inRow_activity_pos r lam hr
  have hs : 0 < tailPStar r lam := by
    rw [← tail_probability_at_threshold r lam hl]
    exact p_pos lam _ hl
  exact div_pos (row_delta_pos r lam hr) hs

theorem tail_child_support_vertices (r : Row) (lam : ℝ) (hr : InRow r lam) :
    0 < tailChildH0 lam ∧ tailChildH0 lam < tailChildHb lam ∧ tailChildHb lam < 1 := by
  have hl := inRow_activity_pos r lam hr
  have hq := q_pos lam hl
  have hq1 := q_lt_one lam hl
  have hC := tail_childC_range r lam hr
  have hCq : tailChildC lam ≤ q lam := by
    unfold tailChildC q
    apply (div_le_div_iff₀ (by positivity : 0 < 29 + 10 * lam) (by positivity : 0 < 1 + lam)).mpr
    nlinarith only [hl]
  have hheight := (tail_child_height_threshold lam hl).trans (childH_linear_upper (q lam) hq.le hq1)
  refine ⟨?_, ?_, ?_⟩
  · unfold tailChildH0
    have h1 : 0 < 1 - q lam := sub_pos.mpr hq1
    have h2 : 0 < 2 - q lam := by linarith only [hq1]
    have hd : 0 < (q lam) ^ 2 - 12 * q lam + 12 := by nlinarith only [sq_nonneg (q lam), hq1]
    positivity
  · unfold tailChildHb
    linarith only [hheight, hCq, hq]
  · unfold tailChildHb
    linarith only [hC.1]

theorem tail_model_positive_of_guards (r : Row) (lam J h y : ℝ) (hr : InRow r lam)
    (hJ : 0 < J) (hJC : J ≤ tailChildC lam) (hJL : J ≤ 33 / 8 - 4 * h)
    (hh0 : tailChildH0 lam ≤ h) (hh1 : h ≤ 1)
    (h12 : 0 < tailGuard r lam 12) (h13 : 0 < tailGuard r lam 13)
    (h14 : 0 < tailGuard r lam 14) (h15 : 0 < tailGuard r lam 15)
    (h16 : 0 < tailGuard r lam 16) : 0 < tailModel r lam J h y := by
  have hK := tail_reserveK_positive r lam hr
  have hv := tail_child_support_vertices r lam hr
  have hC := hJ.trans_le hJC
  have hB : 0 ≤ beta r lam := by have hb := cap_row_beta_lower r lam hr; linarith only [hb]
  change 0 < tailC r lam at h12
  change 0 < tailReserveK r lam + tailD r lam * tailChildC lam at h13
  change 0 < responseNumerator (tailA r lam) (beta r lam) (tailC r lam) (tailD r lam)
    (tailReserveK r lam) (tailChildC lam) (tailChildH0 lam) at h14
  change 0 < responseNumerator (tailA r lam) (beta r lam) (tailC r lam) (tailD r lam)
    (tailReserveK r lam) (tailChildC lam) (tailChildHb lam) at h15
  change 0 < responseNumerator (tailA r lam) (beta r lam) (tailC r lam) (tailD r lam)
    (tailReserveK r lam) (1 / 8) 1 at h16
  unfold tailModel
  by_cases hd : 0 ≤ tailD r lam
  · exact tail_response_positive_curvature _ _ _ _ _ _ _ _ _ _
      hB h12.le hd hK hv.1.le hh0 hJ hJC h14
  have hd' : tailD r lam ≤ 0 := le_of_not_ge hd
  by_cases hh : h ≤ tailChildHb lam
  · have hpos := tail_response_chord_interval (tailA r lam) (beta r lam) (tailC r lam)
      (tailD r lam) (tailReserveK r lam) (tailChildC lam) (tailChildC lam)
      (tailChildH0 lam) (tailChildHb lam) h y hK.le hd' hv.2.1 hh0 hh hC hC h13 h13 h14 h15
    have hid : (1 - (h - tailChildH0 lam) / (tailChildHb lam - tailChildH0 lam)) * tailChildC lam +
        (h - tailChildH0 lam) / (tailChildHb lam - tailChildH0 lam) * tailChildC lam = tailChildC lam := by ring
    rw [hid] at hpos
    exact hpos.trans_le (tail_response_envelope_order _ _ _ _ _ J (tailChildC lam) h y hK.le hJ hJC)
  · have hbh : tailChildHb lam ≤ h := le_of_not_ge hh
    have hC8 : 1 / 8 ≤ tailChildC lam := by have hb := tail_childC_range r lam hr; linarith only [hb.1]
    have hG8 : 0 < tailReserveK r lam + tailD r lam * (1 / 8) := by
      have hm := mul_le_mul_of_nonpos_left hC8 hd'
      linarith only [h13, hm]
    have hpos := tail_response_chord_interval (tailA r lam) (beta r lam) (tailC r lam)
      (tailD r lam) (tailReserveK r lam) (tailChildC lam) (1 / 8)
      (tailChildHb lam) 1 h y hK.le hd' hv.2.2 hbh hh1 hC (by norm_num) h13 hG8 h15 h16
    have hid : (1 - (h - tailChildHb lam) / (1 - tailChildHb lam)) * tailChildC lam +
        (h - tailChildHb lam) / (1 - tailChildHb lam) * (1 / 8) = 33 / 8 - 4 * h := by
      have hden : 1 - tailChildHb lam ≠ 0 := ne_of_gt (sub_pos.mpr hv.2.2)
      apply (mul_right_cancel₀ hden)
      field_simp [hden]
      unfold tailChildHb
      ring
    rw [hid] at hpos
    exact hpos.trans_le (tail_response_envelope_order _ _ _ _ _ J (33 / 8 - 4 * h) h y hK.le hJ hJL)

theorem tail_model_child_positive (r : Row) (lam u y : ℝ) (hr : InRow r lam)
    (hu : 0 ≤ u) (huq : u ≤ q lam) (hJ : 0 < childJ lam u)
    (hguards : ∀ i, 12 ≤ i → i ≤ 16 → 0 < tailGuard r lam i) :
    0 < tailModel r lam (childJ lam u) (childH u) y := by
  have hl := inRow_activity_pos r lam hr
  have hh := tail_child_height_range lam u hl hu huq
  exact tail_model_positive_of_guards r lam (childJ lam u) (childH u) y hr hJ
    (tail_childJ_constant_upper r lam u hr hu (huq.trans_lt (q_lt_one lam hl)))
    (tail_childJ_line_upper r lam u hr hu huq) hh.1 hh.2
    (hguards 12 (by omega) (by omega)) (hguards 13 (by omega) (by omega))
    (hguards 14 (by omega) (by omega)) (hguards 15 (by omega) (by omega))
    (hguards 16 (by omega) (by omega))

end F4Heavy.Analysis
