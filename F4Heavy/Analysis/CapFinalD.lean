module

public import F4Heavy.Analysis.CapD13Guard
public import F4Heavy.Analysis.CapReserveIncrement
public import F4Heavy.Analysis.CapResponseSigns

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem cap_D_adverse_bound (lam u : ℝ) (hr : InRow .D lam)
    (hu : 0 < u) (huc : u ≤ q lam / 2)
    (hprod : childH u * childCurveT lam u < 1) :
    capAdverse u (childCurveT lam u) (childH u) ≤
      capAdverseUpper (q lam / 2) (capDLogChord lam) := by
  have hl := inRow_activity_pos .D lam hr
  have hq := cap_half_q_bounds lam hl
  have hu1 := huc.trans_lt hq.2
  have ht : 0 < childCurveT lam u := by
    have h := cap_child_log_antitone lam u (q lam / 2) hl hu huc hq.2
    rw [(cap_half_q_log_identity lam hl).1] at h
    exact (Real.log_pos (by linarith only [hl] : 1 < lam + 2)).trans_le h
  have hfirst := cap_adverse_height_bound u (childCurveT lam u) (childH u) hu hu1 ht
    (cap_childH_rational_lower u hu.le hu1) (child_w_bounds u hu hu1).1 hprod
  have hsecond := cap_adverse_upper_monotone lam hl ⟨hu, huc⟩ ⟨hq.1, le_rfl⟩ huc
  dsimp only at hsecond
  rw [(cap_half_q_log_identity lam hl).1] at hsecond
  exact (hfirst.trans hsecond).trans (cap_adverse_upper_log_antitone (q lam / 2)
    (capDLogChord lam) (Real.log (lam + 2)) hq.1 hq.2 (cap_D_log_chord_pos lam hr)
    (cap_D_log_chord_lower lam hr) (cap_D_log_upper lam hr).le)

theorem cap_D_reserve_coefficient (lam Y rho u : ℝ) (hr : InRow .D lam)
    (hH : parentH Y ≤ q lam) (hrho : FeasibleVacancy lam Y rho)
    (hu : 0 < u) (huc : u ≤ capChild lam Y) :
    0 ≤ capB .D lam Y rho - 1 / 500 -
      delta .D lam * capAdverse u (childCurveT lam u) (childH u) := by
  have hl := inRow_activity_pos .D lam hr
  have hu1 := huc.trans_lt (cap_child_lt_one lam Y hl)
  have hd := row_delta_pos .D lam hr
  by_cases hprod : childH u * childCurveT lam u < 1
  · have hadv := cap_D_adverse_bound lam u hr hu (huc.trans (min_le_right _ _)) hprod
    have hm := mul_le_mul_of_nonneg_left hadv hd.le
    have hb := cap_parent_b_lower .D lam Y rho hl hH hrho
      (le_of_lt (lt_trans (by norm_num) (cap_row_beta_lower .D lam hr)))
    have hg := cap_d13_D_13_positive lam hr
    change beta .D lam * lam / (lam ^ 2 + 3 * lam + 1) ≤ capB .D lam Y rho at hb
    linarith only [hm, hb, hg]
  · have hb := cap_b_uniform_lower .D lam Y rho hr hH hrho
    have hn : capAdverse u (childCurveT lam u) (childH u) ≤ 0 := by
      unfold capAdverse
      apply div_nonpos_of_nonpos_of_nonneg (by linarith only [le_of_not_gt hprod])
      exact mul_nonneg (mul_nonneg hu.le (sq_nonneg _)) (child_w_bounds u hu hu1).1.le
    have hm := mul_nonpos_of_nonneg_of_nonpos hd.le hn
    linarith only [hb, hm]

theorem cap_scalar_bounds_D (lam Y rho : ℝ) (hr : InRow .D lam)
    (hY : 0 < Y) (hH : parentH Y ≤ q lam) (hrho : FeasibleVacancy lam Y rho) :
    CapScalarBounds .D lam Y rho := by
  apply cap_scalar_bounds_from_reserve_increment .D lam Y rho hr hY hH hrho
  intro u hu huc
  exact cap_reserve_increment_of_coefficient lam Y (capB .D lam Y rho) (delta .D lam)
    (inRow_activity_pos .D lam hr)
    (fun v hv hvc => cap_D_reserve_coefficient lam Y rho v hr hH hrho hv hvc) u hu huc

theorem fixedParentCap_D_complete : FixedParentCap .D := by
  apply fixedParentCap_of_scalar_bounds
  intro lam Y rho hr hY hH hrho
  exact cap_scalar_bounds_D lam Y rho hr hY hH hrho

end F4Heavy.Analysis
