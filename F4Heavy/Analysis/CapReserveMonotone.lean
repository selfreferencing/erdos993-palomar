module

public import F4Heavy.Analysis.CapReserveLog

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem cap_half_q_bounds (lam : ℝ) (hl : 0 < lam) :
    0 < q lam / 2 ∧ q lam / 2 < 1 := by
  have hq := q_pos lam hl
  have hq1 := q_lt_one lam hl
  constructor <;> linarith only [hq, hq1]

theorem cap_half_q_log_identity (lam : ℝ) (hl : 0 < lam) :
    childCurveT lam (q lam / 2) = Real.log (lam + 2) ∧
      phi (q lam / 2) = Real.log (2 * (lam + 1) / (lam + 2)) := by
  have h1 : 1 + lam ≠ 0 := by positivity
  constructor
  · unfold childCurveT q
    congr 1
    field_simp
    <;> ring
  · rw [phi_eq_negative_log, ← Real.log_inv]
    congr 1
    unfold q
    field_simp
    <;> ring_nf
    <;> field_simp [show 2 + lam ≠ 0 by positivity]
    <;> ring

theorem cap_half_q_height_log_product (lam : ℝ) (hl : 13 / 10 ≤ lam) :
    1 < childH (q lam / 2) * childCurveT lam (q lam / 2) := by
  have hp : 0 < lam := by linarith only [hl]
  have hv := cap_half_q_bounds lam hp
  have hphi := phi_positive (q lam / 2) hv.1 hv.2
  have hid := cap_half_q_log_identity lam hp
  have hm := cap_reserve_log_margin_positive lam hl
  have hg : phi (q lam / 2) < q lam / 2 * childCurveT lam (q lam / 2) := by
    rw [hid.1, hid.2]
    unfold capReserveLogMargin at hm
    unfold q
    linarith only [hm]
  rw [childH, if_neg (ne_of_gt hv.1), div_mul_eq_mul_div]
  exact (lt_div_iff₀ hphi).mpr (by simpa using hg)

theorem cap_child_log_antitone (lam u v : ℝ) (hl : 0 < lam)
    (hu : 0 < u) (huv : u ≤ v) (hv : v < 1) :
    childCurveT lam v ≤ childCurveT lam u := by
  have hv0 := hu.trans_le huv
  apply Real.log_le_log (div_pos (mul_pos hl (sub_pos.mpr hv)) hv0)
  apply (div_le_div_iff₀ hv0 hu).mpr
  nlinarith only [mul_nonneg hl.le (sub_nonneg.mpr huv)]

theorem cap_child_height_log_product (lam u : ℝ) (hl : 13 / 10 ≤ lam)
    (hu : 0 < u) (huc : u ≤ q lam / 2) : 1 < childH u * childCurveT lam u := by
  have hp : 0 < lam := by linarith only [hl]
  have hv := cap_half_q_bounds lam hp
  have hh := cap_childH_height_increment u (q lam / 2) hu.le huc hv.2
  have hhh : childH (q lam / 2) ≤ childH u := by linarith only [hh, huc]
  have ht := cap_child_log_antitone lam u (q lam / 2) hp hu huc hv.2
  have htv : 0 < childCurveT lam (q lam / 2) := by
    rw [(cap_half_q_log_identity lam hp).1]
    apply Real.log_pos
    linarith only [hp]
  have hhu := childH_nonnegative u hu.le (huc.trans_lt hv.2)
  exact (cap_half_q_height_log_product lam hl).trans_le (mul_le_mul hhh ht htv.le hhu)

noncomputable def capReserveDen (lam u : ℝ) : ℝ := phi u * childCurveT lam u

theorem cap_reserve_den_derivative (lam u : ℝ) (hl : 0 < lam)
    (hu : 0 < u) (hu1 : u < 1) :
    HasDerivAt (capReserveDen lam)
      ((u * childCurveT lam u - phi u) / (u * (1 - u))) u := by
  have h := (phi_derivative u hu1).mul (childCurveT_derivative lam u hl hu hu1)
  convert h using 1
  · rfl
  · field_simp
    <;> ring

theorem cap_reserve_den_monotone (lam : ℝ) (hl : 13 / 10 ≤ lam) :
    MonotoneOn (capReserveDen lam) (Set.Ioc 0 (q lam / 2)) := by
  have hp : 0 < lam := by linarith only [hl]
  have hv := cap_half_q_bounds lam hp
  apply monotoneOn_of_deriv_nonneg (convex_Ioc 0 (q lam / 2))
  · intro u hu
    exact (cap_reserve_den_derivative lam u hp hu.1 (hu.2.trans_lt hv.2)).continuousAt.continuousWithinAt
  · intro u hu
    have hu' : u ∈ Set.Ioc 0 (q lam / 2) := interior_subset hu
    exact (cap_reserve_den_derivative lam u hp hu'.1 (hu'.2.trans_lt hv.2)).differentiableAt.differentiableWithinAt
  · intro u hu
    have hu' : u ∈ Set.Ioc 0 (q lam / 2) := interior_subset hu
    have hu1 := hu'.2.trans_lt hv.2
    have hf := phi_positive u hu'.1 hu1
    have hprod := cap_child_height_log_product lam u hl hu'.1 hu'.2
    rw [childH, if_neg (ne_of_gt hu'.1), div_mul_eq_mul_div] at hprod
    have hn := (lt_div_iff₀ hf).mp hprod
    rw [(cap_reserve_den_derivative lam u hp hu'.1 hu1).deriv]
    apply div_nonneg _ (mul_pos hu'.1 (sub_pos.mpr hu1)).le
    linarith only [hn]

theorem cap_reserve_quotient_identity (lam u : ℝ) (hu : 0 < u) (hu1 : u < 1) :
    (childH u) ^ 2 / childJ lam u = 1 / capReserveDen lam u := by
  have hf := ne_of_gt (phi_positive u hu hu1)
  simp only [childH, childJ, if_neg (ne_of_gt hu), capReserveDen, childCurveT]
  field_simp
  <;> ring

theorem cap_reserve_quotient_antitone (lam u v : ℝ) (hl : 13 / 10 ≤ lam)
    (hu : 0 < u) (huv : u ≤ v) (hv : v ≤ q lam / 2) :
    (childH v) ^ 2 / childJ lam v ≤ (childH u) ^ 2 / childJ lam u := by
  have hp : 0 < lam := by linarith only [hl]
  have hq := cap_half_q_bounds lam hp
  have hu1 := (huv.trans hv).trans_lt hq.2
  have hv0 := hu.trans_le huv
  have hv1 := hv.trans_lt hq.2
  have hden : 0 < capReserveDen lam u := by
    have ht := cap_child_log_antitone lam u (q lam / 2) hp hu (huv.trans hv) hq.2
    rw [(cap_half_q_log_identity lam hp).1] at ht
    have hg := Real.log_pos (show 1 < lam + 2 by linarith only [hp])
    exact mul_pos (phi_positive u hu hu1) (hg.trans_le ht)
  rw [cap_reserve_quotient_identity lam u hu hu1, cap_reserve_quotient_identity lam v hv0 hv1]
  exact one_div_le_one_div_of_le hden (cap_reserve_den_monotone lam hl ⟨hu, huv.trans hv⟩ ⟨hv0, hv⟩ huv)

end F4Heavy.Analysis
