module

public import F4Heavy.Analysis.CapAdverseAlgebra

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem cap_reserve_corrected_derivative (lam b d u : ℝ) (hl : 0 < lam)
    (hu : 0 < u) (hu1 : u < 1) (ht : 0 < childCurveT lam u) :
    HasDerivAt (fun x => (b - 1 / 500) * childH x + d / capReserveDen lam x)
      ((b - 1 / 500 - d * capAdverse u (childCurveT lam u) (childH u)) *
        (-childCurveW u / ((1 - u) * phi u))) u := by
  have hf := phi_positive u hu hu1
  have hw := (child_w_bounds u hu hu1).1
  have hd : capReserveDen lam u ≠ 0 := ne_of_gt (mul_pos hf ht)
  have h := ((childH_derivative u hu hu1).const_mul (b - 1 / 500)).add
    ((hasDerivAt_const u d).div (cap_reserve_den_derivative lam u hl hu hu1) hd)
  convert h using 1
  unfold capAdverse capReserveDen childCurveW
  field_simp [ne_of_gt hf, ne_of_gt ht, ne_of_gt hu, ne_of_gt hw, ne_of_gt (sub_pos.mpr hu1)]
  simp only [childH, if_neg (ne_of_gt hu)]
  field_simp [ne_of_gt hf]
  <;> ring

theorem cap_reserve_increment_of_coefficient (lam Y b d : ℝ) (hl : 0 < lam)
    (hc : ∀ u, 0 < u → u ≤ capChild lam Y →
      0 ≤ b - 1 / 500 - d * capAdverse u (childCurveT lam u) (childH u))
    (u : ℝ) (hu : 0 < u) (huc : u ≤ capChild lam Y) :
    (childH u - childH (capChild lam Y)) / 500 ≤
      b * (childH u - childH (capChild lam Y)) + d *
        ((childH u) ^ 2 / childJ lam u -
          (childH (capChild lam Y)) ^ 2 / childJ lam (capChild lam Y)) := by
  have hq := cap_half_q_bounds lam hl
  have hu1 := huc.trans_lt (cap_child_lt_one lam Y hl)
  have hv0 := hu.trans_le huc
  have hv1 := cap_child_lt_one lam Y hl
  have ht (v : ℝ) (hv : v ∈ Set.Ioc 0 (capChild lam Y)) : 0 < childCurveT lam v := by
    have h := cap_child_log_antitone lam v (q lam / 2) hl hv.1
      (hv.2.trans (min_le_right _ _)) hq.2
    rw [(cap_half_q_log_identity lam hl).1] at h
    exact (Real.log_pos (by linarith only [hl] : 1 < lam + 2)).trans_le h
  have hm : AntitoneOn (fun v => (b - 1 / 500) * childH v + d / capReserveDen lam v)
      (Set.Ioc 0 (capChild lam Y)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioc 0 (capChild lam Y))
    · intro v hv
      exact (cap_reserve_corrected_derivative lam b d v hl hv.1 (hv.2.trans_lt hv1) (ht v hv)).continuousAt.continuousWithinAt
    · intro v hv
      have hv' : v ∈ Set.Ioc 0 (capChild lam Y) := interior_subset hv
      exact (cap_reserve_corrected_derivative lam b d v hl hv'.1 (hv'.2.trans_lt hv1) (ht v hv')).differentiableAt.differentiableWithinAt
    · intro v hv
      have hv' : v ∈ Set.Ioc 0 (capChild lam Y) := interior_subset hv
      rw [(cap_reserve_corrected_derivative lam b d v hl hv'.1 (hv'.2.trans_lt hv1) (ht v hv')).deriv]
      have hneg := childH_derivative_negative v hv'.1 (hv'.2.trans_lt hv1)
      rw [(childH_derivative v hv'.1 (hv'.2.trans_lt hv1)).deriv] at hneg
      exact mul_nonpos_of_nonneg_of_nonpos (hc v hv'.1 hv'.2) hneg.le
  have hmuv := hm ⟨hu, huc⟩ ⟨hv0, le_rfl⟩ huc
  rw [cap_reserve_quotient_identity lam u hu hu1,
    cap_reserve_quotient_identity lam (capChild lam Y) hv0 hv1]
  dsimp only at hmuv
  simp only [div_eq_mul_inv] at hmuv ⊢
  nlinarith only [hmuv]

end F4Heavy.Analysis
