module

public import F4Heavy.Analysis.CapParentBounds
public import F4Heavy.Analysis.CapReserveMonotone

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

noncomputable def capAdverse (u T h : ℝ) : ℝ := (1 - h * T) / (u * T ^ 2 * (h - 1 + u))
noncomputable def capAdverseUpper (u T : ℝ) : ℝ :=
  (2 - u - 2 * (1 - u) * T) / (u ^ 2 * (1 - u) * T ^ 2)

theorem cap_adverse_height_bound (u T h : ℝ) (hu : 0 < u) (hu1 : u < 1)
    (hT : 0 < T) (hh : 2 * (1 - u) / (2 - u) ≤ h) (hw : 0 < h - 1 + u)
    (hprod : h * T < 1) : capAdverse u T h ≤ capAdverseUpper u T := by
  have hlower := (div_le_iff₀ (by linarith : 0 < 2 - u)).mp hh
  have hweight : 0 ≤ 1 - T * (1 - u) := by
    have hm := mul_pos hT hw
    nlinarith only [hm, hprod]
  unfold capAdverse capAdverseUpper
  apply (div_le_div_iff₀ (by positivity : 0 < u * T ^ 2 * (h - 1 + u))
    (by positivity : 0 < u ^ 2 * (1 - u) * T ^ 2)).mpr
  have hid : (2 - u - 2 * (1 - u) * T) * (u * T ^ 2 * (h - 1 + u)) -
      (1 - h * T) * (u ^ 2 * (1 - u) * T ^ 2) =
      T ^ 2 * u * (1 - T * (1 - u)) * (h * (2 - u) - 2 * (1 - u)) := by ring
  have hn : 0 ≤ T ^ 2 * u * (1 - T * (1 - u)) * (h * (2 - u) - 2 * (1 - u)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg T) hu.le) hweight) (sub_nonneg.mpr hlower)
  linarith only [hid, hn]

theorem cap_adverse_upper_discriminant (u : ℝ) (hu : 0 < u) (hu2 : u ≤ 1 / 2) :
    0 < 4 * (4 * (1 - u) ^ 2) * (4 - 2 * u) - (-2 * u ^ 2 + 9 * u - 6) ^ 2 := by
  have h4 := pow_le_pow_left₀ hu.le hu2 4
  norm_num at h4
  have h3 : 0 ≤ u ^ 3 := by positivity
  nlinarith only [h4, h3, sq_nonneg u, hu2]

theorem cap_adverse_upper_derivative_numerator (u T : ℝ) (hu : 0 < u) (hu2 : u ≤ 1 / 2) :
    0 < 4 * (1 - u) ^ 2 * T ^ 2 + (-2 * u ^ 2 + 9 * u - 6) * T + 4 - 2 * u := by
  simpa only [add_sub_assoc] using quadratic_positive (4 * (1 - u) ^ 2) (-2 * u ^ 2 + 9 * u - 6) (4 - 2 * u) T
    (mul_pos (by norm_num) (sq_pos_of_pos (by linarith only [hu2])))
    (cap_adverse_upper_discriminant u hu hu2)

theorem cap_adverse_upper_derivative (lam u : ℝ) (hl : 0 < lam)
    (hu : 0 < u) (hu1 : u < 1) (hT : 0 < childCurveT lam u) :
    HasDerivAt (fun x => capAdverseUpper x (childCurveT lam x))
      ((4 * (1 - u) ^ 2 * (childCurveT lam u) ^ 2 +
        (-2 * u ^ 2 + 9 * u - 6) * childCurveT lam u + 4 - 2 * u) /
        ((childCurveT lam u) ^ 3 * u ^ 3 * (1 - u) ^ 2)) u := by
  have hi := hasDerivAt_id u
  have ht := childCurveT_derivative lam u hl hu hu1
  have hn := (hi.const_sub 2).sub (((hi.const_sub 1).const_mul 2).mul ht)
  have hd := ((hi.pow 2).mul (hi.const_sub 1)).mul (ht.pow 2)
  have h := hn.div hd (ne_of_gt (by positivity : 0 < u ^ 2 * (1 - u) * (childCurveT lam u) ^ 2))
  convert h using 1
  · rfl
  · dsimp
    field_simp [ne_of_gt hT, ne_of_gt hu, ne_of_gt (sub_pos.mpr hu1)]
    <;> ring

theorem cap_adverse_upper_monotone (lam : ℝ) (hl : 0 < lam) :
    MonotoneOn (fun u => capAdverseUpper u (childCurveT lam u)) (Set.Ioc 0 (q lam / 2)) := by
  have hq := cap_half_q_bounds lam hl
  have ht (u : ℝ) (hu : u ∈ Set.Ioc 0 (q lam / 2)) : 0 < childCurveT lam u := by
    have h := cap_child_log_antitone lam u (q lam / 2) hl hu.1 hu.2 hq.2
    rw [(cap_half_q_log_identity lam hl).1] at h
    exact (Real.log_pos (by linarith only [hl] : 1 < lam + 2)).trans_le h
  apply monotoneOn_of_deriv_nonneg (convex_Ioc 0 (q lam / 2))
  · intro u hu
    exact (cap_adverse_upper_derivative lam u hl hu.1 (hu.2.trans_lt hq.2) (ht u hu)).continuousAt.continuousWithinAt
  · intro u hu
    have hu' : u ∈ Set.Ioc 0 (q lam / 2) := interior_subset hu
    exact (cap_adverse_upper_derivative lam u hl hu'.1 (hu'.2.trans_lt hq.2) (ht u hu')).differentiableAt.differentiableWithinAt
  · intro u hu
    have hu' : u ∈ Set.Ioc 0 (q lam / 2) := interior_subset hu
    rw [(cap_adverse_upper_derivative lam u hl hu'.1 (hu'.2.trans_lt hq.2) (ht u hu')).deriv]
    have hu2 : u ≤ 1 / 2 := by have h := q_lt_one lam hl; linarith only [h, hu'.2]
    exact (div_pos (cap_adverse_upper_derivative_numerator u (childCurveT lam u) hu'.1 hu2)
      (by have h := ht u hu'; have h1 := hu'.2.trans_lt hq.2; have hu0 := hu'.1; positivity)).le

theorem cap_adverse_upper_log_antitone (u s t : ℝ) (hu : 0 < u) (hu1 : u < 1)
    (hs : 0 < s) (hst : s ≤ t) (ht : t ≤ 6 / 5) :
    capAdverseUpper u t ≤ capAdverseUpper u s := by
  have ht0 := hs.trans_le hst
  have hmargin : 0 ≤ 2 - u - (1 - u) * t := by
    have hm := mul_le_mul_of_nonneg_left ht (sub_pos.mpr hu1).le
    nlinarith only [hm, hu]
  have hfactor : 0 ≤ (2 - u) * (t - s) + 2 * s * (2 - u - (1 - u) * t) := by
    have h2 : 0 ≤ 2 - u := by linarith only [hu1]
    exact add_nonneg (mul_nonneg h2 (sub_nonneg.mpr hst)) (mul_nonneg (by positivity) hmargin)
  have hid : (2 - u - 2 * (1 - u) * s) * (u ^ 2 * (1 - u) * t ^ 2) -
      (2 - u - 2 * (1 - u) * t) * (u ^ 2 * (1 - u) * s ^ 2) =
      u ^ 2 * (1 - u) * (t - s) *
        ((2 - u) * (t - s) + 2 * s * (2 - u - (1 - u) * t)) := by ring
  have hn := mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg u) (sub_pos.mpr hu1).le)
    (sub_nonneg.mpr hst)) hfactor
  unfold capAdverseUpper
  apply (div_le_div_iff₀ (by positivity : 0 < u ^ 2 * (1 - u) * t ^ 2)
    (by positivity : 0 < u ^ 2 * (1 - u) * s ^ 2)).mpr
  linarith only [hid, hn]

end F4Heavy.Analysis
