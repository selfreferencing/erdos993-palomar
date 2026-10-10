module

public import F4Heavy.Analysis.CapDomain
public import F4Heavy.Analysis.ParentBounds

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem cap_phi_upper_remainder_derivative (u : ℝ) (hu : u < 1) :
    HasDerivAt (fun x => x * (2 - x) / (2 * (1 - x)) - phi x)
      (u ^ 2 / (2 * (1 - u) ^ 2)) u := by
  have hid := hasDerivAt_id u
  have hd : 2 * (1 - u) ≠ 0 := by positivity
  have h := ((hid.mul (hid.const_sub 2)).div ((hid.const_sub 1).const_mul 2) hd).sub
    (phi_derivative u hu)
  convert h using 1
  · rfl
  · dsimp
    field_simp [ne_of_gt (sub_pos.mpr hu)]
    <;> ring

theorem cap_phi_quadratic_upper (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    phi u ≤ u * (2 - u) / (2 * (1 - u)) := by
  have hm : MonotoneOn (fun x => x * (2 - x) / (2 * (1 - x)) - phi x) (Set.Iio 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Iio 1)
    · intro x hx
      exact (cap_phi_upper_remainder_derivative x hx).continuousAt.continuousWithinAt
    · intro x hx
      have hx' : x < 1 := by simpa only [interior_Iio, Set.mem_Iio] using hx
      exact (cap_phi_upper_remainder_derivative x hx').differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : x < 1 := by simpa only [interior_Iio, Set.mem_Iio] using hx
      rw [(cap_phi_upper_remainder_derivative x hx').deriv]
      positivity
  have h := hm (show (0 : ℝ) ∈ Set.Iio 1 by norm_num) hu1 hu0
  dsimp only at h
  rw [show phi 0 = 0 by simp [phi]] at h
  simp only [zero_mul, zero_div, sub_zero] at h
  linarith only [h]

theorem cap_childH_rational_lower (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    2 * (1 - u) / (2 - u) ≤ childH u := by
  by_cases hz : u = 0
  · subst u
    norm_num [childH]
  · have hu : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hz)
    have hp := phi_positive u hu hu1
    have hb := (le_div_iff₀ (show 0 < 2 * (1 - u) by positivity)).mp
      (cap_phi_quadratic_upper u hu0 hu1)
    simp only [childH, if_neg hz]
    apply (div_le_div_iff₀ (show 0 < 2 - u by linarith) hp).mpr
    nlinarith only [hb]

theorem cap_child_height_activity_lower (lam Y u : ℝ) (hlam : 0 < lam)
    (hu : 0 ≤ u) (huc : u ≤ capChild lam Y) :
    2 * (lam + 2) / (3 * lam + 4) ≤ childH u := by
  have hu1 := huc.trans_lt (cap_child_lt_one lam Y hlam)
  have hbound : u ≤ q lam / 2 := huc.trans (min_le_right _ _)
  have hmul : u * (2 * (1 + lam)) ≤ lam := by
    have h : u * 2 ≤ lam / (1 + lam) := (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mp hbound
    have h' := (le_div_iff₀ (show 0 < 1 + lam by linarith)).mp h
    nlinarith only [h']
  apply le_trans _ (cap_childH_rational_lower u hu hu1)
  apply (div_le_div_iff₀ (show 0 < 3 * lam + 4 by linarith) (show 0 < 2 - u by linarith)).mpr
  nlinarith only [hmul]

theorem cap_parent_complement_lower (lam Y rho : ℝ) (hlam : 0 < lam)
    (hY : 0 ≤ Y) (hrho : FeasibleVacancy lam Y rho) :
    1 / (1 + 2 * lam) ≤ rho * (1 - p lam Y) := by
  have hp1 := p_lt_one lam Y hlam
  have hq := p_le_q lam Y hlam hY
  have hmul : p lam Y * (1 + lam) ≤ lam :=
    (le_div_iff₀ (show 0 < 1 + lam by linarith)).mp hq
  have hd : 0 < 1 + lam * (1 - p lam Y) := by positivity
  have hfirst : 1 / (1 + 2 * lam) ≤ (1 - p lam Y) / (1 + lam * (1 - p lam Y)) := by
    apply (div_le_div_iff₀ (show 0 < 1 + 2 * lam by linarith) hd).mpr
    nlinarith only [hmul]
  have hsecond := mul_le_mul_of_nonneg_right hrho.1 (sub_nonneg.mpr hp1.le)
  change 1 / (1 + lam * (1 - p lam Y)) * (1 - p lam Y) ≤ rho * (1 - p lam Y) at hsecond
  have hid : 1 / (1 + lam * (1 - p lam Y)) * (1 - p lam Y) =
      (1 - p lam Y) / (1 + lam * (1 - p lam Y)) := by ring
  rw [hid] at hsecond
  exact hfirst.trans hsecond

theorem cap_parent_log_ratio_lower (lam Y : ℝ) (hlam : 0 < lam) (hY : 0 ≤ Y) :
    2 / (2 + lam) ≤ p lam Y / (-Real.log (1 - p lam Y)) := by
  have hp := p_pos lam Y hlam
  have hp1 := p_lt_one lam Y hlam
  have hq := p_le_q lam Y hlam hY
  have hmul : p lam Y * (1 + lam) ≤ lam :=
    (le_div_iff₀ (show 0 < 1 + lam by linarith)).mp hq
  have hbase : 2 / (2 + lam) ≤ 2 * (1 - p lam Y) / (2 - p lam Y) := by
    apply (div_le_div_iff₀ (show 0 < 2 + lam by linarith) (show 0 < 2 - p lam Y by linarith)).mpr
    nlinarith only [hmul]
  have h := hbase.trans (cap_childH_rational_lower (p lam Y) hp.le hp1)
  simpa only [childH, phi, if_neg (ne_of_gt hp)] using h

theorem cap_parentP_lower (r : Row) (lam Y rho : ℝ) (hr : InRow r lam)
    (hY : 0 ≤ Y) (hrho : FeasibleVacancy lam Y rho) :
    1 / (1 + 2 * lam) + 2 * gamma r lam / (2 + lam) ≤ parentP r lam Y rho := by
  have hl := inRow_activity_pos r lam hr
  have h1 := cap_parent_complement_lower lam Y rho hl hY hrho
  have h2 := mul_le_mul_of_nonneg_left (cap_parent_log_ratio_lower lam Y hl hY) (row_gamma_pos r lam hr).le
  unfold parentP
  convert add_le_add h1 h2 using 1 <;> ring

theorem cap_parentP_upper (r : Row) (lam Y rho : ℝ) (hr : InRow r lam)
    (hH : parentH Y ≤ q lam) (hrho : FeasibleVacancy lam Y rho) :
    parentP r lam Y rho ≤ 1 - lam / (1 + 2 * lam) +
      gamma r lam * (1 - (lam / (1 + 2 * lam)) / 2) := by
  have hl := inRow_activity_pos r lam hr
  have hp := cap_parent_probability_lower lam Y hl hH
  have hp1 := p_lt_one lam Y hl
  have h1 := parentP_linear_upper r lam Y rho hr
  have h2 := mul_le_mul_of_nonneg_right hrho.2 (sub_nonneg.mpr hp1.le)
  have h3 := mul_le_mul_of_nonneg_left (show 1 - p lam Y / 2 ≤ 1 - (lam / (1 + 2 * lam)) / 2 by linarith only [hp])
    (row_gamma_pos r lam hr).le
  linarith only [h1, h2, h3, hp]

end F4Heavy.Analysis
