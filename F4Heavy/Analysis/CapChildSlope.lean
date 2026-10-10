module

public import F4Heavy.Analysis.ChildCurve

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem cap_childH_derivative_half (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) :
    deriv childH u ≤ -(1 / 2) := by
  have hp := phi_positive u hu0 hu1
  have he : Real.exp (phi u) = 1 / (1 - u) := by
    rw [phi_eq_negative_log, Real.exp_neg, Real.exp_log (sub_pos.mpr hu1)]
    simp only [one_div]
  have hquad := Real.quadratic_le_exp_of_nonneg hp.le
  rw [he] at hquad
  have hid : -childCurveW u / ((1 - u) * phi u) =
      -(1 / (1 - u) - 1 - phi u) / (phi u) ^ 2 := by
    unfold childCurveW childH
    rw [if_neg (ne_of_gt hu0)]
    field_simp [ne_of_gt hp, ne_of_gt (sub_pos.mpr hu1)]
    <;> ring
  rw [(childH_derivative u hu0 hu1).deriv, hid]
  apply (div_le_iff₀ (sq_pos_of_pos hp)).mpr
  linarith only [hquad]

theorem cap_childH_shift_antitone :
    AntitoneOn (fun u : ℝ => childH u + u / 2) (Set.Ioo 0 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioo 0 1)
  · intro u hu
    exact ((childH_derivative u hu.1 hu.2).add
      ((hasDerivAt_id u).div_const 2)).continuousAt.continuousWithinAt
  · intro u hu
    have hu' : 0 < u ∧ u < 1 := by simpa only [interior_Ioo, Set.mem_Ioo] using hu
    exact ((childH_derivative u hu'.1 hu'.2).add
      ((hasDerivAt_id u).div_const 2)).differentiableAt.differentiableWithinAt
  · intro u hu
    have hu' : 0 < u ∧ u < 1 := by simpa only [interior_Ioo, Set.mem_Ioo] using hu
    change deriv (childH + fun x : ℝ => id x / 2) u ≤ 0
    rw [((childH_derivative u hu'.1 hu'.2).add ((hasDerivAt_id u).div_const 2)).deriv]
    have hd := cap_childH_derivative_half u hu'.1 hu'.2
    rw [(childH_derivative u hu'.1 hu'.2).deriv] at hd
    linarith only [hd]

/-- Includes the original forced child endpoint, without taking a reserve limit. -/
theorem cap_childH_height_increment (u v : ℝ) (hu : 0 ≤ u) (huv : u ≤ v) (hv : v < 1) :
    (v - u) / 2 ≤ childH u - childH v := by
  by_cases hz : u = 0
  · subst u
    rw [show childH 0 = 1 by simp [childH]]
    have h' := childH_linear_upper v (hu.trans huv) hv
    linarith only [h']
  · have hup : 0 < u := lt_of_le_of_ne hu (Ne.symm hz)
    have h := cap_childH_shift_antitone ⟨hup, huv.trans_lt hv⟩ ⟨hup.trans_le huv, hv⟩ huv
    dsimp only at h
    linarith only [h]

end F4Heavy.Analysis
