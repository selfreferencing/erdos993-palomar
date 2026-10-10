module

public import F4Heavy.Analysis.ChildActivity

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

noncomputable def childMassUpper (u : ℝ) : ℝ :=
  u*(u^2-12*u+12)/(6*(1-u)*(2-u))

theorem phi_eq_negative_log (u : ℝ) : phi u = -Real.log (1-u) := by
  by_cases h : u = 0
  · simp [phi, h]
  · simp [phi, h]

theorem phi_derivative (u : ℝ) (hu : u < 1) :
    HasDerivAt phi (1/(1-u)) u := by
  have h := ((hasDerivAt_id u).const_sub 1).log (ne_of_gt (sub_pos.mpr hu))
  convert h.neg using 1
  · ext x
    exact phi_eq_negative_log x
  · dsimp
    ring

theorem childMassUpper_remainder_derivative (u : ℝ) (hu : u < 1) :
    HasDerivAt (fun x => childMassUpper x-phi x)
      (u^4/(6*(1-u)^2*(2-u)^2)) u := by
  have hid := hasDerivAt_id u
  have hn := hid.mul (((hid.pow 2).sub (hid.const_mul 12)).add_const 12)
  have hd := (((hid.const_sub 1).const_mul 6).mul (hid.const_sub 2))
  have h1 : 1-u ≠ 0 := ne_of_gt (by linarith : 0 < 1-u)
  have h2 : 2-u ≠ 0 := ne_of_gt (by linarith : 0 < 2-u)
  have hd0 : 6*(1-u)*(2-u) ≠ 0 := by
    have h1 : 0 < 1-u := by linarith
    have h2 : 0 < 2-u := by linarith
    positivity
  have h := (hn.div hd hd0).sub (phi_derivative u hu)
  convert h using 1
  · rfl
  · dsimp
    field_simp [h1, h2]
    ring

theorem childMassUpper_remainder_monotone :
    MonotoneOn (fun u => childMassUpper u-phi u) (Set.Iio 1) := by
  apply monotoneOn_of_deriv_nonneg (convex_Iio 1)
  · intro u hu
    exact (childMassUpper_remainder_derivative u hu).continuousAt.continuousWithinAt
  · intro u hu
    have hu' : u < 1 := by simpa only [interior_Iio, Set.mem_Iio] using hu
    exact (childMassUpper_remainder_derivative u hu').differentiableAt.differentiableWithinAt
  · intro u hu
    have hu' : u < 1 := by simpa only [interior_Iio, Set.mem_Iio] using hu
    rw [(childMassUpper_remainder_derivative u hu').deriv]
    positivity

theorem phi_rational_upper (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    phi u ≤ childMassUpper u := by
  have h := childMassUpper_remainder_monotone (show (0 : ℝ) ∈ Set.Iio 1 by norm_num) hu1 hu0
  have hz : childMassUpper 0-phi 0 = 0 := by simp [childMassUpper, phi]
  dsimp only at h
  rw [hz] at h
  linarith only [h]

theorem phi_positive (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) : 0 < phi u := by
  rw [phi_eq_negative_log]
  have h := Real.log_le_sub_one_of_pos (sub_pos.mpr hu1)
  linarith only [h, hu0]

theorem childMassUpper_strict (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) :
    childMassUpper u < u/(1-u) := by
  have h1 : 0 < 1-u := by linarith
  have h2 : 0 < 2-u := by linarith
  have heq : u/(1-u)-childMassUpper u = u^2*(6-u)/(6*(1-u)*(2-u)) := by
    unfold childMassUpper
    field_simp
    ring
  have hp : 0 < u^2*(6-u)/(6*(1-u)*(2-u)) := by
    have h6 : 0 < 6-u := by linarith
    positivity
  linarith only [heq, hp]

theorem child_mass_D_positive (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) :
    0 < u-(1-u)*phi u := by
  have h := (phi_rational_upper u hu0.le hu1).trans_lt (childMassUpper_strict u hu0 hu1)
  have hm := (lt_div_iff₀ (sub_pos.mpr hu1)).mp h
  nlinarith only [hm]

theorem child_w_bounds (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) :
    0 < childH u-1+u ∧ childH u-1+u ≤ u/2 := by
  have hphi := phi_positive u hu0 hu1
  have hd := child_mass_D_positive u hu0 hu1
  have heq : childH u-1+u = (u-(1-u)*phi u)/phi u := by
    simp only [childH, if_neg (ne_of_gt hu0)]
    field_simp
    ring
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact div_pos hd hphi
  · have h := childH_linear_upper u hu0.le hu1
    linarith only [h]

end F4Heavy.Analysis
