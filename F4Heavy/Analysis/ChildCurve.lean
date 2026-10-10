module

public import F4Heavy.Analysis.ChildMass

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified
open scoped Topology

noncomputable def childCurveA (u : ℝ) : ℝ := 2*(1-u)^2*phi u+3*u^2-2*u
noncomputable def childCurveB (u : ℝ) : ℝ := 3*u-(3-2*u)*phi u
noncomputable def childCurveW (u : ℝ) : ℝ := childH u-1+u
noncomputable def childCurveT (e u : ℝ) : ℝ := Real.log (e*(1-u)/u)
noncomputable def childCurveV (e u : ℝ) : ℝ :=
  u*(1+(childH u-2*(1-u))*childCurveT e u)/childCurveW u

theorem childCurveA_derivative (u : ℝ) (hu1 : u < 1) :
    HasDerivAt childCurveA (4*(u-(1-u)*phi u)) u := by
  have hid := hasDerivAt_id u
  have hp := phi_derivative u hu1
  have h := ((((hid.const_sub 1).pow 2).const_mul 2).mul hp).add
    ((hid.pow 2).const_mul 3) |>.sub (hid.const_mul 2)
  convert h using 1
  · rfl
  · dsimp
    field_simp [ne_of_gt (sub_pos.mpr hu1)]
    ring

theorem childCurveA_nonnegative (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    0 ≤ childCurveA u := by
  have hm : MonotoneOn childCurveA (Set.Ico 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ico 0 1)
    · intro x hx
      exact (childCurveA_derivative x hx.2).continuousAt.continuousWithinAt
    · intro x hx
      have hx' : 0 < x ∧ x < 1 := by simpa only [interior_Ico, Set.mem_Ioo] using hx
      exact (childCurveA_derivative x hx'.2).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : 0 < x ∧ x < 1 := by simpa only [interior_Ico, Set.mem_Ioo] using hx
      rw [(childCurveA_derivative x hx'.2).deriv]
      exact mul_nonneg (by norm_num) (child_mass_D_positive x hx'.1 hx'.2).le
  have h := hm (show (0 : ℝ) ∈ Set.Ico 0 1 by norm_num) ⟨hu0, hu1⟩ hu0
  simpa [childCurveA, phi] using h

theorem childH_derivative (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) :
    HasDerivAt childH (-childCurveW u/((1-u)*phi u)) u := by
  have hp := phi_positive u hu0 hu1
  have h := (hasDerivAt_id u).div (phi_derivative u hu1) (ne_of_gt hp)
  have heq : childH =ᶠ[𝓝 u] (fun x => x/phi x) := by
    filter_upwards [eventually_ne_nhds (ne_of_gt hu0)] with x hx
    simp [childH, hx]
  have h' := h.congr_of_eventuallyEq heq
  convert h' using 1
  dsimp [childCurveW, childH]
  rw [if_neg (ne_of_gt hu0)]
  field_simp [ne_of_gt hp, ne_of_gt (sub_pos.mpr hu1)]
  ring

theorem childH_derivative_negative (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) :
    deriv childH u < 0 := by
  rw [(childH_derivative u hu0 hu1).deriv]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (child_w_bounds u hu0 hu1).1)
    (mul_pos (sub_pos.mpr hu1) (phi_positive u hu0 hu1))

theorem childCurveT_derivative (e u : ℝ) (he : 0 < e) (hu0 : 0 < u) (hu1 : u < 1) :
    HasDerivAt (childCurveT e) (-1/(u*(1-u))) u := by
  have hid := hasDerivAt_id u
  have hg := ((hid.const_sub 1).const_mul e).div hid (ne_of_gt hu0)
  have h := hg.log (ne_of_gt (div_pos (mul_pos he (sub_pos.mpr hu1)) hu0))
  convert h using 1
  · rfl
  · dsimp
    field_simp [ne_of_gt he, ne_of_gt hu0, ne_of_gt (sub_pos.mpr hu1)]
    ring

theorem childJ_derivative (e u : ℝ) (he : 0 < e) (hu0 : 0 < u) (hu1 : u < 1) :
    HasDerivAt (childJ e)
      ((-childCurveW u/((1-u)*phi u))*childCurveV e u) u := by
  have hh := childH_derivative u hu0 hu1
  have ht := childCurveT_derivative e u he hu0 hu1
  have h := ((hasDerivAt_id u).mul hh).mul ht
  have heq : childJ e =ᶠ[𝓝 u] (fun x => x*childH x*childCurveT e x) := by
    filter_upwards [eventually_ne_nhds (ne_of_gt hu0)] with x hx
    simp [childJ, childCurveT, hx]
  have h' := h.congr_of_eventuallyEq heq
  convert h' using 1
  have hp := ne_of_gt (phi_positive u hu0 hu1)
  have hw : childCurveW u ≠ 0 := ne_of_gt (child_w_bounds u hu0 hu1).1
  dsimp only [childCurveV]
  field_simp [hp, hw, ne_of_gt hu0, ne_of_gt (sub_pos.mpr hu1)]
  dsimp [childCurveW, childH]
  rw [if_neg (ne_of_gt hu0)]
  field_simp [hp]
  ring

theorem childCurveV_derivative (e u : ℝ) (he : 0 < e) (hu0 : 0 < u) (hu1 : u < 1) :
    HasDerivAt (childCurveV e)
      ((childCurveA u*childCurveT e u+childCurveB u)/(phi u*(childCurveW u)^2)) u := by
  have hid := hasDerivAt_id u
  have hh := childH_derivative u hu0 hu1
  have ht := childCurveT_derivative e u he hu0 hu1
  have hn := hid.mul (((hh.sub ((hid.const_sub 1).const_mul 2)).mul ht).const_add 1)
  have hd := (hh.sub_const 1).add hid
  have hp := ne_of_gt (phi_positive u hu0 hu1)
  have hw : childCurveW u ≠ 0 := ne_of_gt (child_w_bounds u hu0 hu1).1
  have h := hn.div hd hw
  convert h using 1
  · rfl
  · dsimp only [id_eq]
    change (childCurveA u*childCurveT e u+childCurveB u)/(phi u*(childCurveW u)^2) = _
    change _ = ((1*(1+(childH u-2*(1-u))*childCurveT e u)+
      u*((-childCurveW u/((1-u)*phi u)-2*(-1))*childCurveT e u+
        (childH u-2*(1-u))*(-1/(u*(1-u)))))*childCurveW u-
      (u*(1+(childH u-2*(1-u))*childCurveT e u))*(-childCurveW u/((1-u)*phi u)+1)) /
      (childCurveW u)^2
    field_simp [hp, hw, ne_of_gt hu0, ne_of_gt (sub_pos.mpr hu1)]
    dsimp [childCurveA, childCurveB, childCurveW, childH]
    rw [if_neg (ne_of_gt hu0)]
    field_simp [hp]
    ring

end F4Heavy.Analysis
