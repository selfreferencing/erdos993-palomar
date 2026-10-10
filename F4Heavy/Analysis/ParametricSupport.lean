module

public import F4Heavy.Analysis.LogInterpolation

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis

theorem parametric_quadratic_support {D : Set ℝ} (hD : Convex ℝ D)
    (h j v dh : ℝ → ℝ) (k u c : ℝ) (hu : u ∈ D) (hc : c ∈ D)
    (hh : ∀ x ∈ D, HasDerivAt h (dh x) x)
    (hj : ∀ x ∈ D, HasDerivAt j (dh x*v x) x)
    (hdh : ∀ x ∈ D, dh x ≤ 0)
    (hmono : MonotoneOn (fun x => v x+k*h x) D) :
    j u ≤ j c+v c*(h u-h c)-k/2*(h u-h c)^2 := by
  let F := fun x => j x-v c*(h x-h c)+k/2*(h x-h c)^2
  have hF : ∀ x ∈ D, HasDerivAt F (dh x*(v x-v c+k*(h x-h c))) x := by
    intro x hx
    have hhx := (hh x hx).sub_const (h c)
    have hf := ((hj x hx).sub (hhx.const_mul (v c))).add ((hhx.pow 2).const_mul (k/2))
    convert hf using 1
    dsimp
    ring
  have hmax : F u ≤ F c := by
    rcases le_total u c with huc | hcu
    · have hsub : Set.Icc u c ⊆ D := hD.ordConnected.out hu hc
      have hm : MonotoneOn F (Set.Icc u c) := by
        apply monotoneOn_of_deriv_nonneg (convex_Icc u c)
        · intro x hx
          exact (hF x (hsub hx)).continuousAt.continuousWithinAt
        · intro x hx
          exact (hF x (hsub (interior_subset hx))).differentiableAt.differentiableWithinAt
        · intro x hx
          have hx' := interior_subset hx
          have hxD := hsub hx'
          rw [(hF x hxD).deriv]
          have hm := hmono hxD hc hx'.2
          exact mul_nonneg_of_nonpos_of_nonpos (hdh x hxD) (by linarith only [hm])
      exact hm ⟨le_refl u, huc⟩ ⟨huc, le_refl c⟩ huc
    · have hsub : Set.Icc c u ⊆ D := hD.ordConnected.out hc hu
      have hm : AntitoneOn F (Set.Icc c u) := by
        apply antitoneOn_of_deriv_nonpos (convex_Icc c u)
        · intro x hx
          exact (hF x (hsub hx)).continuousAt.continuousWithinAt
        · intro x hx
          exact (hF x (hsub (interior_subset hx))).differentiableAt.differentiableWithinAt
        · intro x hx
          have hx' := interior_subset hx
          have hxD := hsub hx'
          rw [(hF x hxD).deriv]
          have hm := hmono hc hxD hx'.1
          exact mul_nonpos_of_nonpos_of_nonneg (hdh x hxD) (by linarith only [hm])
      exact hm ⟨le_refl c, hcu⟩ ⟨hcu, le_refl u⟩ hcu
  dsimp [F] at hmax
  nlinarith only [hmax]

theorem quadratic_support_line (J h Jc hc v k s c : ℝ) (hk : 0 < k)
    (hquad : J ≤ Jc+v*(h-hc)-k/2*(h-hc)^2)
    (hcontact : Jc-s*hc+(v-s)^2/(2*k) ≤ c) : J ≤ s*h+c := by
  have hid : (Jc-s*hc+(v-s)^2/(2*k))-
      (Jc+v*(h-hc)-k/2*(h-hc)^2-s*h) =
      (k*(h-hc)-(v-s))^2/(2*k) := by
    field_simp
    ring
  have hp : 0 ≤ (k*(h-hc)-(v-s))^2/(2*k) := by positivity
  linarith only [hquad, hcontact, hid, hp]

end F4Heavy.Analysis
