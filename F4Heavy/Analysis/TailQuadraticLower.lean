module

public import F4Heavy.Analysis.TailParentMass

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis

theorem tail_derivative_increment (f f' : ℝ → ℝ) (a L : ℝ)
    (hf : ∀ x, a ≤ x → HasDerivAt f (f' x) x)
    (hL : ∀ x, a ≤ x → L ≤ f' x) (x : ℝ) (hx : a ≤ x) :
    f a + L * (x - a) ≤ f x := by
  have hd (y : ℝ) (hy : a ≤ y) : HasDerivAt (fun z => f z - L * z) (f' y - L) y := by
    convert (hf y hy).sub ((hasDerivAt_id y).const_mul L) using 1
    · rfl
    · simp
  have hm : MonotoneOn (fun y => f y - L * y) (Set.Ici a) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici a)
    · intro y hy
      exact (hd y hy).continuousAt.continuousWithinAt
    · intro y hy
      exact (hd y (interior_subset hy)).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [(hd y (interior_subset hy)).deriv]
      exact sub_nonneg.mpr (hL y (interior_subset hy))
  have h := hm (show a ∈ Set.Ici a from le_rfl) hx hx
  dsimp only at h
  linarith only [h]

theorem tail_quadratic_lower (f f' f'' : ℝ → ℝ) (a L : ℝ)
    (hf : ∀ x, a ≤ x → HasDerivAt f (f' x) x)
    (hf' : ∀ x, a ≤ x → HasDerivAt f' (f'' x) x)
    (hL : ∀ x, a ≤ x → L ≤ f'' x) (x : ℝ) (hx : a ≤ x) :
    f a + f' a * (x - a) + L / 2 * (x - a) ^ 2 ≤ f x := by
  have hs : ∀ y, a ≤ y → f' a + L * (y - a) ≤ f' y :=
    fun y hy => tail_derivative_increment f' f'' a L hf' hL y hy
  let g := fun y => f y - f' a * (y - a) - L / 2 * (y - a) ^ 2
  let g' := fun y => f' y - f' a - L * (y - a)
  have hg (y : ℝ) (hy : a ≤ y) : HasDerivAt g (g' y) y := by
    have hi := (hasDerivAt_id y).sub_const a
    convert ((hf y hy).sub (hi.const_mul (f' a))).sub ((hi.pow 2).const_mul (L / 2)) using 1
    · rfl
    · dsimp [g']
      ring
  have h := tail_derivative_increment g g' a 0 hg
    (fun y hy => by dsimp [g']; linarith only [hs y hy]) x hx
  dsimp [g] at h
  nlinarith only [h]

theorem tail_curvature_drop_bound (f f' f'' : ℝ → ℝ) (a L eta : ℝ)
    (hf : ∀ x, a ≤ x → HasDerivAt f (f' x) x)
    (hf' : ∀ x, a ≤ x → HasDerivAt f' (f'' x) x)
    (hL : ∀ x, a ≤ x → L ≤ f'' x) (hL0 : 0 < L)
    (hslope : -eta ≤ f' a) (x : ℝ) (hx : a ≤ x) :
    f a - eta ^ 2 / (2 * L) ≤ f x := by
  have hq := tail_quadratic_lower f f' f'' a L hf hf' hL x hx
  have hs := mul_le_mul_of_nonneg_right hslope (sub_nonneg.mpr hx)
  have hid : L / 2 * (x - a) ^ 2 - eta * (x - a) + eta ^ 2 / (2 * L) =
      (L * (x - a) - eta) ^ 2 / (2 * L) := by field_simp <;> ring
  have hsq : 0 ≤ L / 2 * (x - a) ^ 2 - eta * (x - a) + eta ^ 2 / (2 * L) := by
    rw [hid]
    exact div_nonneg (sq_nonneg _) (by positivity)
  linarith only [hq, hs, hsq]

end F4Heavy.Analysis
