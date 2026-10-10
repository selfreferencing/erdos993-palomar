module

public import Mathlib

/-!+Closed-interval calculus used in current (22), (28), and (29). These generic
lemmas consume actual first/second HasDerivAt statements and pointwise
curvature inequalities. They do not assume a named unproved cell theorem.+-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance

open Set Real

theorem second_lower_convex {f f' f'' : ℝ → ℝ} {a b M : ℝ}
    (hd : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hdd : ∀ x ∈ Icc a b, HasDerivAt f' (f'' x) x)
    (hM : ∀ x ∈ Icc a b, M ≤ f'' x) :
    ConvexOn ℝ (Icc a b) (fun x => f x - M * x ^ 2 / 2) := by
  have hg : ∀ x ∈ Icc a b,
      HasDerivAt (fun z => f z - M * z ^ 2 / 2) (f' x - M * x) x := by
    intro x hx
    apply ((hd x hx).sub (((hasDerivAt_pow 2 x).const_mul M).div_const 2)).congr_deriv
    (try dsimp) <;> (try simp only [id_eq, Pi.pow_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply]) <;> ring
  have hgp : ∀ x ∈ Icc a b,
      HasDerivAt (fun z => f' z - M * z) (f'' x - M) x := by
    intro x hx
    exact (hdd x hx).fun_sub (hasDerivAt_const_mul M)
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc a b)
    (f' := fun x => f' x - M * x) (f'' := fun x => f'' x - M)
  · intro x hx
    exact (hg x hx).continuousAt.continuousWithinAt
  · intro x hx
    exact (hg x (interior_subset hx)).hasDerivWithinAt
  · intro x hx
    exact (hgp x (interior_subset hx)).hasDerivWithinAt
  · intro x hx
    exact sub_nonneg.mpr (hM x (interior_subset hx))

theorem second_lower_taylor {f f' f'' : ℝ → ℝ} {a b M x x0 : ℝ}
    (hd : ∀ z ∈ Icc a b, HasDerivAt f (f' z) z)
    (hdd : ∀ z ∈ Icc a b, HasDerivAt f' (f'' z) z)
    (hM : ∀ z ∈ Icc a b, M ≤ f'' z)
    (hx : x ∈ Icc a b) (hx0 : x0 ∈ Icc a b) :
    f x0 + f' x0 * (x - x0) + M * (x - x0) ^ 2 / 2 ≤ f x := by
  let g := fun z => f z - M * z ^ 2 / 2
  have hconv : ConvexOn ℝ (Icc a b) g := second_lower_convex hd hdd hM
  have hg0 : HasDerivAt g (f' x0 - M * x0) x0 := by
    apply ((hd x0 hx0).sub (((hasDerivAt_pow 2 x0).const_mul M).div_const 2)).congr_deriv
    (try dsimp) <;> (try simp only [id_eq, Pi.pow_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply]) <;> ring
  rcases lt_trichotomy x0 x with hlt | heq | hgt
  · have hs := hconv.le_slope_of_hasDerivAt hx0 hx hlt hg0
    rw [slope_def_field] at hs
    have hc := (le_div_iff₀ (sub_pos.mpr hlt)).mp hs
    dsimp [g] at hc
    nlinarith only [hc]
  · subst x
    simp
  · have hs := hconv.slope_le_of_hasDerivAt hx hx0 hgt hg0
    rw [slope_def_field] at hs
    have hc := (div_le_iff₀ (sub_pos.mpr hgt)).mp hs
    dsimp [g] at hc
    nlinarith only [hc]

/-- Curvature -k contributes at most k*(b-a)^2/8 above the larger endpoint.
At k=15/32 this is exactly the printed 15/256 activity correction. -/
theorem second_lower_endpoint_upper {f f' f'' : ℝ → ℝ} {a b k x : ℝ}
    (hab : a < b) (hk : 0 ≤ k)
    (hd : ∀ z ∈ Icc a b, HasDerivAt f (f' z) z)
    (hdd : ∀ z ∈ Icc a b, HasDerivAt f' (f'' z) z)
    (hcurv : ∀ z ∈ Icc a b, -k ≤ f'' z)
    (hx : x ∈ Icc a b) :
    f x ≤ max (f a) (f b) + k * (b - a) ^ 2 / 8 := by
  let u := (b - x) / (b - a)
  let v := (x - a) / (b - a)
  have hba : 0 < b - a := sub_pos.mpr hab
  have hu : 0 ≤ u := div_nonneg (by linarith [hx.2]) hba.le
  have hv : 0 ≤ v := div_nonneg (by linarith [hx.1]) hba.le
  have huv : u + v = 1 := by dsimp [u, v]; field_simp [hba.ne'] <;> ring
  have hux : u * a + v * b = x := by dsimp [u, v]; field_simp [hba.ne'] <;> ring
  have hc := second_lower_convex hd hdd hcurv
  have hc' := hc.2 (show a ∈ Icc a b from ⟨le_rfl, hab.le⟩)
    (show b ∈ Icc a b from ⟨hab.le, le_rfl⟩) hu hv huv
  simp only [smul_eq_mul] at hc'
  rw [hux] at hc'
  have hends := add_le_add
    (mul_le_mul_of_nonneg_left (le_max_left (f a) (f b)) hu)
    (mul_le_mul_of_nonneg_left (le_max_right (f a) (f b)) hv)
  have hends' : u * f a + v * f b ≤ max (f a) (f b) := by
    have hsum : u * max (f a) (f b) + v * max (f a) (f b) = max (f a) (f b) := by
      rw [← add_mul, huv, one_mul]
    linarith only [hends, hsum]
  have hquad : u * a ^ 2 + v * b ^ 2 - x ^ 2 = (x - a) * (b - x) := by
    dsimp [u, v]
    (try dsimp) <;> (try simp only [id_eq, Pi.pow_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply]) <;> field_simp [hba.ne'] <;> ring
  have hwidth : (x - a) * (b - x) ≤ (b - a) ^ 2 / 4 := by
    nlinarith [sq_nonneg (2 * x - a - b)]
  have hscaled := mul_le_mul_of_nonneg_left hwidth hk
  have hquadk := congrArg (fun z : ℝ => k * z) hquad
  nlinarith only [hc', hends', hquadk, hscaled]

noncomputable def quadraticLoss (M j w : ℝ) : ℝ :=
  if j ≤ M * w then j ^ 2 / (2 * M) else j * w - M * w ^ 2 / 2

theorem quadraticLoss_bound {M j w r : ℝ}
    (hM : 0 < M) (hj : 0 ≤ j) (hw : 0 ≤ w) (hr : 0 ≤ r) (hrw : r ≤ w) :
    j * r - M * r ^ 2 / 2 ≤ quadraticLoss M j w := by
  unfold quadraticLoss
  split_ifs with hcase
  · apply (le_div_iff₀ (by positivity : 0 < 2 * M)).2
    nlinarith [sq_nonneg (j - M * r)]
  · have hfactor : 0 ≤ (w - r) * (j - M * (w + r) / 2) := by
      apply mul_nonneg (by linarith)
      have hh := mul_le_mul_of_nonneg_left hrw hM.le
      linarith
    nlinarith only [hfactor]

/-- The exact analytic implication behind T_- - Psi on a closed interval.
The basepoint need not be interior; all endpoints use ordinary derivatives. -/
theorem second_lower_cell_value {f f' f'' : ℝ → ℝ} {a b x x0 M j w lower : ℝ}
    (hd : ∀ z ∈ Icc a b, HasDerivAt f (f' z) z)
    (hdd : ∀ z ∈ Icc a b, HasDerivAt f' (f'' z) z)
    (hcurv : ∀ z ∈ Icc a b, M ≤ f'' z)
    (hx : x ∈ Icc a b) (hx0 : x0 ∈ Icc a b)
    (hM : 0 < M) (hj : 0 ≤ j) (hw : 0 ≤ w)
    (hwidth : |x - x0| ≤ w) (hbase : lower ≤ f x0) (hslope : |f' x0| ≤ j) :
    lower - quadraticLoss M j w ≤ f x := by
  have ht := second_lower_taylor hd hdd hcurv hx hx0
  have hprod := neg_abs_le (f' x0 * (x - x0))
  rw [abs_mul] at hprod
  have hsl := mul_le_mul_of_nonneg_right hslope (abs_nonneg (x - x0))
  have hlinear : -j * |x - x0| ≤ f' x0 * (x - x0) := by linarith
  have hq := quadraticLoss_bound hM hj hw (abs_nonneg (x - x0)) hwidth
  rw [sq_abs] at hq
  linarith only [ht, hbase, hlinear, hq]

end Erdos993Lean.Analytic.V213.FreeCountVariance

#check Erdos993Lean.Analytic.V213.FreeCountVariance.second_lower_convex
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.second_lower_convex
#check Erdos993Lean.Analytic.V213.FreeCountVariance.second_lower_taylor
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.second_lower_taylor
#check Erdos993Lean.Analytic.V213.FreeCountVariance.second_lower_endpoint_upper
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.second_lower_endpoint_upper
#check Erdos993Lean.Analytic.V213.FreeCountVariance.quadraticLoss_bound
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.quadraticLoss_bound
#check Erdos993Lean.Analytic.V213.FreeCountVariance.second_lower_cell_value
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.second_lower_cell_value
