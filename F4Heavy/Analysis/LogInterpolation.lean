module

public import F4Heavy.Analysis.ActivityEnclosure
public import Mathlib.Analysis.Convex.Deriv

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis

theorem log_quadratic_correction_derivative (a x : ℝ) (ha : 0 < a) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => Real.log y+y^2/(2*a^2)) (x⁻¹+x/a^2) x := by
  have hp : HasDerivAt (fun y : ℝ => y^2/(2*a^2)) ((2*x)/(2*a^2)) x := by
    simpa using ((hasDerivAt_id x).pow 2).div_const (2*a^2)
  have hc : (2*x)/(2*a^2) = x/a^2 := by field_simp
  rw [hc] at hp
  exact (Real.hasDerivAt_log (ne_of_gt hx)).add hp

theorem log_quadratic_correction_convex (a : ℝ) (ha : 0 < a) :
    ConvexOn ℝ (Set.Ici a) (fun x : ℝ => Real.log x+x^2/(2*a^2)) := by
  apply MonotoneOn.convexOn_of_deriv (convex_Ici a)
  · intro x hx
    exact (log_quadratic_correction_derivative a x ha (ha.trans_le hx)).continuousAt.continuousWithinAt
  · intro x hx
    have hax : a < x := by simpa only [interior_Ici, Set.mem_Ioi] using hx
    exact (log_quadratic_correction_derivative a x ha (ha.trans hax)).differentiableAt.differentiableWithinAt
  · intro x hx y hy hxy
    have hax : a < x := by simpa only [interior_Ici, Set.mem_Ioi] using hx
    have hay : a < y := by simpa only [interior_Ici, Set.mem_Ioi] using hy
    have hx0 := ha.trans hax
    have hy0 := ha.trans hay
    rw [(log_quadratic_correction_derivative a x ha hx0).deriv,
      (log_quadratic_correction_derivative a y ha hy0).deriv]
    have hsq : a^2 ≤ x*y := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr hax.le) (sub_nonneg.mpr hay.le),
        mul_nonneg ha.le (sub_nonneg.mpr hax.le), mul_nonneg ha.le (sub_nonneg.mpr hay.le)]
    have hinv : 1/(x*y) ≤ 1/a^2 :=
      div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos ha) hsq
    have hnonneg := mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hinv)
    have heq : (y⁻¹+y/a^2)-(x⁻¹+x/a^2) = (y-x)*(1/a^2-1/(x*y)) := by
      field_simp
      ring
    linarith only [heq, hnonneg]

theorem log_chord_quadratic_upper (a b t : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.log ((1-t)*a+t*b) ≤ (1-t)*Real.log a+t*Real.log b+
      t*(1-t)*(b-a)^2/(2*a^2) := by
  have hc := (log_quadratic_correction_convex a ha).2
    (show a ∈ Set.Ici a from le_refl a) (show b ∈ Set.Ici a from hab)
    (sub_nonneg.mpr ht1) ht0 (by ring : 1-t+t=1)
  simp only [smul_eq_mul] at hc
  have heq : (1-t)*(a^2/(2*a^2))+t*(b^2/(2*a^2))-
      ((1-t)*a+t*b)^2/(2*a^2) = t*(1-t)*(b-a)^2/(2*a^2) := by
    ring
  linarith only [hc, heq]

theorem log_chord_uniform_upper (a b t : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.log ((1-t)*a+t*b) ≤ (1-t)*Real.log a+t*Real.log b+(b-a)^2/(8*a^2) := by
  have h := log_chord_quadratic_upper a b t ha hab ht0 ht1
  have ht : t*(1-t) ≤ 1/4 := by nlinarith only [sq_nonneg (t-1/2)]
  have hb := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ht (sq_nonneg (b-a)))
    (by positivity : 0 ≤ 2*a^2)
  have heq : ((1/4)*(b-a)^2)/(2*a^2) = (b-a)^2/(8*a^2) := by ring
  rw [heq] at hb
  linarith only [h, hb]

end F4Heavy.Analysis
