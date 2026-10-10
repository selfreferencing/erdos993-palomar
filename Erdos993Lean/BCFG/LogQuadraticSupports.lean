module

public import Mathlib

/-! Quadratic log supports. The proof uses actual derivatives
and closed-interval monotonicity, with no assumed Taylor remainder bound. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Erdos993Lean.BCFG.Analytic

open Set

/-- A continuous differentiable function whose derivative points away from c
has its minimum there, including both endpoints of the closed interval. -/
theorem minimum_at_of_derivative_sign {f df : ℝ → ℝ} {a b c x : ℝ}
    (hc : c ∈ Icc a b) (hx : x ∈ Icc a b)
    (hd : ∀ y ∈ Icc a b, HasDerivAt f (df y) y)
    (hleft : ∀ y ∈ Icc a b, y ≤ c → df y ≤ 0)
    (hright : ∀ y ∈ Icc a b, c ≤ y → 0 ≤ df y) : f c ≤ f x := by
  by_cases hxc : x ≤ c
  · have hm : AntitoneOn f (Icc a c) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a c)
      · intro y hy
        exact (hd y ⟨hy.1, hy.2.trans hc.2⟩).continuousAt.continuousWithinAt
      · intro y hy
        have hy' : y ∈ Icc a c := interior_subset hy
        exact (hd y ⟨hy'.1, hy'.2.trans hc.2⟩).hasDerivWithinAt
      · intro y hy
        have hy' : y ∈ Icc a c := interior_subset hy
        exact hleft y ⟨hy'.1, hy'.2.trans hc.2⟩ hy'.2
    exact hm ⟨hx.1, hxc⟩ ⟨hc.1, le_rfl⟩ hxc
  · have hcx : c ≤ x := le_of_not_ge hxc
    have hm : MonotoneOn f (Icc c b) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc c b)
      · intro y hy
        exact (hd y ⟨hc.1.trans hy.1, hy.2⟩).continuousAt.continuousWithinAt
      · intro y hy
        have hy' : y ∈ Icc c b := interior_subset hy
        exact (hd y ⟨hc.1.trans hy'.1, hy'.2⟩).hasDerivWithinAt
      · intro y hy
        have hy' : y ∈ Icc c b := interior_subset hy
        exact hright y ⟨hc.1.trans hy'.1, hy'.2⟩ hy'.1
    exact hm ⟨le_rfl, hc.2⟩ ⟨hcx, hx.2⟩ hcx

def logQuadraticGap (d c x : ℝ) : ℝ :=
  Real.log (1+x)-(x-c)/(1+c)+(x-c)^2/(2*(1+d)^2)

theorem logQuadraticGap_hasDerivAt {d c x : ℝ}
    (hd : 0 < 1+d) (hc : 0 < 1+c) (hx : 0 < 1+x) :
    HasDerivAt (logQuadraticGap d c)
      ((x-c)*(1/(1+d)^2-1/((1+x)*(1+c)))) x := by
  have hlog := ((hasDerivAt_id x).const_add 1).log hx.ne'
  have hlin := ((hasDerivAt_id x).sub_const c).div_const (1+c)
  have hquad := (((hasDerivAt_id x).sub_const c).pow 2).div_const (2*(1+d)^2)
  have h := (hlog.sub hlin).add hquad
  unfold logQuadraticGap
  convert h using 1 <;>
    (try funext y) <;>
    (try dsimp) <;>
    norm_num only [Nat.reduceSub, pow_one, mul_one, Nat.cast_ofNat] <;>
    field_simp [hd.ne', hc.ne', hx.ne'] <;> ring

theorem lower_log_gap_coefficient_nonneg {a c y : ℝ}
    (ha : 0 < 1+a) (hac : a ≤ c) (hay : a ≤ y) :
    0 ≤ 1/(1+a)^2-1/((1+y)*(1+c)) := by
  have hc : 0 < 1+c := by linarith
  have hprod : (1+a)^2 ≤ (1+y)*(1+c) := by
    have h1 := mul_nonneg (show 0 ≤ y-a by linarith) hc.le
    have h2 := mul_nonneg (show 0 ≤ c-a by linarith) ha.le
    nlinarith
  exact sub_nonneg.mpr (one_div_le_one_div_of_le (sq_pos_of_pos ha) hprod)

theorem upper_log_gap_coefficient_nonneg {b c y : ℝ}
    (hc : 0 < 1+c) (hy : 0 < 1+y) (hcb : c ≤ b) (hyb : y ≤ b) :
    0 ≤ 1/((1+y)*(1+c))-1/(1+b)^2 := by
  have hb : 0 < 1+b := by linarith
  have hprod : (1+y)*(1+c) ≤ (1+b)^2 := by
    have h1 := mul_nonneg (show 0 ≤ b-y by linarith) hb.le
    have h2 := mul_nonneg (show 0 ≤ b-c by linarith) hy.le
    nlinarith
  exact sub_nonneg.mpr (one_div_le_one_div_of_le (mul_pos hy hc) hprod)

/-- The exact lower quadratic support throughout a closed interval. -/
theorem log_quadratic_lower {a b c x : ℝ} (ha : 0 < 1+a)
    (hc : c ∈ Icc a b) (hx : x ∈ Icc a b) :
    Real.log (1+c)+(x-c)/(1+c)-(x-c)^2/(2*(1+a)^2) ≤ Real.log (1+x) := by
  have hcpos : 0 < 1+c := by linarith [hc.1]
  have h := minimum_at_of_derivative_sign
    (f := logQuadraticGap a c)
    (df := fun y => (y-c)*(1/(1+a)^2-1/((1+y)*(1+c)))) hc hx
    (by
      intro y hy
      exact logQuadraticGap_hasDerivAt ha hcpos (by linarith [hy.1]))
    (by
      intro y hy hyc
      exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hyc)
        (lower_log_gap_coefficient_nonneg ha hc.1 hy.1))
    (by
      intro y hy hcy
      exact mul_nonneg (sub_nonneg.mpr hcy)
        (lower_log_gap_coefficient_nonneg ha hc.1 hy.1))
  simp only [logQuadraticGap, sub_self, zero_div, zero_pow (by decide : 2 ≠ 0),
    sub_zero, add_zero] at h
  linarith

/-- The exact upper quadratic support throughout a closed interval. -/
theorem log_quadratic_upper {a b c x : ℝ} (ha : 0 < 1+a)
    (hc : c ∈ Icc a b) (hx : x ∈ Icc a b) :
    Real.log (1+x) ≤ Real.log (1+c)+(x-c)/(1+c)-(x-c)^2/(2*(1+b)^2) := by
  have hcpos : 0 < 1+c := by linarith [hc.1]
  have hbpos : 0 < 1+b := by linarith [hc.1, hc.2]
  have h := minimum_at_of_derivative_sign
    (f := fun y => -logQuadraticGap b c y)
    (df := fun y => (y-c)*(1/((1+y)*(1+c))-1/(1+b)^2)) hc hx
    (by
      intro y hy
      have hd := (logQuadraticGap_hasDerivAt hbpos hcpos
        (show 0 < 1+y by linarith [hy.1])).neg
      convert hd using 1 <;> ring)
    (by
      intro y hy hyc
      exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hyc)
        (upper_log_gap_coefficient_nonneg hcpos (by linarith [hy.1]) hc.2 hy.2))
    (by
      intro y hy hcy
      exact mul_nonneg (sub_nonneg.mpr hcy)
        (upper_log_gap_coefficient_nonneg hcpos (by linarith [hy.1]) hc.2 hy.2))
  simp only [logQuadraticGap, sub_self, zero_div, zero_pow (by decide : 2 ≠ 0),
    sub_zero, add_zero] at h
  linarith

end Erdos993Lean.BCFG.Analytic

#check Erdos993Lean.BCFG.Analytic.minimum_at_of_derivative_sign
#print axioms Erdos993Lean.BCFG.Analytic.minimum_at_of_derivative_sign
#check Erdos993Lean.BCFG.Analytic.logQuadraticGap
#print axioms Erdos993Lean.BCFG.Analytic.logQuadraticGap
#check Erdos993Lean.BCFG.Analytic.logQuadraticGap_hasDerivAt
#print axioms Erdos993Lean.BCFG.Analytic.logQuadraticGap_hasDerivAt
#check Erdos993Lean.BCFG.Analytic.lower_log_gap_coefficient_nonneg
#print axioms Erdos993Lean.BCFG.Analytic.lower_log_gap_coefficient_nonneg
#check Erdos993Lean.BCFG.Analytic.upper_log_gap_coefficient_nonneg
#print axioms Erdos993Lean.BCFG.Analytic.upper_log_gap_coefficient_nonneg
#check Erdos993Lean.BCFG.Analytic.log_quadratic_lower
#print axioms Erdos993Lean.BCFG.Analytic.log_quadratic_lower
#check Erdos993Lean.BCFG.Analytic.log_quadratic_upper
#print axioms Erdos993Lean.BCFG.Analytic.log_quadratic_upper
