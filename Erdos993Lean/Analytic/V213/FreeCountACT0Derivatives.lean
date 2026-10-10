module

public import Erdos993Lean.Analytic.V213.FreeCountACParentFunctions
public import Erdos993Lean.Analytic.V213.FreeCountRealScalarBounds

/-!+Exact parent derivatives and the last curvature estimate of current (28).
The 3/25 message bound is proved on the actual closed range p<=q<=7/10;
the 1/10 loss follows from D>=6/5. No cell record is used.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance

open Real

noncomputable def T0Slope (D lam y : ℝ) : ℝ :=
  -(message lam y * (1 - message lam y)) / (D * q lam) +
    (7 / 12 : ℝ) * ((1 + y) * exp y) / ((1 + lam) * logActivity lam)

noncomputable def T0Curvature (D lam y : ℝ) : ℝ :=
  message lam y * (1 - message lam y) * (1 - 2 * message lam y) / (D * q lam) +
    (7 / 12 : ℝ) * ((2 + y) * exp y) / ((1 + lam) * logActivity lam)

theorem T0_hasDerivAt_parent {D lam : ℝ} (hD : 0 < D) (hlam : 0 < lam) (y : ℝ) :
    HasDerivAt (T0 D lam) (T0Slope D lam y) y := by
  have hp := message_hasDerivAt hlam y
  unfold T0
  apply ((((hp.div_const (q lam)).sub_const 1).div_const D).add
    ((((hasDerivAt_id y).mul (Real.hasDerivAt_exp y)).const_mul (7 / 12 : ℝ)).div_const
      ((1 + lam) * logActivity lam))).congr_deriv
  unfold T0Slope
  (try dsimp) <;> (try simp only [id_eq, Pi.pow_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply]) <;> field_simp [hD.ne', (q_pos hlam).ne', (logActivity_pos hlam).ne',
    ne_of_gt (show 0 < 1 + lam by linarith)] <;> ring

theorem T0Slope_hasDerivAt_parent {D lam : ℝ} (hD : 0 < D) (hlam : 0 < lam) (y : ℝ) :
    HasDerivAt (T0Slope D lam) (T0Curvature D lam y) y := by
  have hp := message_hasDerivAt hlam y
  unfold T0Slope
  apply ((((hp.mul (hp.const_sub 1)).neg).div_const (D * q lam)).add
    (((((hasDerivAt_id y).const_add 1).mul (Real.hasDerivAt_exp y)).const_mul (7 / 12 : ℝ)).div_const
      ((1 + lam) * logActivity lam))).congr_deriv
  unfold T0Curvature
  (try dsimp) <;> (try simp only [id_eq, Pi.pow_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply]) <;> field_simp [hD.ne', (q_pos hlam).ne', (logActivity_pos hlam).ne',
    ne_of_gt (show 0 < 1 + lam by linarith)] <;> ring

theorem message_ratio_curvature_lower {lam y : ℝ} (hlam : 0 < lam)
    (hlam7 : lam ≤ 7 / 3) (hy : 0 ≤ y) :
    -(3 / 25 : ℝ) ≤
      (message lam y / q lam) * (1 - message lam y) * (1 - 2 * message lam y) := by
  have hp := message_pos hlam y
  have hp1 := message_lt_one hlam y
  have hq := q_pos hlam
  have hpq := Envelopes.message_le_q hlam hy
  have hq7 : q lam ≤ 7 / 10 := by
    unfold q
    apply (div_le_iff₀ (by linarith : 0 < 1 + lam)).2
    linarith
  have hp7 : message lam y ≤ 7 / 10 := hpq.trans hq7
  have hr0 : 0 ≤ message lam y / q lam := (div_pos hp hq).le
  have hr1 : message lam y / q lam ≤ 1 := (div_le_one hq).2 hpq
  by_cases hh : message lam y ≤ 1 / 2
  · have hn : 0 ≤ (message lam y / q lam) * (1 - message lam y) *
        (1 - 2 * message lam y) := by
      apply mul_nonneg (mul_nonneg hr0 (by linarith)) (by linarith)
    linarith
  · have hv0 : 0 ≤ (1 - message lam y) * (2 * message lam y - 1) :=
      mul_nonneg (by linarith) (by linarith)
    have hf : 0 ≤ (7 / 10 - message lam y) * (8 / 5 - 2 * message lam y) :=
      mul_nonneg (by linarith) (by linarith)
    have hv : (1 - message lam y) * (2 * message lam y - 1) ≤ 3 / 25 := by
      nlinarith only [hf]
    have hm := mul_le_mul_of_nonneg_right hr1 hv0
    nlinarith only [hm, hv]

/-- Closed parent intervals may include c=0; the estimate itself has no 1/y.
The later AC conclusion still explicitly excludes y=0. -/
theorem T0Curvature_lower {D lam c y : ℝ}
    (hD : (6 / 5 : ℝ) ≤ D) (hlam : 0 < lam) (hlam7 : lam ≤ 7 / 3)
    (hc : 0 ≤ c) (hcy : c ≤ y) :
    (7 / 12 : ℝ) * ((2 + c) * exp c) / ((1 + lam) * logActivity lam) - 1 / 10 ≤
      T0Curvature D lam y := by
  have hD0 : 0 < D := by linarith
  have hy : 0 ≤ y := hc.trans hcy
  have hmsg := message_ratio_curvature_lower hlam hlam7 hy
  have hfirst : -(1 / 10 : ℝ) ≤
      ((message lam y / q lam) * (1 - message lam y) * (1 - 2 * message lam y)) / D := by
    apply (le_div_iff₀ hD0).2
    linarith only [hD, hmsg]
  have hexp : (2 + c) * exp c ≤ (2 + y) * exp y :=
    mul_le_mul (by linarith) (Real.exp_le_exp.mpr hcy) (Real.exp_pos c).le (by linarith)
  have hsecond := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hexp (by norm_num : (0 : ℝ) ≤ 7 / 12))
    (show 0 ≤ (1 + lam) * logActivity lam by
      exact mul_nonneg (by linarith) (logActivity_pos hlam).le)
  have hid : ((message lam y / q lam) * (1 - message lam y) * (1 - 2 * message lam y)) / D =
      message lam y * (1 - message lam y) * (1 - 2 * message lam y) / (D * q lam) := by
    (try dsimp) <;> (try simp only [id_eq, Pi.pow_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply]) <;> ring
  rw [hid] at hfirst
  unfold T0Curvature
  linarith only [hfirst, hsecond]

end Erdos993Lean.Analytic.V213.FreeCountVariance

#check Erdos993Lean.Analytic.V213.FreeCountVariance.T0_hasDerivAt_parent
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.T0_hasDerivAt_parent
#check Erdos993Lean.Analytic.V213.FreeCountVariance.T0Slope_hasDerivAt_parent
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.T0Slope_hasDerivAt_parent
#check Erdos993Lean.Analytic.V213.FreeCountVariance.message_ratio_curvature_lower
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.message_ratio_curvature_lower
#check Erdos993Lean.Analytic.V213.FreeCountVariance.T0Curvature_lower
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.T0Curvature_lower
