module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceCaps
public import Erdos993Lean.Analytic.V213.FreeCountRealScalarBounds
public import Erdos993Lean.Analytic.V213.FreeCountRealExpEnvelopes

/-!
Proof of the actual uniform child-J part of Lemma 3.2.
The half bound uses the printed quartic. The third bound uses a global
logarithm tangent instead of locating the printed cubic's minimum; its only
remaining finite premise is the very same printed log (369/80)<153/100.
No old cap theorem or finite table is substituted.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform

open Real Envelopes

theorem J_le_scalar_envelope {lam t : ℝ} (hlam : 0 < lam) (ht : 0 ≤ t) :
    J lam t ≤ t * message lam t * (1-message lam t/2) := by
  have hh := (message_scalarH_bounds hlam t).2
  have hm := mul_le_mul_of_nonneg_left hh
    (mul_nonneg ht (message_pos hlam t).le)
  convert hm using 1 <;> dsimp [J] <;> ring

theorem J_lt_half_small {lam t : ℝ} (hlam : 0 < lam)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) : J lam t < 1/2 := by
  have hp := message_pos hlam t
  have hp1 := message_lt_one hlam t
  have henv := J_le_scalar_envelope hlam ht
  have hu : 0 ≤ message lam t*(1-message lam t/2) :=
    mul_nonneg hp.le (by linarith)
  have htbound := mul_le_mul_of_nonneg_right ht1 hu
  have hsq : 0 < (1-message lam t)^2 := sq_pos_of_pos (by linarith)
  nlinarith

theorem printed_quartic_positive {t : ℝ} (ht : 1 ≤ t) :
    0 < t^4+4*t^3+12*t^2-88*t+88 := by
  have ht0 : 0 ≤ t := by linarith
  have hid : t^4+4*t^3+12*t^2-88*t+88 =
      (t^2+(36/5)*t)*(t-8/5)^2 +
        (812/25)*(t-1663/1015)^2+102724/126875 := by ring
  rw [hid]
  have hfirst : 0 ≤ (t^2+(36/5)*t)*(t-8/5)^2 := by positivity
  nlinarith [sq_nonneg (t-1663/1015)]

theorem exp_child_ratio_lower {lam t : ℝ} (hlam : 0 < lam)
    (hlam7 : lam ≤ 7/3) (ht : 1 ≤ t) : 2*t-3/2 < exp t/lam := by
  have he := expPartial_le_exp 4 (x := t) (by linarith)
  norm_num [expPartial, Finset.sum_range_succ, Nat.factorial] at he
  have hquartic := printed_quartic_positive ht
  have hgap : 0 < 3*exp t-14*t+8 := by nlinarith
  have hz : 0 < exp t/lam := div_pos (exp_pos t) hlam
  have hmul : lam*(exp t/lam)=exp t := by field_simp <;> ring
  have hh := mul_le_mul_of_nonneg_right hlam7 hz.le
  nlinarith

theorem J_le_rational_envelope {lam t : ℝ} (hlam : 0 < lam) (ht : 0 ≤ t) :
    J lam t ≤ t*(1+2*(exp t/lam))/(2*(1+exp t/lam)^2) := by
  have hz : 0 < exp t/lam := div_pos (exp_pos t) hlam
  have hu : message lam t = 1/(1+exp t/lam) := by
    rw [message_eq_exp_quotient hlam]
    field_simp [hlam.ne', (exp_pos t).ne', ne_of_gt (show 0 < exp t+lam by positivity)] <;> ring
  calc
    J lam t ≤ t*message lam t*(1-message lam t/2) := J_le_scalar_envelope hlam ht
    _ = t*(1+2*(exp t/lam))/(2*(1+exp t/lam)^2) := by
      rw [hu]
      field_simp [ne_of_gt (show 0 < 1+exp t/lam by positivity)] <;> ring

theorem J_lt_half {lam t : ℝ} (hlam : 0 < lam)
    (hlam7 : lam ≤ 7/3) (ht : 0 ≤ t) : J lam t < 1/2 := by
  by_cases ht1 : t ≤ 1
  · exact J_lt_half_small hlam ht ht1
  have htge : 1 ≤ t := by linarith
  let z := exp t/lam
  have hz : 0 < z := div_pos (exp_pos t) hlam
  have hzl : 2*t-3/2 < z := exp_child_ratio_lower hlam hlam7 htge
  have hid : (1+z)^2-t*(1+2*z) =
      1/4+(z-(2*t-3/2))*(z+1/2) := by ring
  have hgap : 0 < (1+z)^2-t*(1+2*z) := by
    rw [hid]
    have : 0 < (z-(2*t-3/2))*(z+1/2) := mul_pos (by linarith) (by linarith)
    linarith
  have hrat : t*(1+2*z)/(2*(1+z)^2) < (1/2 : ℝ) := by
    apply (div_lt_iff₀ (by positivity)).2
    nlinarith
  exact (J_le_rational_envelope hlam ht).trans_lt hrat

/-- A global rational comparison for the actual F (z) in the paper. -/
theorem third_rational_gap {z : ℝ} (hz : 0 < z) :
    (1/25 : ℝ) < z/123+1/(6*(1+2*z)) := by
  have hid : (z/123+1/(6*(1+2*z))-1/25)*(18450*(1+2*z)) =
      300*(z-221/100)^2+87177/100 := by
    field_simp [ne_of_gt (show 0 < 1+2*z by positivity)] <;> ring
  have hp : 0 < (z/123+1/(6*(1+2*z))-1/25)*(18450*(1+2*z)) := by
    rw [hid]
    nlinarith [sq_nonneg (z-221/100)]
  have hden : 0 < 18450*(1+2*z) := by positivity
  have : 0 < z/123+1/(6*(1+2*z))-1/25 :=
    (mul_pos_iff_of_pos_right hden).mp hp
  linarith

theorem third_log_tangent {z : ℝ} (hz : 0 < z)
    (hlog : log (369/80 : ℝ) < 153/100) :
    log ((3/2)*z) < 2*(1+z)^2/(3*(1+2*z)) := by
  have ht := log_le_sub_one_of_pos
    (show 0 < ((3/2)*z)/(369/80 : ℝ) by positivity)
  rw [log_div (by positivity) (by norm_num)] at ht
  have hr : ((3/2)*z)/(369/80 : ℝ) = 40*z/123 := by ring
  rw [hr] at ht
  have hf := third_rational_gap hz
  have hid : 2*(1+z)^2/(3*(1+2*z)) = z/3+1/2+1/(6*(1+2*z)) := by
    field_simp [ne_of_gt (show 0 < 1+2*z by positivity)] <;> ring
  rw [hid]
  linarith

theorem J_lt_third_of_printed_log {lam t : ℝ} (hlam : 0 < lam)
    (hlam3 : lam ≤ 3/2) (ht : 0 ≤ t)
    (hlog : log (369/80 : ℝ) < 153/100) : J lam t < 1/3 := by
  let z := exp t/lam
  have hz : 0 < z := div_pos (exp_pos t) hlam
  have he : exp t = lam*z := by dsimp [z]; field_simp <;> ring
  have heupper : exp t ≤ (3/2)*z := by
    rw [he]
    exact mul_le_mul_of_nonneg_right hlam3 hz.le
  have hlogupper : t ≤ log ((3/2)*z) := by
    have hh := Real.log_le_log (exp_pos t) heupper
    simpa only [log_exp] using hh
  have hbound := hlogupper.trans_lt (third_log_tangent hz hlog)
  have hcross : t*(3*(1+2*z)) < 2*(1+z)^2 :=
    (lt_div_iff₀ (by positivity)).mp hbound
  have hrat : t*(1+2*z)/(2*(1+z)^2) < (1/3 : ℝ) := by
    apply (div_lt_iff₀ (by positivity)).2
    nlinarith
  exact (J_le_rational_envelope hlam ht).trans_lt hrat

theorem cap_J_bound {c : Cap} {lam t : ℝ} (hc : c.Contains lam) (ht : 0 ≤ t)
    (hlog : log (369/80 : ℝ) < 153/100) : J lam t < c.jBound := by
  have hlam := Cap.activity_pos hc
  have hlam7 := (Cap.activity_domain hc).2
  cases c with
  | first =>
      have hu : lam ≤ (263/200 : ℝ) := hc.2
      exact J_lt_third_of_printed_log hlam (by linarith) ht hlog
  | second =>
      exact J_lt_third_of_printed_log hlam hc.2 ht hlog
  | third => exact J_lt_half hlam hlam7 ht
  | fourth => exact J_lt_half hlam hlam7 ht
  | fifth => exact J_lt_half hlam hlam7 ht

end Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform

-- Type and axiom audit commands.
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.J_le_scalar_envelope
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.J_le_scalar_envelope
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.J_lt_half_small
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.J_lt_half_small
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.printed_quartic_positive
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.printed_quartic_positive
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.exp_child_ratio_lower
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.exp_child_ratio_lower
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.J_le_rational_envelope
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.J_le_rational_envelope
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.J_lt_half
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.J_lt_half
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.third_rational_gap
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.third_rational_gap
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.third_log_tangent
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.third_log_tangent
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.J_lt_third_of_printed_log
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.J_lt_third_of_printed_log
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.cap_J_bound
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.cap_J_bound
