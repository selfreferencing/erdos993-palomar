module

public import Mathlib

/-!
Current T2a (Section 4), equations (31)--(32).
These are literal current definitions, not old rate/cap/profile substitutes.
Pi(0)=0 and H(q)=0 are exceptional assigned values. In particular H(q) is
not asserted to be a continuous extension of the nonleaf expression.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace

open Real Set

noncomputable def q (lam : ℝ) : ℝ := lam/(1+lam)
noncomputable def a (lam : ℝ) : ℝ := (1+4*lam)/100
noncomputable def aQ (q : ℝ) : ℝ := (1+3*q)/(100*(1-q))
noncomputable def rateR (q : ℝ) : ℝ := 2*q*(1+2*q)*(1-q)/((1+q)*(2-q))
noncomputable def lowRate (q : ℝ) : ℝ := rateR q-1/125
noncomputable def highRate (q : ℝ) : ℝ := rateR q+3/1250
noncomputable def delta (q : ℝ) : ℝ := if q < 3/7 then -1/125 else 3/1250
noncomputable def rate (q : ℝ) : ℝ := rateR q+delta q
noncomputable def ellH (lam : ℝ) : ℝ := rate (q lam)

noncomputable def f (lam t : ℝ) : ℝ := log (1+lam*exp (-t))
noncomputable def activityLog (lam : ℝ) : ℝ := log (1+lam)
noncomputable def b (p : ℝ) : ℝ := -log (1-p)
noncomputable def Y (lam p : ℝ) : ℝ := log (lam*(1-p)/p)
noncomputable def w (lam : ℝ) : ℝ := 1-2/(1+sqrt (1+4*lam))
noncomputable def kappa (lam : ℝ) : ℝ := (1+sqrt (1+4*lam))/2
noncomputable def Bplus (lam t : ℝ) : ℝ := max (log (lam/(exp t-1))) 0
noncomputable def Pi (lam t : ℝ) : ℝ :=
  if t = 0 then 0 else (1-w lam)*t+w lam*Bplus lam t
noncomputable def H (lam p : ℝ) : ℝ :=
  if p = q lam then 0 else Y lam p+w lam*Bplus lam (Y lam p)
noncomputable def E (lam t : ℝ) : ℝ := ellH lam/(q lam*(1+q lam*exp (-t)))
noncomputable def K (lam p : ℝ) : ℝ := 1-a lam*w lam+a lam*H lam p/b p
noncomputable def unitExpression (lam x y p : ℝ) : ℝ :=
  x*(K lam p-(p/b p)*E lam (x+y))+(1-a lam)*f lam (x+y)-f lam y+a lam*Pi lam y

def ActivityDomain (lam : ℝ) : Prop := 1/3 ≤ lam ∧ lam ≤ 7/3
def QDomain (q : ℝ) : Prop := 1/4 ≤ q ∧ q ≤ 7/10
def LowClosedDomain (q : ℝ) : Prop := 1/4 ≤ q ∧ q ≤ 3/7
def HighDomain (q : ℝ) : Prop := 3/7 ≤ q ∧ q ≤ 7/10
def UnitDomain (lam x y p : ℝ) : Prop :=
  0 < x ∧ 0 ≤ y ∧ 0 < p ∧ p ≤ q lam ∧ b p ≤ x

theorem q_pos {lam : ℝ} (hlam : 0 < lam) : 0 < q lam := by unfold q; positivity

theorem q_lt_one {lam : ℝ} (hlam : 0 < lam) : q lam < 1 := by
  unfold q
  apply (div_lt_one (by positivity)).2
  linarith

theorem q_domain {lam : ℝ} (h : ActivityDomain lam) : QDomain (q lam) := by
  have hp : 0 < 1+lam := by linarith [h.1]
  unfold QDomain q
  constructor
  · apply (le_div_iff₀ hp).2
    linarith [h.1]
  · apply (div_le_iff₀ hp).2
    linarith [h.2]

theorem activity_from_q {lam : ℝ} (hlam : 0 < lam) : lam = q lam/(1-q lam) := by
  have hd : 1+lam ≠ 0 := by positivity
  have hq : 1-q lam ≠ 0 := by linarith [q_lt_one hlam]
  unfold q at *
  field_simp [hd, hq] <;> ring

theorem a_eq_aQ {lam : ℝ} (hlam : 0 < lam) : a lam = aQ (q lam) := by
  have hd : 1+lam ≠ 0 := by positivity
  have hq : 1-q lam ≠ 0 := by linarith [q_lt_one hlam]
  unfold a aQ q at *
  field_simp [hd, hq] <;> ring

theorem a_bounds {lam : ℝ} (h : ActivityDomain lam) :
    7/300 ≤ a lam ∧ a lam ≤ 31/300 ∧ a lam < 11/100 := by
  unfold a
  constructor
  · linarith [h.1]
  constructor <;> linarith [h.2]

theorem rate_low {q : ℝ} (hq : q < 3/7) : rate q = lowRate q := by
  simp [rate, delta, lowRate, hq] <;> ring

theorem rate_high {q : ℝ} (hq : 3/7 ≤ q) : rate q = highRate q := by
  simp [rate, delta, highRate, not_lt.mpr hq]

/-- The actual switch uses the high branch, even though the low estimates close at it. -/
theorem rate_at_switch : rate (3/7) = highRate (3/7) := rate_high le_rfl

theorem high_minus_low (q : ℝ) : highRate q-lowRate q = 13/1250 := by
  unfold highRate lowRate
  ring

@[simp] theorem Pi_zero (lam : ℝ) : Pi lam 0 = 0 := by simp [Pi]
@[simp] theorem H_leaf (lam : ℝ) : H lam (q lam) = 0 := by simp [H]

theorem Pi_positive_argument {lam t : ℝ} (ht : 0 < t) :
    Pi lam t = (1-w lam)*t+w lam*Bplus lam t := by simp [Pi, ht.ne']

theorem H_nonleaf {lam p : ℝ} (hpq : p < q lam) :
    H lam p = Y lam p+w lam*Bplus lam (Y lam p) := by simp [H, ne_of_lt hpq]

theorem Y_positive {lam p : ℝ} (hlam : 0 < lam) (hp : 0 < p) (hpq : p < q lam) :
    0 < Y lam p := by
  have hden : 0 < 1+lam := by positivity
  have hpq' : p*(1+lam) < lam := (lt_div_iff₀ hden).mp hpq
  unfold Y
  apply Real.log_pos
  apply (lt_div_iff₀ hp).2
  nlinarith

theorem f_Y_eq_b {lam p : ℝ} (hlam : 0 < lam) (hp : 0 < p) (hpq : p < q lam) :
    f lam (Y lam p) = b p := by
  have hp1 : p < 1 := hpq.trans (q_lt_one hlam)
  have hu : 0 < lam*(1-p)/p := div_pos (mul_pos hlam (by linarith)) hp
  have he : exp (-Y lam p) = (lam*(1-p)/p)⁻¹ := by
    rw [Real.exp_neg, Y, Real.exp_log hu]
  unfold f b
  rw [he]
  have hid : 1+lam*(lam*(1-p)/p)⁻¹ = (1-p)⁻¹ := by
    field_simp [hlam.ne', hp.ne', ne_of_gt (show 0 < 1-p by linarith)] <;> ring
  rw [hid, Real.log_inv]

theorem H_eq_Pi_add {lam p : ℝ} (hlam : 0 < lam) (hp : 0 < p) (hpq : p < q lam) :
    H lam p = Pi lam (Y lam p)+w lam*Y lam p := by
  rw [H_nonleaf hpq, Pi_positive_argument (Y_positive hlam hp hpq)]
  ring

end Erdos993Lean.Analytic.V213.ZeroTiltLaplace

-- Audit commands.
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.q_pos
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.q_pos
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.q_lt_one
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.q_lt_one
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.q_domain
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.q_domain
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.activity_from_q
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.activity_from_q
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.a_eq_aQ
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.a_eq_aQ
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.a_bounds
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.a_bounds
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.rate_low
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.rate_low
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.rate_high
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.rate_high
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.rate_at_switch
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.rate_at_switch
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.high_minus_low
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.high_minus_low
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.Pi_zero
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.Pi_zero
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.H_leaf
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.H_leaf
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.Pi_positive_argument
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.Pi_positive_argument
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.H_nonleaf
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.H_nonleaf
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.Y_positive
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.Y_positive
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.f_Y_eq_b
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.f_Y_eq_b
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.H_eq_Pi_add
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.H_eq_Pi_add
