module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceChildDerivatives
public import Erdos993Lean.Analytic.V213.FreeCountRealScalarBounds
public import Erdos993Lean.Analytic.V213.FreeCountRealExpEnvelopes

/-!
Current Section3, paragraph after (19): the actual
strict child-coordinate alpha/gamma budget. The polynomial products are
monotone on the full closed message domain. This is not a completed CA
claim: the negative-weight and parent ell/denominator estimates remain
explicit premises for the final derivative wrapper.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance

open Real Set
open Envelopes

noncomputable def childCost (c u : ℝ) : ℝ :=
  u^2 * (c*(1-u/2) + c^2*(1-u/2)^2)

noncomputable def childCostSlope (c u : ℝ) : ℝ :=
  u*(2*c+2*c^2-3*c*u/2-3*c^2*u+c^2*u^2)

theorem childCost_hasDerivAt (c u : ℝ) :
    HasDerivAt (childCost c) (childCostSlope c u) u := by
  have hi := hasDerivAt_id u
  have hlin := (hi.div_const 2).const_sub 1
  unfold childCost
  apply ((hi.pow 2).mul
    ((hlin.const_mul c).add ((hlin.pow 2).const_mul (c^2)))).congr_deriv
  unfold childCostSlope
  (try dsimp) <;> ring

theorem childCostSlope_nonneg {c u : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hu0 : 0 ≤ u) (hu7 : u ≤ 7/10) :
    0 ≤ childCostSlope c u := by
  have hc2 : c^2 ≤ c := by nlinarith
  have hcu : c*u ≤ c*(7/10) := mul_le_mul_of_nonneg_left hu7 hc0
  have hccu : c^2*u ≤ c^2*(7/10) :=
    mul_le_mul_of_nonneg_left hu7 (sq_nonneg c)
  have hlast : 0 ≤ c^2*u^2 := mul_nonneg (sq_nonneg c) (sq_nonneg u)
  have hb : 0 ≤ 2*c+2*c^2-3*c*u/2-3*c^2*u+c^2*u^2 := by
    nlinarith only [hc0, hc2, hcu, hccu, hlast]
  exact mul_nonneg hu0 hb

theorem childCost_monotone {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    MonotoneOn (childCost c) (Icc 0 (7/10)) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 (7/10))
    (fun u hu => (childCost_hasDerivAt c u).continuousAt.continuousWithinAt)
    (fun u hu => (childCost_hasDerivAt c u).hasDerivWithinAt)
  intro u hu
  have hi := interior_subset hu
  exact childCostSlope_nonneg hc0 hc1 hi.1 hi.2

theorem actual_childCost_le_q {lam t c : ℝ} (hlam : 0 < lam)
    (hlam7 : lam ≤ 7/3) (ht : 0 ≤ t) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    message lam t^2 * (c*childH lam t+c^2*childH lam t^2) ≤
      childCost c (q lam) := by
  have hu := message_pos hlam t
  have hmq := message_le_q hlam ht
  have hq := q_pos hlam
  have hq7 : q lam ≤ 7/10 := by
    unfold q
    apply (div_le_iff₀ (by linarith : 0 < 1+lam)).2
    linarith
  have hv : 0 ≤ 1-message lam t/2 := by linarith [message_lt_one hlam t]
  have hh := childH_pos hlam t
  have hupper : childH lam t ≤ 1-message lam t/2 := (message_scalarH_bounds hlam t).2
  have hs : childH lam t^2 ≤ (1-message lam t/2)^2 := by nlinarith
  have hsum := add_le_add (mul_le_mul_of_nonneg_left hupper hc0)
    (mul_le_mul_of_nonneg_left hs (sq_nonneg c))
  have hcost := mul_le_mul_of_nonneg_left hsum (sq_nonneg (message lam t))
  exact hcost.trans
    (childCost_monotone hc0 hc1 ⟨hu.le, hmq.trans hq7⟩ ⟨hq.le, hq7⟩ hmq)

theorem alpha_beta_budget_identity {D lam : ℝ} (hlam : 0 < lam) :
    alpha D lam * (5*logActivity lam^2) = 7*(gamma D lam*q lam^2) := by
  have hb := (logActivity_pos hlam).ne'
  unfold alpha gamma
  field_simp [hb] <;> ring

theorem alpha_lower_from_beta {D lam k B : ℝ} (hD : 0 < D) (hlam : 0 < lam)
    (hB : 0 < B) (hk : 0 ≤ k) (hbeta : logActivity lam^2 ≤ B)
    (hidentity : k*(5*B) = 7) :
    k*(gamma D lam*q lam^2) ≤ alpha D lam := by
  have ha := alpha_pos hD hlam
  have hi := alpha_beta_budget_identity (D := D) hlam
  have hm := mul_le_mul_of_nonneg_left hbeta (show 0 ≤ 5*alpha D lam by positivity)
  have hx := mul_le_mul_of_nonneg_left hm hk
  have hik := congrArg (fun z : ℝ => k*z) hi
  have hid : k*(5*alpha D lam*B) = 7*alpha D lam := by
    calc
      _ = alpha D lam*(k*(5*B)) := by ring
      _ = _ := by rw [hidentity]; ring
  nlinarith only [hx, hik, hid]

theorem beta_lt_seven_tenths {lam : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1) :
    logActivity lam < 7/10 := by
  have hh := Real.log_le_log (by linarith : 0 < 1+lam)
    (by linarith : 1+lam ≤ 2)
  unfold logActivity
  linarith [log_two_brackets.2]

theorem beta_lt_one {lam : ℝ} (hlam : 0 < lam) (hlam3 : lam ≤ 3/2) :
    logActivity lam < 1 := by
  unfold logActivity
  apply (Real.log_lt_iff_lt_exp (by linarith : 0 < 1+lam)).2
  linarith [exp_one_gt_eight_thirds]

theorem beta_lt_five_fourths {lam : ℝ} (hlam : 0 < lam) (hlam7 : lam ≤ 7/3) :
    logActivity lam < 5/4 := by
  unfold logActivity
  apply (Real.log_lt_iff_lt_exp (by linarith : 0 < 1+lam)).2
  linarith [exp_five_fourths_gt_ten_thirds]

theorem childCost_one_le_two {u : ℝ} (hu0 : 0 ≤ u) (hu7 : u ≤ 7/10) :
    childCost 1 u ≤ 2*u^2 := by
  have hv0 : 0 ≤ 1-u/2 := by linarith
  have hv1 : 1-u/2 ≤ 1 := by linarith
  have hs : (1-u/2)^2 ≤ 1 := by nlinarith
  have hh := mul_le_mul_of_nonneg_left (show (1-u/2)+(1-u/2)^2 ≤ 2 by linarith)
    (sq_nonneg u)
  simpa only [childCost, one_mul, one_pow, mul_comm] using hh

theorem childCost_one_le_twentyone_sixteenths {u : ℝ}
    (hu5 : 1/2 ≤ u) (hu7 : u ≤ 7/10) :
    childCost 1 u ≤ (21/16)*u^2 := by
  have hv0 : 0 ≤ 1-u/2 := by linarith
  have hv : 1-u/2 ≤ 3/4 := by linarith
  have hs : (1-u/2)^2 ≤ (3/4 : ℝ)^2 := by nlinarith
  have hh := mul_le_mul_of_nonneg_left
    (show (1-u/2)+(1-u/2)^2 ≤ 21/16 by nlinarith) (sq_nonneg u)
  simpa only [childCost, one_mul, one_pow, mul_comm] using hh

theorem childCost_two_thirds_bound {u : ℝ} (hu6 : 3/5 ≤ u) (hu7 : u ≤ 7/10) :
    childCost (2/3) u ≤ (154/225)*u^2 := by
  have hv0 : 0 ≤ 1-u/2 := by linarith
  have hv : 1-u/2 ≤ 7/10 := by linarith
  have hs : (1-u/2)^2 ≤ (7/10 : ℝ)^2 := by nlinarith
  have hh := mul_le_mul_of_nonneg_left
    (show (2/3)*(1-u/2)+(2/3 : ℝ)^2*(1-u/2)^2 ≤ 154/225 by nlinarith)
    (sq_nonneg u)
  simpa only [childCost, mul_comm] using hh

theorem child_budget_first_two {D lam t : ℝ} (hD : 0 < D)
    (hlam : 0 < lam) (hlam3 : lam ≤ 3/2) (ht : 0 ≤ t) :
    gamma D lam*message lam t^2*(childH lam t+childH lam t^2) < alpha D lam := by
  have hb := logActivity_pos hlam
  have hg := gamma_pos hD hlam
  have hq := q_pos hlam
  have hq7 : q lam ≤ 7/10 := by
    unfold q
    apply (div_le_iff₀ (by linarith : 0 < 1+lam)).2
    linarith
  have hcost := actual_childCost_le_q hlam (by linarith) ht
    (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 1)
  simp only [one_mul, one_pow] at hcost
  by_cases hl : lam ≤ 1
  · have hu := beta_lt_seven_tenths hlam hl
    have hs : logActivity lam^2 ≤ (49/100 : ℝ) := by nlinarith
    have ha := alpha_lower_from_beta hD hlam (by norm_num : (0 : ℝ) < 49/100)
      (by norm_num : (0 : ℝ) ≤ 20/7) hs (by norm_num : (20/7 : ℝ)*(5*(49/100)) = 7)
    have hm := mul_le_mul_of_nonneg_left
      (hcost.trans (childCost_one_le_two hq.le hq7)) hg.le
    nlinarith [mul_pos hg (sq_pos_of_pos hq)]
  · have hq5 : 1/2 ≤ q lam := by
      unfold q
      apply (le_div_iff₀ (by linarith : 0 < 1+lam)).2
      linarith
    have hu := beta_lt_one hlam hlam3
    have hs : logActivity lam^2 ≤ (1 : ℝ) := by nlinarith
    have ha := alpha_lower_from_beta hD hlam (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) ≤ 7/5) hs (by norm_num : (7/5 : ℝ)*(5*1) = 7)
    have hm := mul_le_mul_of_nonneg_left
      (hcost.trans (childCost_one_le_twentyone_sixteenths hq5 hq7)) hg.le
    nlinarith [mul_pos hg (sq_pos_of_pos hq)]

theorem child_budget_last_three {D lam t : ℝ} (hD : 0 < D)
    (hlam3 : 3/2 ≤ lam) (hlam7 : lam ≤ 7/3) (ht : 0 ≤ t) :
    gamma D lam*message lam t^2*((2/3)*childH lam t+(4/9)*childH lam t^2) < alpha D lam := by
  have hlam : 0 < lam := by linarith
  have hb := logActivity_pos hlam
  have hg := gamma_pos hD hlam
  have hq := q_pos hlam
  have hq6 : 3/5 ≤ q lam := by
    unfold q
    apply (le_div_iff₀ (by linarith : 0 < 1+lam)).2
    linarith
  have hq7 : q lam ≤ 7/10 := by
    unfold q
    apply (div_le_iff₀ (by linarith : 0 < 1+lam)).2
    linarith
  have hcost := actual_childCost_le_q hlam hlam7 ht
    (by norm_num : (0 : ℝ) ≤ 2/3) (by norm_num : (2/3 : ℝ) ≤ 1)
  have hu := beta_lt_five_fourths hlam hlam7
  have hs : logActivity lam^2 ≤ (25/16 : ℝ) := by nlinarith
  have ha := alpha_lower_from_beta hD hlam (by norm_num : (0 : ℝ) < 25/16)
    (by norm_num : (0 : ℝ) ≤ 112/125) hs
    (by norm_num : (112/125 : ℝ)*(5*(25/16)) = 7)
  have hm := mul_le_mul_of_nonneg_left
    (hcost.trans (childCost_two_thirds_bound hq6 hq7)) hg.le
  norm_num at hm
  nlinarith [mul_pos hg (sq_pos_of_pos hq)]

end Erdos993Lean.Analytic.V213.FreeCountVariance

#check Erdos993Lean.Analytic.V213.FreeCountVariance.childCost_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.childCost_hasDerivAt
#check Erdos993Lean.Analytic.V213.FreeCountVariance.childCostSlope_nonneg
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.childCostSlope_nonneg
#check Erdos993Lean.Analytic.V213.FreeCountVariance.childCost_monotone
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.childCost_monotone
#check Erdos993Lean.Analytic.V213.FreeCountVariance.actual_childCost_le_q
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.actual_childCost_le_q
#check Erdos993Lean.Analytic.V213.FreeCountVariance.alpha_beta_budget_identity
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.alpha_beta_budget_identity
#check Erdos993Lean.Analytic.V213.FreeCountVariance.alpha_lower_from_beta
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.alpha_lower_from_beta
#check Erdos993Lean.Analytic.V213.FreeCountVariance.beta_lt_seven_tenths
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.beta_lt_seven_tenths
#check Erdos993Lean.Analytic.V213.FreeCountVariance.beta_lt_one
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.beta_lt_one
#check Erdos993Lean.Analytic.V213.FreeCountVariance.beta_lt_five_fourths
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.beta_lt_five_fourths
#check Erdos993Lean.Analytic.V213.FreeCountVariance.childCost_one_le_two
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.childCost_one_le_two
#check Erdos993Lean.Analytic.V213.FreeCountVariance.childCost_one_le_twentyone_sixteenths
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.childCost_one_le_twentyone_sixteenths
#check Erdos993Lean.Analytic.V213.FreeCountVariance.childCost_two_thirds_bound
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.childCost_two_thirds_bound
#check Erdos993Lean.Analytic.V213.FreeCountVariance.child_budget_first_two
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.child_budget_first_two
#check Erdos993Lean.Analytic.V213.FreeCountVariance.child_budget_last_three
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.child_budget_last_three
