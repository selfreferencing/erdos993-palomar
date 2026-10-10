module

public import Erdos993Lean.Analytic.V213.FreeCountACParentFunctions
public import Erdos993Lean.Analytic.V213.FreeCountRealScalarBounds
public import Erdos993Lean.Analytic.V213.FreeCountRealExpEnvelopes

/-! Actual activity monotonicities in current (28). Activity derivatives hold
D fixed. Closed upper endpoints are included; lambda=0 is not silently
assigned a quotient value. The T0 sign includes y=0, where it is equality. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance

open Real Set

theorem scalarH_add_self_monotone :
    MonotoneOn (fun p : ℝ => Envelopes.scalarH p+p) (Ioc 0 (7/10)) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioc 0 (7/10))
    (f' := fun p => deriv Envelopes.scalarH p+1)
  · intro p hp
    exact ((Envelopes.hasDerivAt_scalarH hp.1 (by linarith [hp.2])).add
      (hasDerivAt_id p)).continuousAt.continuousWithinAt
  · intro p hp
    have hh := interior_subset hp
    have hd := Envelopes.hasDerivAt_scalarH hh.1 (by linarith [hh.2])
    rw [hd.deriv]
    exact (hd.add (hasDerivAt_id p)).hasDerivWithinAt
  · intro p hp
    have hh := interior_subset hp
    have hb := Envelopes.scalarH_deriv_gt_neg_one hh.1 hh.2
    linarith

theorem rho_activity_deriv_nonpos {lam y : ℝ} (hlam : 0<lam)
    (hlam7 : lam≤7/3) (hy : 0≤y) :
    deriv (fun a => rho a y) lam ≤ 0 := by
  have hp := message_pos hlam y
  have hq := q_pos hlam
  have hq7 : q lam≤7/10 := by
    unfold q
    apply (div_le_iff₀ (by linarith : 0<1+lam)).2
    linarith
  have hpq := Envelopes.message_le_q hlam hy
  have hh := scalarH_add_self_monotone ⟨hp, hpq.trans hq7⟩ ⟨hq, hq7⟩ hpq
  have hpH : Envelopes.scalarH (message lam y) = 1/B lam y := by
    unfold Envelopes.scalarH Envelopes.scalarLog B
    rw [← logMass_eq_neg_log hlam y]
    simp only [one_div_div]
  have hqH : Envelopes.scalarH (q lam) = q lam/logActivity lam := by
    have hh0 := logMass_eq_neg_log hlam 0
    simp only [logMass_zero, message_zero] at hh0
    unfold Envelopes.scalarH Envelopes.scalarLog
    rw [← hh0]
  change Envelopes.scalarH (message lam y) + message lam y ≤
    Envelopes.scalarH (q lam) + q lam at hh
  rw [hpH, hqH] at hh
  rw [(rho_hasDerivAt_activity hlam y).deriv]
  exact mul_nonpos_of_nonneg_of_nonpos
    (div_pos (rho_pos hlam y) hlam).le (by linarith)

theorem rho_antitone_activity {y : ℝ} (hy : 0≤y) :
    AntitoneOn (fun a => rho a y) (Ioc 0 (7/3)) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioc 0 (7/3))
    (f' := fun a => deriv (fun b => rho b y) a)
  · intro a ha
    exact (rho_hasDerivAt_activity ha.1 y).continuousAt.continuousWithinAt
  · intro a ha
    have hh := interior_subset ha
    have hd := rho_hasDerivAt_activity hh.1 y
    rw [hd.deriv]
    exact hd.hasDerivWithinAt
  · intro a ha
    have hh := interior_subset ha
    exact rho_activity_deriv_nonpos hh.1 hh.2 hy

theorem beta_div_activity_hasDerivAt {lam : ℝ} (hlam : 0<lam) :
    HasDerivAt (fun a => logActivity a/a)
      ((q lam-logActivity lam)/lam^2) lam := by
  apply ((logActivity_hasDerivAt hlam).div (hasDerivAt_id lam) hlam.ne').congr_deriv
  unfold q
  (try dsimp) <;> (try simp only [id_eq, Pi.pow_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply]) <;> ring

theorem beta_div_activity_deriv_nonpos {lam : ℝ} (hlam : 0<lam) :
    deriv (fun a => logActivity a/a) lam ≤ 0 := by
  have hh := (Envelopes.message_scalarH_bounds hlam 0).1
  simp only [message_zero, logMass_zero] at hh
  have hlog := Real.log_le_sub_one_of_pos (show 0<(1+lam)⁻¹ by positivity)
  rw [Real.log_inv] at hlog
  have hb : q lam≤logActivity lam := by
    unfold q logActivity
    have hi : 1-(1+lam)⁻¹ = lam/(1+lam) := by
      (try dsimp) <;> (try simp only [id_eq, Pi.pow_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply]) <;> field_simp [ne_of_gt (show 0<1+lam by linarith)] <;> ring
    rw [← hi]
    linarith
  rw [(beta_div_activity_hasDerivAt hlam).deriv]
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hb) (sq_nonneg _)

noncomputable def betaRatio (lam : ℝ) : ℝ :=
  (logActivity lam/q lam)^2/(1+lam)

theorem betaRatio_hasDerivAt {lam : ℝ} (hlam : 0<lam) :
    HasDerivAt betaRatio
      (betaRatio lam/lam*(2*q lam/logActivity lam-2+q lam)) lam := by
  have hb := (logActivity_pos hlam).ne'
  have hq := (q_pos hlam).ne'
  have h1 : 1+lam ≠ 0 := ne_of_gt (by linarith)
  unfold betaRatio
  apply ((((logActivity_hasDerivAt hlam).div (q_hasDerivAt hlam) hq).pow 2).div
    ((hasDerivAt_id lam).const_add 1) h1).congr_deriv
  unfold q
  (try dsimp) <;> (try simp only [id_eq, Pi.pow_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply]) <;> field_simp [hlam.ne', hb, h1] <;> ring

theorem betaRatio_deriv_nonpos {lam : ℝ} (hlam : 0<lam) : deriv betaRatio lam ≤ 0 := by
  have hh := (Envelopes.message_scalarH_bounds hlam 0).2
  simp only [message_zero, logMass_zero] at hh
  have hp : 0≤betaRatio lam/lam := by
    unfold betaRatio
    positivity
  rw [(betaRatio_hasDerivAt hlam).deriv]
  exact mul_nonpos_of_nonneg_of_nonpos hp (by
    ring_nf at hh ⊢
    linarith only [hh])

theorem beta_div_activity_antitone : AntitoneOn (fun a => logActivity a/a) (Ioi 0) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi 0)
    (f' := fun a => (q a-logActivity a)/a^2)
  · intro a ha
    exact (beta_div_activity_hasDerivAt ha).continuousAt.continuousWithinAt
  · intro a ha
    exact (beta_div_activity_hasDerivAt (interior_subset ha)).hasDerivWithinAt
  · intro a ha
    have hh := beta_div_activity_deriv_nonpos (interior_subset ha)
    rwa [(beta_div_activity_hasDerivAt (interior_subset ha)).deriv] at hh

theorem betaRatio_antitone : AntitoneOn betaRatio (Ioi 0) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi 0)
    (f' := fun a => betaRatio a/a*(2*q a/logActivity a-2+q a))
  · intro a ha
    exact (betaRatio_hasDerivAt ha).continuousAt.continuousWithinAt
  · intro a ha
    exact (betaRatio_hasDerivAt (interior_subset ha)).hasDerivWithinAt
  · intro a ha
    have hh := betaRatio_deriv_nonpos (interior_subset ha)
    rwa [(betaRatio_hasDerivAt (interior_subset ha)).deriv] at hh

theorem logActivity_lt_five_fourths {lam : ℝ} (hlam : 0<lam) (hlam7 : lam≤7/3) :
    logActivity lam < 5/4 := by
  apply (Real.log_lt_iff_lt_exp (by linarith : 0<1+lam)).2
  exact lt_of_le_of_lt (by linarith) Envelopes.exp_five_fourths_gt_ten_thirds

noncomputable def T0ActivitySlope (D lam y : ℝ) : ℝ :=
  (exp y-1)/(D*(exp y+lam)^2) -
    (7/12:ℝ)*y*exp y*(logActivity lam+1)/((1+lam)^2*logActivity lam^2)

theorem T0_hasDerivAt_activity {D lam : ℝ} (hD : 0<D) (hlam : 0<lam) (y : ℝ) :
    HasDerivAt (fun a => T0 D a y) (T0ActivitySlope D lam y) lam := by
  have h1 : 1+lam ≠ 0 := ne_of_gt (by linarith)
  have hb := (logActivity_pos hlam).ne'
  have hq := (q_pos hlam).ne'
  have he : exp y+lam ≠ 0 := ne_of_gt (by positivity)
  unfold T0
  apply (((((message_hasDerivAt_activity hlam y).div (q_hasDerivAt hlam) hq).sub_const 1).div_const D).add
    ((hasDerivAt_const lam ((7/12:ℝ)*(y*exp y))).div
      (((hasDerivAt_id lam).const_add 1).mul (logActivity_hasDerivAt hlam))
      (mul_ne_zero h1 hb))).congr_deriv
  rw [message_eq_exp_quotient hlam]
  unfold T0ActivitySlope q
  (try dsimp) <;> (try simp only [id_eq, Pi.pow_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply]) <;> field_simp [hD.ne', hlam.ne', h1, hb, he] <;> ring

theorem T0ActivitySlope_upper {D lam y : ℝ}
    (hD : 0<D) (hlam : 0<lam) (hy : 0≤y) :
    T0ActivitySlope D lam y ≤ y*exp y/(1+lam)^2 *
      (1/D-7*(logActivity lam+1)/(12*logActivity lam^2)) := by
  have he : 1≤exp y := by simpa using Real.exp_le_exp.mpr hy
  have hlog := Real.log_le_sub_one_of_pos (Real.exp_pos (-y))
  rw [Real.log_exp] at hlog
  have hm := mul_le_mul_of_nonneg_right (show 1-exp (-y)≤y by linarith)
    (Real.exp_pos y).le
  have hrec : exp (-y)*exp y=1 := by rw [← Real.exp_add]; simp
  have hnum : exp y-1≤y*exp y := by nlinarith only [hm, hrec]
  have hfirst : (exp y-1)/(D*(exp y+lam)^2) ≤
      y*exp y/(D*(1+lam)^2) := by
    apply div_le_div₀ (by positivity) hnum (by positivity)
    have hs : (1+lam)^2≤(exp y+lam)^2 := by nlinarith
    exact mul_le_mul_of_nonneg_left hs hD.le
  have hi : y*exp y/(1+lam)^2*(1/D-7*(logActivity lam+1)/(12*logActivity lam^2)) =
      y*exp y/(D*(1+lam)^2) -
        (7/12:ℝ)*y*exp y*(logActivity lam+1)/((1+lam)^2*logActivity lam^2) := by
    field_simp [hD.ne', (logActivity_pos hlam).ne',
      ne_of_gt (show 0<1+lam by linarith)]
    <;> ring
  rw [hi]
  unfold T0ActivitySlope
  linarith

theorem T0ActivitySlope_nonpos {D lam y : ℝ}
    (hD : (6/5:ℝ)≤D) (hlam : 0<lam) (hlam7 : lam≤7/3) (hy : 0≤y) :
    T0ActivitySlope D lam y ≤ 0 := by
  have hD0 : 0<D := by linarith
  have hb := logActivity_pos hlam
  have hb5 := logActivity_lt_five_fourths hlam hlam7
  have hcost : (21/25:ℝ) ≤ 7*(logActivity lam+1)/(12*logActivity lam^2) := by
    apply (le_div_iff₀ (by positivity : 0<12*logActivity lam^2)).2
    have hf := mul_nonneg (show 0≤5/4-logActivity lam by linarith)
      (show 0≤252*logActivity lam+140 by positivity)
    nlinarith
  have hDinv : 1/D≤(5/6:ℝ) := (div_le_iff₀ hD0).2 (by linarith)
  have hbr : 1/D-7*(logActivity lam+1)/(12*logActivity lam^2)≤0 := by linarith
  have hh := T0ActivitySlope_upper hD0 hlam hy
  exact hh.trans (mul_nonpos_of_nonneg_of_nonpos (by positivity) hbr)

theorem T0_antitone_activity {D y : ℝ} (hD : (6/5:ℝ)≤D) (hy : 0≤y) :
    AntitoneOn (fun a => T0 D a y) (Ioc 0 (7/3)) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioc 0 (7/3))
    (f' := fun a => T0ActivitySlope D a y)
  · intro a ha
    exact (T0_hasDerivAt_activity (by linarith) ha.1 y).continuousAt.continuousWithinAt
  · intro a ha
    have hh := interior_subset ha
    exact (T0_hasDerivAt_activity (by linarith) hh.1 y).hasDerivWithinAt
  · intro a ha
    have hh := interior_subset ha
    exact T0ActivitySlope_nonpos hD hh.1 hh.2 hy

end Erdos993Lean.Analytic.V213.FreeCountVariance

#check Erdos993Lean.Analytic.V213.FreeCountVariance.scalarH_add_self_monotone
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.scalarH_add_self_monotone
#check Erdos993Lean.Analytic.V213.FreeCountVariance.rho_activity_deriv_nonpos
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.rho_activity_deriv_nonpos
#check Erdos993Lean.Analytic.V213.FreeCountVariance.rho_antitone_activity
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.rho_antitone_activity
#check Erdos993Lean.Analytic.V213.FreeCountVariance.beta_div_activity_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.beta_div_activity_hasDerivAt
#check Erdos993Lean.Analytic.V213.FreeCountVariance.beta_div_activity_deriv_nonpos
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.beta_div_activity_deriv_nonpos
#check Erdos993Lean.Analytic.V213.FreeCountVariance.betaRatio_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.betaRatio_hasDerivAt
#check Erdos993Lean.Analytic.V213.FreeCountVariance.betaRatio_deriv_nonpos
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.betaRatio_deriv_nonpos
#check Erdos993Lean.Analytic.V213.FreeCountVariance.beta_div_activity_antitone
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.beta_div_activity_antitone
#check Erdos993Lean.Analytic.V213.FreeCountVariance.betaRatio_antitone
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.betaRatio_antitone
#check Erdos993Lean.Analytic.V213.FreeCountVariance.logActivity_lt_five_fourths
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.logActivity_lt_five_fourths
#check Erdos993Lean.Analytic.V213.FreeCountVariance.T0_hasDerivAt_activity
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.T0_hasDerivAt_activity
#check Erdos993Lean.Analytic.V213.FreeCountVariance.T0ActivitySlope_upper
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.T0ActivitySlope_upper
#check Erdos993Lean.Analytic.V213.FreeCountVariance.T0ActivitySlope_nonpos
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.T0ActivitySlope_nonpos
#check Erdos993Lean.Analytic.V213.FreeCountVariance.T0_antitone_activity
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.T0_antitone_activity
