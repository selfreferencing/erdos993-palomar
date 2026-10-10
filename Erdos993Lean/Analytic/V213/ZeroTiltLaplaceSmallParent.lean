module

public import Erdos993Lean.Analytic.V213.ZeroTiltLaplaceXElimination

/-! Actual small-p reduction in current T2a Section4.3. The active nonleaf
formula H=Y is proved for 0<p<=p0. No continuity at the assigned leaf H(q)=0
is used. All bounds are analytic/rational; no finite table is consumed. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace

open Real Set

noncomputable def smallParentTerm (lam x p : ℝ) : ℝ :=
  (a lam*Y lam p-E lam x*p)/b p
noncomputable def smallParentSlope (lam x p : ℝ) : ℝ :=
  (-a lam*(b p/p+Y lam p)+E lam x*(p-(1-p)*b p))/((1-p)*(b p)^2)

theorem pZero_pos_lt {q : ℝ} (hq : 0<q) : 0<pZero q ∧ pZero q<q := by
  have hd : 0<1+q := by positivity
  refine ⟨by unfold pZero; positivity,?_⟩
  unfold pZero
  apply (div_lt_iff₀ hd).2
  nlinarith [sq_pos_of_pos hq]

theorem pZero_activity {lam : ℝ} (hlam : 0<lam) :
    pZero (q lam)=lam/(1+2*lam) := by
  unfold pZero q
  field_simp [show 1+lam≠0 by positivity,show 1+2*lam≠0 by positivity] <;> ring

theorem b_q_eq_log {lam : ℝ} (hlam : 0<lam) : b (q lam)=activityLog lam := by
  have hi : 1-q lam=(1+lam)⁻¹ := by
    unfold q
    field_simp [show 1+lam≠0 by positivity] <;> ring
  rw [b,hi,Real.log_inv]
  simp only [neg_neg,activityLog]

theorem logActivity_ge_q {lam : ℝ} (hlam : 0<lam) : q lam≤activityLog lam := by
  rw [←b_q_eq_log hlam]
  exact p_le_b (q_lt_one hlam)

theorem Y_ge_logActivity_small {lam p : ℝ} (hlam : 0<lam) (hp : 0<p)
    (hp0 : p≤pZero (q lam)) : activityLog lam≤Y lam p := by
  have hpa : p*(1+2*lam)≤lam := by
    rw [pZero_activity hlam] at hp0
    exact (le_div_iff₀ (by positivity : 0<1+2*lam)).mp hp0
  unfold activityLog Y
  apply Real.log_le_log (by positivity)
  apply (le_div_iff₀ hp).2
  nlinarith

theorem Bplus_zero_above_log {lam t : ℝ} (hlam : 0<lam)
    (ht : activityLog lam≤t) : Bplus lam t=0 := by
  have hE : 1+lam≤exp t := by
    have hh := Real.exp_le_exp.mpr ht
    simpa only [activityLog,Real.exp_log (by positivity : 0<1+lam)] using hh
  have hd : 0<exp t-1 := by linarith
  have hl : log (lam/(exp t-1))≤0 := Real.log_nonpos
    (by positivity) ((div_le_one hd).2 (by linarith))
  exact max_eq_right hl

theorem H_eq_Y_small {lam p : ℝ} (hlam : 0<lam) (hp : 0<p)
    (hp0 : p≤pZero (q lam)) : H lam p=Y lam p := by
  have hpq := hp0.trans_lt (pZero_pos_lt (q_pos hlam)).2
  rw [H_nonleaf hpq,Bplus_zero_above_log hlam (Y_ge_logActivity_small hlam hp hp0)]
  ring

theorem E_bounds {lam : ℝ} (hlam : ActivityDomain lam) (x : ℝ) :
    0≤E lam x ∧ E lam x≤1 := by
  have hl : 0<lam := by linarith [hlam.1]
  have hq := q_pos hl
  have hell := activity_rate_bounds hlam
  have hell0 : 0≤ellH lam := hell.1.le
  have hd : 0<q lam*(1+q lam*exp (-x)) := by positivity
  unfold E
  refine ⟨by positivity,(div_le_one hd).2 ?_⟩
  have hp := mul_nonneg hq.le (exp_pos (-x)).le
  nlinarith [hell.2.1]

theorem hasDerivAt_b {p : ℝ} (hp1 : p<1) : HasDerivAt b (1/(1-p)) p := by
  have h := (((hasDerivAt_id p).const_sub 1).log (show 1-p≠0 by linarith)).neg
  convert h using 1 <;> (try funext t) <;> simp only [b,Pi.neg_apply,Pi.sub_apply,id_eq] <;> ring

theorem hasDerivAt_Y {lam p : ℝ} (hlam : 0<lam) (hp : 0<p) (hp1 : p<1) :
    HasDerivAt (Y lam) (-1/(p*(1-p))) p := by
  have h1 : 0<1-p := by linarith
  have hd : 0<lam*(1-p)/p := by positivity
  have h := ((((hasDerivAt_id p).const_sub 1).const_mul lam).div
    (hasDerivAt_id p) hp.ne').log hd.ne'
  convert h using 1 <;> (try funext t) <;>
    simp only [Y,Pi.div_apply,Pi.mul_apply,Pi.sub_apply,id_eq] <;>
    field_simp [hlam.ne',hp.ne',h1.ne'] <;> ring

theorem hasDerivAt_smallParentTerm {lam p : ℝ} (hlam : 0<lam) (hp : 0<p)
    (hp1 : p<1) (x : ℝ) :
    HasDerivAt (smallParentTerm lam x) (smallParentSlope lam x p) p := by
  have hb := b_pos hp hp1
  have h := (((hasDerivAt_Y hlam hp hp1).const_mul (a lam)).sub
    ((hasDerivAt_id p).const_mul (E lam x))).div (hasDerivAt_b hp1) hb.ne'
  convert h using 1 <;> (try funext t) <;>
    simp only [smallParentTerm,smallParentSlope,Pi.div_apply,Pi.mul_apply,Pi.sub_apply,id_eq] <;>
    field_simp [hp.ne',hb.ne',show 1-p≠0 by linarith] <;> ring

theorem entropy_remainder_bounds {p : ℝ} (hp : 0<p) (hp1 : p<1) :
    0≤p-(1-p)*b p ∧ p-(1-p)*b p≤p^2/(2-p) := by
  have hm : 0<1-p := by linarith
  have h2 : 0<2-p := by linarith
  have hu : b p≤p/(1-p) := FreeCountVariance.Envelopes.scalarLog_upper hp hp1
  have hl : 2*p/(2-p)≤b p := FreeCountVariance.Envelopes.scalarLog_lower hp hp1
  have hu' := (le_div_iff₀ hm).mp hu
  have hl' := mul_le_mul_of_nonneg_left hl hm.le
  refine ⟨by nlinarith [hu'],?_⟩
  calc
    p-(1-p)*b p≤p-(1-p)*(2*p/(2-p)) := by linarith
    _=p^2/(2-p) := by field_simp [h2.ne'] <;> ring

theorem square_div_two_sub_mono {p r : ℝ} (hp : 0≤p) (hpr : p≤r) (hr1 : r<1) :
    p^2/(2-p)≤r^2/(2-r) := by
  have hp2 : 0<2-p := by linarith
  have hr2 : 0<2-r := by linarith
  have hr : 0≤r := hp.trans hpr
  have hfactor : 0≤2*r+2*p-p*r := by
    have hprod := mul_nonneg hp (show 0≤2-r by linarith)
    nlinarith
  have h := mul_nonneg (sub_nonneg.mpr hpr) hfactor
  apply (div_le_div_iff₀ hp2 hr2).2
  nlinarith only [h]

theorem smallParentSlope_negative {lam p : ℝ} (hlam : ActivityDomain lam)
    (hp : 0<p) (hp0 : p≤pZero (q lam)) (x : ℝ) : smallParentSlope lam x p<0 := by
  have hl : 0<lam := by linarith [hlam.1]
  have hq := q_pos hl
  have hpq := hp0.trans_lt (pZero_pos_lt hq).2
  have hp1 := hpq.trans (q_lt_one hl)
  have hr1 := (pZero_pos_lt hq).2.trans (q_lt_one hl)
  have hb := b_pos hp hp1
  have ha : 0<a lam := by linarith [(a_bounds hlam).1]
  have hbp : 1≤b p/p := (le_div_iff₀ hp).2 (by simpa using p_le_b hp1)
  have hY : q lam≤Y lam p := (logActivity_ge_q hl).trans (Y_ge_logActivity_small hl hp hp0)
  have hs := entropy_remainder_bounds hp hp1
  have he := E_bounds hlam x
  have heprod := mul_le_mul_of_nonneg_right he.2 hs.1
  have hrem := hs.2.trans (square_div_two_sub_mono hp.le hp0 hr1)
  have hgood := small_parent_sufficient_condition (q_domain hlam)
  rw [←a_eq_aQ hl] at hgood
  have hagain := mul_le_mul_of_nonneg_left (add_le_add hbp hY) ha.le
  have hnum : -a lam*(b p/p+Y lam p)+E lam x*(p-(1-p)*b p)<0 := by
    nlinarith only [heprod,hrem,hgood,hagain]
  have h1 : 0<1-p := by linarith
  exact div_neg_of_neg_of_pos hnum (by positivity : 0<(1-p)*(b p)^2)

theorem smallParentTerm_antitone {lam : ℝ} (hlam : ActivityDomain lam) (x : ℝ) :
    AntitoneOn (smallParentTerm lam x) (Ioc 0 (pZero (q lam))) := by
  have hl : 0<lam := by linarith [hlam.1]
  have htop := (pZero_pos_lt (q_pos hl)).2.trans (q_lt_one hl)
  apply antitoneOn_of_deriv_nonpos (convex_Ioc 0 _)
  · intro p hp
    exact (hasDerivAt_smallParentTerm hl hp.1 (hp.2.trans_lt htop) x).continuousAt.continuousWithinAt
  · intro p hp
    have hm := interior_subset hp
    exact (hasDerivAt_smallParentTerm hl hm.1 (hm.2.trans_lt htop) x).differentiableAt.differentiableWithinAt
  · intro p hp
    have hm := interior_subset hp
    rw [(hasDerivAt_smallParentTerm hl hm.1 (hm.2.trans_lt htop) x).deriv]
    exact (smallParentSlope_negative hlam hm.1 hm.2 x).le

theorem unit_zero_small_form {lam p : ℝ} (hlam : 0<lam) (hp : 0<p)
    (hp0 : p≤pZero (q lam)) (x : ℝ) :
    unitExpression lam x 0 p=x*(1-a lam*w lam)+x*smallParentTerm lam x p+
      (1-a lam)*f lam x-activityLog lam := by
  simp only [unitExpression,K,Pi_zero,mul_zero,add_zero,H_eq_Y_small hlam hp hp0,
    f,neg_zero,exp_zero,mul_one,activityLog,smallParentTerm]
  ring

/-- For fixed nonnegative x, increasing a small parent lowers the actual unit. -/
theorem unit_antitone_small_parent {lam x p r : ℝ} (hlam : ActivityDomain lam)
    (hx : 0≤x) (hp : 0<p) (hpr : p≤r) (hr0 : r≤pZero (q lam)) :
    unitExpression lam x 0 r≤unitExpression lam x 0 p := by
  have hl : 0<lam := by linarith [hlam.1]
  have hr : 0<r := hp.trans_le hpr
  have h := smallParentTerm_antitone hlam x ⟨hp,hpr.trans hr0⟩ ⟨hr,hr0⟩ hpr
  have hh := mul_le_mul_of_nonneg_left h hx
  rw [unit_zero_small_form hl hp (hpr.trans hr0),unit_zero_small_form hl hr hr0]
  linarith

end Erdos993Lean.Analytic.V213.ZeroTiltLaplace

-- Current small-parent reduction.
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.pZero_pos_lt
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.pZero_pos_lt
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.pZero_activity
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.pZero_activity
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.b_q_eq_log
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.b_q_eq_log
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.logActivity_ge_q
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.logActivity_ge_q
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.Y_ge_logActivity_small
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.Y_ge_logActivity_small
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.Bplus_zero_above_log
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.Bplus_zero_above_log
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.H_eq_Y_small
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.H_eq_Y_small
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.E_bounds
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.E_bounds
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.hasDerivAt_b
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.hasDerivAt_b
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.hasDerivAt_Y
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.hasDerivAt_Y
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.hasDerivAt_smallParentTerm
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.hasDerivAt_smallParentTerm
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.entropy_remainder_bounds
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.entropy_remainder_bounds
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.square_div_two_sub_mono
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.square_div_two_sub_mono
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.smallParentSlope_negative
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.smallParentSlope_negative
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.smallParentTerm_antitone
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.smallParentTerm_antitone
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.unit_zero_small_form
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.unit_zero_small_form
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.unit_antitone_small_parent
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.unit_antitone_small_parent
