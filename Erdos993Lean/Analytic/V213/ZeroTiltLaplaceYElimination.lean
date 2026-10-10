module

public import Erdos993Lean.Analytic.V213.ZeroTiltLaplaceExponentialElimination

/-!
Current T2a equation36: actual elimination of y from the current unit.
The scalar rate bound is the already proved-source Lemma4.2, and F0 is
bounded by the explicit hyperbolic/polynomial alternative in the import.
This file neither assumes the unit inequality nor changes Pi(0)=0.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace

open Real Set

noncomputable def messageAt (lam t : ℝ) : ℝ :=
  lam*exp (-t)/(1+lam*exp (-t))
noncomputable def vExpression (lam x p y : ℝ) : ℝ :=
  x*(K lam p-(p/b p)*E lam (x+y))+(1-a lam)*(f lam (x+y)-f lam y)
noncomputable def yBudget (lam x y : ℝ) : ℝ :=
  (1-a lam)*lam*(exp x-1)/x*
    eliminationQuotient (q lam) (lam*exp x) lam (exp (-x-y))
noncomputable def vSlope (lam x p y : ℝ) : ℝ :=
  (1-a lam)*(messageAt lam y-messageAt lam (x+y))-
    (p/b p)*(x*ellH lam*exp (-(x+y))/(1+q lam*exp (-(x+y)))^2)

theorem p_le_b {p : ℝ} (hp1 : p<1) : p≤b p := by
  have hh := log_le_sub_one_of_pos (show 0<1-p by linarith)
  unfold b
  linarith

theorem p_div_b_le_one {p : ℝ} (hp : 0<p) (hp1 : p<1) : p/b p≤1 := by
  have hb := p_le_b hp1
  exact (div_le_one (hp.trans_le hb)).2 hb

theorem hasDerivAt_f {lam : ℝ} (hlam : 0<lam) (t : ℝ) :
    HasDerivAt (f lam) (-messageAt lam t) t := by
  have hd : 0<1+lam*exp (-t) := by positivity
  have hh := ((((hasDerivAt_id t).neg.exp).const_mul lam).const_add 1).log hd.ne'
  convert hh using 1 <;>
    (try funext s) <;>
    simp only [f, messageAt, id_eq, Pi.neg_apply, Pi.mul_apply, Pi.add_apply] <;>
    field_simp [hd.ne'] <;> ring

theorem hasDerivAt_E {lam : ℝ} (hlam : 0<lam) (t : ℝ) :
    HasDerivAt (E lam) (ellH lam*exp (-t)/(1+q lam*exp (-t))^2) t := by
  have hq := q_pos hlam
  have hd : 0<q lam*(1+q lam*exp (-t)) := by positivity
  have h1 : 0<1+q lam*exp (-t) := by positivity
  have hh := (hasDerivAt_const t (ellH lam)).div
    (((((hasDerivAt_id t).neg.exp).const_mul (q lam)).const_add 1).const_mul (q lam)) hd.ne'
  convert hh using 1 <;>
    (try funext s) <;>
    simp only [E, id_eq, Pi.neg_apply, Pi.mul_apply, Pi.add_apply, Pi.div_apply] <;>
    field_simp [hq.ne',h1.ne'] <;> ring

theorem hasDerivAt_vExpression {lam : ℝ} (hlam : 0<lam) (x p y : ℝ) :
    HasDerivAt (vExpression lam x p) (vSlope lam x p y) y := by
  have he := (hasDerivAt_E hlam (x+y)).comp y ((hasDerivAt_id y).const_add x)
  have hf := (hasDerivAt_f hlam (x+y)).comp y ((hasDerivAt_id y).const_add x)
  have hg := hasDerivAt_f hlam y
  have hh := (((he.const_mul (p/b p)).const_sub (K lam p)).const_mul x).add
    ((hf.sub hg).const_mul (1-a lam))
  convert hh using 1 <;>
    (try funext s) <;>
    simp only [vExpression, vSlope, id_eq, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Function.comp_apply] <;> ring

theorem yBudget_zero {lam x : ℝ} (hlam : 0<lam) (hx : 0<x) :
    yBudget lam x 0=(1-a lam)*q lam*fZero lam x := by
  have hx0 := hx.ne'
  have h1 : 0<1+lam := by positivity
  have he : exp x*exp (-x)=1 := by rw [← exp_add]; simp
  have ha : 1+lam*exp x*exp (-x)=1+lam := by
    calc
      1+lam*exp x*exp (-x)=1+lam*(exp x*exp (-x)) := by ring
      _=1+lam := by rw [he]; ring
  have hb : 0<1+lam*exp (-x) := by positivity
  unfold yBudget eliminationQuotient fZero
  simp only [sub_zero]
  rw [ha]
  unfold q
  field_simp [hx0,h1.ne',hb.ne'] <;> ring

theorem yBudget_ge_rate {lam x y : ℝ} (hlam : ActivityDomain lam)
    (hx : 0<x) (hy : 0≤y) : ellH lam≤yBudget lam x y := by
  have hl : 0<lam := by linarith [hlam.1]
  have hq := q_pos hl
  have ha := a_bounds hlam
  have h1a : 0≤1-a lam := by linarith
  have hqLam : q lam≤lam := by
    unfold q
    apply (div_le_iff₀ (show 0<1+lam by positivity)).2
    nlinarith [sq_nonneg lam]
  have hex : 1≤exp x := by simpa only [exp_zero] using (exp_le_exp.mpr hx.le : exp 0≤exp x)
  have hlex : lam≤lam*exp x := by nlinarith
  have hzr : exp (-x-y)≤exp (-x) := exp_le_exp.mpr (by linarith)
  have hquo := eliminationQuotient_antitone hq.le (hqLam.trans hlex) hqLam
    (exp_pos (-x-y)).le hzr
  have hexsub : 0≤exp x-1 := sub_nonneg.mpr hex
  have hc : 0≤(1-a lam)*lam*(exp x-1)/x := by positivity
  have hstep := mul_le_mul_of_nonneg_left hquo hc
  have hf := mul_le_mul_of_nonneg_left (fZero_lower hl hx)
    (show 0≤(1-a lam)*q lam by positivity)
  have hr := (activity_rate_bounds hlam).2.2.2
  calc
    ellH lam≤(1-a lam)*q lam*(1-q lam)*(1+q lam)^2 := hr
    _≤(1-a lam)*q lam*fZero lam x := by convert hf using 1 <;> ring
    _=yBudget lam x 0 := (yBudget_zero hl hx).symm
    _≤yBudget lam x y := by simpa only [yBudget,sub_zero] using hstep

/-- The cleared derivative comparison. All divisions have positive factors;
only the already proved scalar budget and p/b<=1 are used. -/
theorem slope_nonnegative_of_budget {a ell lam q e z x r : ℝ}
    (hx : 0<x) (hlam : 0<lam) (hq : 0≤q) (he : 0<e) (hz : 0<z)
    (hell : 0≤ell) (hr : r≤1)
    (hb : ell≤(1-a)*lam*(e-1)/x*eliminationQuotient q (lam*e) lam z) :
    0≤(1-a)*(lam*e*z/(1+lam*e*z)-lam*z/(1+lam*z))-
      r*(x*ell*z/(1+q*z)^2) := by
  have hs : 0<1+q*z := by positivity
  have hd1 : 0<1+lam*e*z := by positivity
  have hd2 : 0<1+lam*z := by positivity
  have hmul := mul_le_mul_of_nonneg_right hb (show 0≤x*z/(1+q*z)^2 by positivity)
  have hloss : 0≤x*ell*z/(1+q*z)^2 := by positivity
  have hsmall := mul_le_mul_of_nonneg_right hr hloss
  have hgain : x*ell*z/(1+q*z)^2≤
      (1-a)*(lam*e*z/(1+lam*e*z)-lam*z/(1+lam*z)) := by
    unfold eliminationQuotient at hmul
    convert hmul using 1 <;>
      field_simp [hx.ne',hs.ne',hd1.ne',hd2.ne'] <;> ring
  nlinarith only [hgain,hsmall]

theorem vSlope_nonnegative {lam x p y : ℝ} (hlam : ActivityDomain lam)
    (hx : 0<x) (hp : 0<p) (hpq : p≤q lam) (hy : 0≤y) :
    0≤vSlope lam x p y := by
  have hl : 0<lam := by linarith [hlam.1]
  have hp1 : p<1 := hpq.trans_lt (q_lt_one hl)
  have hr := slope_nonnegative_of_budget hx hl (q_pos hl).le (exp_pos x)
    (exp_pos (-x-y)) (activity_rate_bounds hlam).1.le
    (p_div_b_le_one hp hp1) (yBudget_ge_rate hlam hx hy)
  have he : exp x*exp (-x-y)=exp (-y) := by
    rw [← exp_add]
    congr 1
    ring
  have hz : exp (-(x+y))=exp (-x-y) := by congr 1 <;> ring
  unfold vSlope messageAt
  rw [hz]
  simpa only [mul_assoc, he] using hr

theorem vExpression_monotone_y {lam x p : ℝ} (hlam : ActivityDomain lam)
    (hx : 0<x) (hp : 0<p) (hpq : p≤q lam) :
    MonotoneOn (vExpression lam x p) (Ici 0) := by
  have hl : 0<lam := by linarith [hlam.1]
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
  · exact fun y _ => (hasDerivAt_vExpression hl x p y).continuousAt.continuousWithinAt
  · exact fun y _ => (hasDerivAt_vExpression hl x p y).differentiableAt.differentiableWithinAt
  · intro y hy
    rw [(hasDerivAt_vExpression hl x p y).deriv]
    exact vSlope_nonnegative hlam hx hp hpq (interior_subset hy)

theorem unit_ge_v {lam x p y : ℝ} (hlam : ActivityDomain lam) (hy : 0<y) :
    vExpression lam x p y≤unitExpression lam x y p := by
  have ha : 0≤a lam := by linarith [(a_bounds hlam).1]
  have hm := mul_nonneg ha (sub_nonneg.mpr (Pi_ge_f hlam hy))
  unfold vExpression unitExpression
  nlinarith only [hm]

theorem vExpression_zero (lam x p : ℝ) :
    vExpression lam x p 0=unitExpression lam x 0 p+a lam*activityLog lam := by
  simp only [vExpression,unitExpression,Pi_zero,f,activityLog,add_zero,neg_zero,exp_zero,mul_one]
  ring

/-- Literal current equation36, on its strict y>0 branch. The exceptional
assigned value Pi(0)=0 accounts for the added a*log(1+lambda). -/
theorem eliminate_y {lam x p y : ℝ} (hlam : ActivityDomain lam)
    (hx : 0<x) (hp : 0<p) (hpq : p≤q lam) (hy : 0<y) :
    unitExpression lam x 0 p+a lam*activityLog lam≤unitExpression lam x y p := by
  have hv := vExpression_monotone_y hlam hx hp hpq
    (show (0:ℝ) ∈ Ici 0 from by change (0:ℝ) ≤ 0; exact le_rfl) (show y ∈ Ici 0 from hy.le) hy.le
  rw [vExpression_zero] at hv
  exact hv.trans (unit_ge_v hlam hy)

end Erdos993Lean.Analytic.V213.ZeroTiltLaplace

-- Audit commands.
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.p_le_b
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.p_le_b
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.p_div_b_le_one
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.p_div_b_le_one
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.hasDerivAt_f
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.hasDerivAt_f
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.hasDerivAt_E
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.hasDerivAt_E
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.hasDerivAt_vExpression
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.hasDerivAt_vExpression
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.yBudget_zero
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.yBudget_zero
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.yBudget_ge_rate
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.yBudget_ge_rate
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.slope_nonnegative_of_budget
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.slope_nonnegative_of_budget
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.vSlope_nonnegative
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.vSlope_nonnegative
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.vExpression_monotone_y
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.vExpression_monotone_y
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.unit_ge_v
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.unit_ge_v
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.vExpression_zero
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.vExpression_zero
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.eliminate_y
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.eliminate_y
