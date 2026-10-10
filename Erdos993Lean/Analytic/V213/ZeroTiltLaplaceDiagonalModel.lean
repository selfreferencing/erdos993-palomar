module

public import Erdos993Lean.Analytic.V213.ZeroTiltLaplaceSmallParent
public import Erdos993Lean.Analytic.V213.ZeroTiltLaplaceDiagonalCurvature

/-! Actual diagonal and its two smooth nonleaf formulas. The leaf p=q is
kept outside these identities: its H is assigned zero. Both formulas agree
with the actual diagonal at p0, so no continuity across a fake leaf is used. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace

open Real Set

noncomputable def diagonal (lam p : ℝ) : ℝ := unitExpression lam (b p) 0 p
noncomputable def diagonalLeftValue (lam p : ℝ) : ℝ :=
  -(1-a lam*(1+w lam))*log (1-p)-a lam*log p+
  (1-a lam)*log (1-q lam*p)+a lam*log (q lam)-
  ellH lam*p/(q lam*(1+q lam-q lam*p))
noncomputable def diagonalRightValue (lam p : ℝ) : ℝ :=
  diagonalLeftValue lam p+a lam*w lam*log (q lam*p/(q lam-p))

theorem exp_neg_b {p : ℝ} (hp1 : p<1) : exp (-b p)=1-p := by
  simp only [b,neg_neg,Real.exp_log (show 0<1-p by linarith)]

theorem f_b_normalized {lam p : ℝ} (hlam : 0<lam) (hp : 0≤p) (hpq : p<q lam) :
    f lam (b p)=log (1-q lam*p)-log (1-q lam) := by
  have hq := q_pos hlam
  have hq1 := q_lt_one hlam
  have hp1 := hpq.trans hq1
  have h1 : 0<1-q lam := by linarith
  have h2 : 0<1-q lam*p := by nlinarith
  have hid : 1+lam*(1-p)=(1-q lam*p)/(1-q lam) := by
    have ha := activity_from_q hlam
    generalize hqv : q lam=qv at ha h1 ⊢
    rw [ha]
    field_simp [h1.ne'] <;> ring
  simp only [f,exp_neg_b hp1,hid,Real.log_div h2.ne' h1.ne']

theorem Y_log_normalized {lam p : ℝ} (hlam : 0<lam) (hp : 0<p) (hpq : p<q lam) :
    Y lam p=log (q lam)+log (1-p)-log (1-q lam)-log p := by
  have hq := q_pos hlam
  have hp1 := hpq.trans (q_lt_one hlam)
  have h1 : 0<1-q lam := by linarith [q_lt_one hlam]
  have h2 : 0<1-p := by linarith
  have hid : lam*(1-p)/p=(q lam*(1-p))/((1-q lam)*p) := by
    have ha := activity_from_q hlam
    generalize hqv : q lam=qv at ha h1 ⊢
    rw [ha]
    field_simp [h1.ne',hp.ne'] <;> ring
  unfold Y
  rw [hid,Real.log_div (mul_pos hq h2).ne' (mul_pos h1 hp).ne',
    Real.log_mul hq.ne' h2.ne',Real.log_mul h1.ne' hp.ne']
  ring

theorem Bplus_Y_normalized {lam p : ℝ} (hlam : 0<lam) (hp : 0<p) (hpq : p<q lam) :
    Bplus lam (Y lam p)=max (log (q lam*p/(q lam-p))) 0 := by
  have hq := q_pos hlam
  have hq1 := q_lt_one hlam
  have hp1 := hpq.trans hq1
  have h1 : 0<1-q lam := by linarith
  have h2 : 0<q lam-p := by linarith
  have hpSub : 0<1-p := sub_pos.mpr hp1
  have harg : 0<lam*(1-p)/p := by positivity
  have hid : lam/(lam*(1-p)/p-1)=q lam*p/(q lam-p) := by
    have ha := activity_from_q hlam
    generalize hqv : q lam=qv at ha h1 h2 ⊢
    rw [ha]
    field_simp [h1.ne',h2.ne',hp.ne']
    rw [show qv*(1-p)-(1-qv)*p=qv-p by ring]
    exact mul_div_cancel_right₀ qv h2.ne'
  simp only [Bplus,Y,Real.exp_log harg,hid]

theorem diagonal_normalized {lam p : ℝ} (hlam : 0<lam) (hp : 0<p) (hpq : p<q lam) :
    diagonal lam p=diagonalLeftValue lam p+
      a lam*w lam*max (log (q lam*p/(q lam-p))) 0 := by
  have hq := q_pos hlam
  have hp1 := hpq.trans (q_lt_one hlam)
  have hb := b_pos hp hp1
  have h1 : 0<1-q lam := by linarith [q_lt_one hlam]
  have hE : 0<1+q lam-q lam*p := by nlinarith [q_lt_one hlam]
  have hL : activityLog lam=-log (1-q lam) := by
    rw [←b_q_eq_log hlam]; rfl
  have he : E lam (b p)=ellH lam/(q lam*(1+q lam-q lam*p)) := by
    simp only [E,exp_neg_b hp1]
    congr 2 <;> ring
  unfold diagonal unitExpression
  simp only [add_zero,Pi_zero,mul_zero,add_zero]
  rw [show f lam 0=activityLog lam by
    simp only [f,neg_zero,exp_zero,mul_one,activityLog]]
  change b p*(K lam p-(p/b p)*E lam (b p))+(1-a lam)*f lam (b p)-activityLog lam=_
  rw [he,f_b_normalized hlam hp.le hpq,hL]
  unfold K
  rw [H_nonleaf hpq,Bplus_Y_normalized hlam hp hpq,Y_log_normalized hlam hp hpq]
  unfold diagonalLeftValue b
  have hbLog : log (1-p)≠0 := by
    intro hz
    apply hb.ne'
    simp only [b,hz,neg_zero]
  generalize hlogval : log (1-p)=lv at hbLog ⊢
  generalize hqv : q lam=qv at hq hE ⊢
  generalize hEval : 1+qv-qv*p=ev at hE ⊢
  field_simp [hbLog,hq.ne',hE.ne'] <;> ring

theorem parent_ratio_le_one {q p : ℝ} (hq : 0<q) (hp : 0<p) (hpq : p<q)
    (hp0 : p≤pZero q) : q*p/(q-p)≤1 := by
  have hh := (le_div_iff₀ (by positivity : 0<1+q)).mp hp0
  apply (div_le_one (by linarith : 0<q-p)).2
  nlinarith

theorem one_le_parent_ratio {q p : ℝ} (hq : 0<q) (hp : 0<p) (hpq : p<q)
    (hp0 : pZero q≤p) : 1≤q*p/(q-p) := by
  have hh := (div_le_iff₀ (by positivity : 0<1+q)).mp hp0
  apply (le_div_iff₀ (by linarith : 0<q-p)).2
  nlinarith

theorem diagonal_eq_left {lam p : ℝ} (hlam : 0<lam) (hp : 0<p)
    (hp0 : p≤pZero (q lam)) : diagonal lam p=diagonalLeftValue lam p := by
  have hpq := hp0.trans_lt (pZero_pos_lt (q_pos hlam)).2
  have hq0 := q_pos hlam
  have hqp : 0<q lam-p := sub_pos.mpr hpq
  have hlog := Real.log_nonpos (by positivity : 0≤q lam*p/(q lam-p))
    (parent_ratio_le_one (q_pos hlam) hp hpq hp0)
  rw [diagonal_normalized hlam hp hpq,max_eq_right hlog]
  ring

theorem diagonal_eq_right {lam p : ℝ} (hlam : 0<lam) (hp : 0<p) (hpq : p<q lam)
    (hp0 : pZero (q lam)≤p) : diagonal lam p=diagonalRightValue lam p := by
  have hlog := Real.log_nonneg (one_le_parent_ratio (q_pos hlam) hp hpq hp0)
  rw [diagonal_normalized hlam hp hpq,max_eq_left hlog]
  rfl

theorem hasDerivAt_diagonalLeftValue {lam p : ℝ} (hlam : ActivityDomain lam)
    (hp : 0<p) (hpq : p<q lam) :
    HasDerivAt (diagonalLeftValue lam) (diagonalBaseSlope lam p) p := by
  have hl : 0<lam := by linarith [hlam.1]
  have hq := q_pos hl
  have hq1 := q_lt_one hl
  have h1 : 0<1-p := by linarith
  have h2 : 0<1-q lam*p := by nlinarith
  have h3 : 0<1+q lam-q lam*p := by linarith
  have ha := (((hasDerivAt_id p).const_sub 1).log h1.ne').const_mul (-(1-a lam*(1+w lam)))
  have hb := ((hasDerivAt_id p).log hp.ne').const_mul (a lam)
  have hc := ((((hasDerivAt_id p).const_mul (q lam)).const_sub 1).log h2.ne').const_mul (1-a lam)
  have hd := ((hasDerivAt_id p).const_mul (ellH lam)).div
    ((((hasDerivAt_id p).const_mul (q lam)).const_sub (1+q lam)).const_mul (q lam))
    (by positivity : q lam*(1+q lam-q lam*p)≠0)
  have hh := (((ha.sub hb).add hc).add_const (a lam*log (q lam))).sub hd
  convert hh using 1 <;> (try funext t) <;>
    simp only [diagonalLeftValue,diagonalBaseSlope,Pi.add_apply,Pi.sub_apply,
      Pi.mul_apply,Pi.div_apply,id_eq] <;>
    field_simp [hq.ne',hp.ne',h1.ne',h2.ne',h3.ne'] <;> ring

theorem hasDerivAt_diagonalRightValue {lam p : ℝ} (hlam : ActivityDomain lam)
    (hp : 0<p) (hpq : p<q lam) :
    HasDerivAt (diagonalRightValue lam) (diagonalRightSlope lam p) p := by
  have hl : 0<lam := by linarith [hlam.1]
  have hq := q_pos hl
  have hd : 0<q lam-p := by linarith
  have harg : 0<q lam*p/(q lam-p) := by positivity
  have hc := ((((hasDerivAt_id p).const_mul (q lam)).div
    ((hasDerivAt_id p).const_sub (q lam)) hd.ne').log harg.ne').const_mul (a lam*w lam)
  convert (hasDerivAt_diagonalLeftValue hlam hp hpq).add hc using 1 <;> (try funext t) <;>
    simp only [diagonalRightValue,diagonalRightSlope,Pi.add_apply,Pi.sub_apply,
      Pi.mul_apply,Pi.div_apply,id_eq] <;> field_simp [hq.ne',hp.ne',hd.ne'] <;> ring

end Erdos993Lean.Analytic.V213.ZeroTiltLaplace

--
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.exp_neg_b
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.exp_neg_b
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.f_b_normalized
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.f_b_normalized
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.Y_log_normalized
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.Y_log_normalized
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.Bplus_Y_normalized
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.Bplus_Y_normalized
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.diagonal_normalized
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.diagonal_normalized
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.parent_ratio_le_one
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.parent_ratio_le_one
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.one_le_parent_ratio
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.one_le_parent_ratio
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.diagonal_eq_left
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.diagonal_eq_left
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.diagonal_eq_right
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.diagonal_eq_right
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.hasDerivAt_diagonalLeftValue
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.hasDerivAt_diagonalLeftValue
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.hasDerivAt_diagonalRightValue
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.hasDerivAt_diagonalRightValue
