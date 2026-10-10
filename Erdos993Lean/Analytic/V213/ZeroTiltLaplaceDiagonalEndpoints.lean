module

public import Erdos993Lean.Analytic.V213.ZeroTiltLaplaceDiagonalMinimum

/-! Actual center and assigned-leaf values. No nonleaf limit is used at p=q.
Only the literal PE sign is consumed below; all logarithmic estimates are proved. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace
open Real Set

theorem log_two_terms {t : ℝ} (ht : 0≤t) :
    2*t/(2+t)+2*t^3/(3*(2+t)^3)≤log (1+t) := by
  let z:=t/(2+t)
  have hd : 0<2+t := by positivity
  have hz : 0≤z := by dsimp [z]; positivity
  have hz1 : z<1 := by dsimp [z]; exact (div_lt_one hd).2 (by linarith)
  have hh := Real.sum_range_le_log_div hz hz1 2
  have hid : (1+z)/(1-z)=1+t := by dsimp [z]; field_simp [hd.ne'] <;> ring
  rw [hid] at hh
  norm_num [Finset.sum_range_succ] at hh
  have hform : 2*t/(2+t)+2*t^3/(3*(2+t)^3)=2*(z+z^3/3) := by
    dsimp [z]
    generalize hdval : 2+t=d at hd ⊢
    field_simp [hd.ne'] <;> ring
  rw [hform]
  linarith

theorem activityLog_chord {lam : ℝ} (hlam : 0<lam) :
    activityLog lam≤q lam*(2-q lam)/(2*(1-q lam)) := by
  have h := (FreeCountVariance.Envelopes.log_star hlam.le).2
  have h1 : 0<1-q lam := by linarith [q_lt_one hlam]
  change log (1+lam)≤_
  convert h using 1
  have ha := activity_from_q hlam
  generalize hqval : q lam=qv at ha h1 ⊢
  rw [ha]
  field_simp [h1.ne'] <;> ring

theorem diagonal_center_value {lam : ℝ} (hlam : 0<lam) :
    diagonal lam (pZero (q lam))=
      (1-a lam)*log (1+q lam*(1-q lam))+
      a lam*(1-w lam)*log (1+q lam)-ellH lam/(1+2*q lam) := by
  have hq:=q_pos hlam
  have hq1:=q_lt_one hlam
  have hsub:0<1-q lam:=by linarith
  have hp:=pZero_pos_lt hq
  have h1 : 0<1+q lam := by positivity
  have hz : 0<1+q lam*(1-q lam) := by positivity
  have hc : 0<1+2*q lam := by positivity
  have hpLog : log (pZero (q lam))=log (q lam)-log (1+q lam) := by
    simp only [pZero,Real.log_div hq.ne' h1.ne']
  have h1Log : log (1-pZero (q lam))= -log (1+q lam) := by
    have he : 1-pZero (q lam)=1/(1+q lam) := by
      unfold pZero; field_simp [h1.ne'] <;> ring
    rw [he,Real.log_div (by norm_num : (1:ℝ)≠0) h1.ne',Real.log_one]
    ring
  have hzLog : log (1-q lam*pZero (q lam))=
      log (1+q lam*(1-q lam))-log (1+q lam) := by
    have he : 1-q lam*pZero (q lam)=(1+q lam*(1-q lam))/(1+q lam) := by
      unfold pZero; field_simp [h1.ne'] <;> ring
    rw [he,Real.log_div hz.ne' h1.ne']
  rw [diagonal_eq_left hlam hp.1 le_rfl]
  unfold diagonalLeftValue
  rw [hpLog,h1Log,hzLog]
  have hcenterDen : 1+q lam-q lam*pZero (q lam)=(1+2*q lam)/(1+q lam) := by
    unfold pZero; field_simp [h1.ne'] <;> ring
  rw [hcenterDen]
  unfold pZero
  generalize hqval : q lam=qv at hq h1 hc ⊢
  generalize hcv : 1+2*qv=cv at hc ⊢
  generalize hpv : 1+qv=pv at h1 ⊢
  field_simp [hq.ne',h1.ne',hc.ne'] <;> ring

theorem diagonal_leaf_value {lam : ℝ} (hlam : 0<lam) :
    diagonal lam (q lam)=(1-a lam)*log (1+q lam)-
      a lam*w lam*activityLog lam-ellH lam/(1+q lam-(q lam)^2) := by
  have hq:=q_pos hlam
  have hq1:=q_lt_one hlam
  have hb:=b_pos hq hq1
  have h1 : 0<1-q lam := by linarith
  have h2 : 0<1+q lam := by positivity
  have h3 : 0<1+q lam-(q lam)^2 := by nlinarith [mul_pos hq h1]
  have hL : activityLog lam= -log (1-q lam) := by
    rw [←b_q_eq_log hlam]; rfl
  have hf : f lam (b (q lam))=log (1+q lam) := by
    unfold f
    rw [exp_neg_b hq1]
    have ha := activity_from_q hlam
    generalize hqval : q lam=qv at ha h1 ⊢
    rw [ha]
    congr 1
    field_simp [h1.ne'] <;> ring
  have he : E lam (b (q lam))=ellH lam/(q lam*(1+q lam-(q lam)^2)) := by
    unfold E
    rw [exp_neg_b hq1]
    congr 2 <;> ring
  unfold diagonal unitExpression K
  simp only [add_zero,Pi_zero,H_leaf,mul_zero,zero_div,add_zero]
  rw [hf,he,b_q_eq_log hlam]
  rw [show f lam 0=activityLog lam by
    simp only [f,neg_zero,exp_zero,mul_one,activityLog]]
  change activityLog lam*(1-a lam*w lam-(q lam/activityLog lam)*
    (ellH lam/(q lam*(1+q lam-(q lam)^2))))+
    (1-a lam)*log (1+q lam)-activityLog lam=_
  have hLp : 0<activityLog lam := by rw [←b_q_eq_log hlam]; exact hb
  generalize hqval : q lam=qv at hq h3 ⊢
  generalize hdval : 1+qv-qv^2=dv at h3 ⊢
  field_simp [hq.ne',hLp.ne',h3.ne'] <;> ring

theorem diagonal_center_lower {lam : ℝ} (hlam : ActivityDomain lam) :
    centerC1 (q lam)+centerC2 (q lam)-delta (q lam)≤
      (1+2*q lam)*diagonal lam (pZero (q lam)) := by
  have hl : 0<lam := by linarith [hlam.1]
  have hq:=q_pos hl
  have hq1:=q_lt_one hl
  have ha:0≤a lam:=by linarith [(a_bounds hlam).1]
  have ha1:0≤1-a lam:=by linarith [(a_bounds hlam).2.2]
  have hw:0≤1-wPlus (q lam):=by linarith [wPlus_lt_three_fifths (q_domain hlam)]
  have hlog:0≤log (1+q lam):=Real.log_nonneg (by linarith)
  have h1:=mul_le_mul_of_nonneg_left
    (log_two_terms (mul_nonneg hq.le (show 0≤1-q lam by linarith))) ha1
  have h2:=mul_le_mul_of_nonneg_left (FreeCountVariance.Envelopes.log_star hq.le).1
    (mul_nonneg ha hw)
  have h3:=mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (show 1-wPlus (q lam)≤1-w lam by
      linarith [(w_mobius_bounds hl).2.2]) ha) hlog
  have hlow : centerRationalLower (q lam) (delta (q lam))≤diagonal lam (pZero (q lam)) := by
    rw [diagonal_center_value hl]
    unfold centerRationalLower
    rw [←a_eq_aQ hl]
    unfold ellH rate
    linarith
  have hp:0≤1+2*q lam:=by positivity
  have hmul:=mul_le_mul_of_nonneg_left hlow hp
  rwa [center_rational_clearing (q_domain hlam)] at hmul

theorem diagonal_leaf_lower {lam : ℝ} (hlam : ActivityDomain lam) :
    leafRationalLower (q lam) (delta (q lam))≤diagonal lam (q lam) := by
  have hl : 0<lam := by linarith [hlam.1]
  have hq:=q_pos hl
  have hq1:=q_lt_one hl
  have ha:0≤a lam:=by linarith [(a_bounds hlam).1]
  have ha1:0≤1-a lam:=by linarith [(a_bounds hlam).2.2]
  have hw:0≤w lam:=(w_pos_lt_one hl).1.le
  have hsub1 : 0<1-q lam := sub_pos.mpr hq1
  have hsub2 : 0<2-q lam := by linarith
  have hc:0≤q lam*(2-q lam)/(2*(1-q lam)):=by positivity
  have h1:=mul_le_mul_of_nonneg_left (log_two_terms hq.le) ha1
  have h2:=mul_le_mul_of_nonneg_left (activityLog_chord hl) (mul_nonneg ha hw)
  have h3:=mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (w_mobius_bounds hl).2.2 ha) hc
  rw [diagonal_leaf_value hl]
  unfold leafRationalLower
  rw [←a_eq_aQ hl]
  unfold ellH rate
  convert sub_le_sub_right (sub_le_sub h1 (h2.trans h3))
    ((rateR (q lam)+delta (q lam))/(1+q lam-(q lam)^2)) using 1 <;> ring

theorem diagonal_leaf_nonnegative {lam : ℝ} (hlam : ActivityDomain lam)
    (he : 0≤polyE (q lam) (delta (q lam))) : 0≤diagonal lam (q lam) := by
  have hd:0<deltaE (q lam):=(diagonal_clearing_factors_pos (q_domain hlam)).2
  have hr:0≤leafRationalLower (q lam) (delta (q lam)):=by
    unfold polyE at he
    nlinarith
  exact hr.trans (diagonal_leaf_lower hlam)

end Erdos993Lean.Analytic.V213.ZeroTiltLaplace

--
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.log_two_terms
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.log_two_terms
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.activityLog_chord
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.activityLog_chord
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.diagonal_center_value
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.diagonal_center_value
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.diagonal_leaf_value
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.diagonal_leaf_value
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.diagonal_center_lower
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.diagonal_center_lower
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.diagonal_leaf_lower
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.diagonal_leaf_lower
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.diagonal_leaf_nonnegative
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.diagonal_leaf_nonnegative
