module

public import Erdos993Lean.Analytic.V213.ZeroTiltLaplaceXElimination

/-! Actual diagonal curvature bound from current T2a Section4.4.
The weighted reciprocal-square inequality is proved by a rational square
identity instead of cube roots. No finite coefficient table is used. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace

open Real Set

noncomputable def diagonalC (lam : ℝ) : ℝ :=
  (1-a lam)*(1-(q lam)^2)-a lam*w lam
noncomputable def diagonalBaseSlope (lam p : ℝ) : ℝ :=
  (1-a lam*(1+w lam))/(1-p)-(1-a lam)*q lam/(1-q lam*p)-a lam/p-
    ellH lam*(1+q lam)/(q lam*(1+q lam-q lam*p)^2)
noncomputable def diagonalBaseCurvature (lam p : ℝ) : ℝ :=
  (1-a lam*(1+w lam))/(1-p)^2-(1-a lam)*(q lam)^2/(1-q lam*p)^2+
    a lam/p^2-2*ellH lam*(1+q lam)/(1+q lam-q lam*p)^3
noncomputable def diagonalRightSlope (lam p : ℝ) : ℝ :=
  diagonalBaseSlope lam p+a lam*w lam*q lam/(p*(q lam-p))

theorem cubic_denominator_bound {q : ℝ} (hq : QDomain q) :
    1+q≤(1+q-q^2)^3 := by
  have hq0 : 0≤q := by linarith [hq.1]
  have hs : q^2≤(49/100:ℝ) := by nlinarith [hq.2]
  have hb : 0≤5-(23/10:ℝ)*(q^2+49/100) := by linarith
  have hprod := mul_nonneg (sub_nonneg.mpr hs) hb
  have hlast := mul_nonneg (show 0≤7/10-q by linarith [hq.2]) (pow_nonneg hq0 4)
  have hid : 2-5*q^2+3*q^4-q^5-(10223/100000:ℝ)=
      (49/100-q^2)*(5-(23/10)*(q^2+49/100))+(7/10-q)*q^4 := by ring
  have hf : 0≤2-5*q^2+3*q^4-q^5 := by linarith
  have h := mul_nonneg hq0 hf
  have he : (1+q-q^2)^3-(1+q)=q*(2-5*q^2+3*q^4-q^5) := by ring
  linarith

theorem diagonalC_lower {lam : ℝ} (hlam : ActivityDomain lam) :
    (3879/10000:ℝ)≤diagonalC lam := by
  have hl : 0<lam := by linarith [hlam.1]
  have hq := q_domain hlam
  have hq0 := q_pos hl
  have hq2 : (q lam)^2≤(49/100:ℝ) := by nlinarith [hq.2]
  have ha := a_bounds hlam
  have hw := (w_pos_lt_one hl).1
  have hw3 : w lam≤(3/5:ℝ) := (w_mobius_bounds hl).2.2.trans (wPlus_lt_three_fifths hq).le
  have hA : (89/100:ℝ)≤1-a lam := by linarith
  have hB : (51/100:ℝ)≤1-(q lam)^2 := by linarith
  have hp := mul_le_mul hA hB (by norm_num : (0:ℝ)≤51/100)
    (show 0≤1-a lam by linarith)
  have hm := mul_le_mul ha.2.2.le hw3 hw.le (by norm_num : (0:ℝ)≤11/100)
  unfold diagonalC
  linarith

theorem reciprocal_square_identity {p : ℝ} (hp : 0<p) (hp1 : p<1) :
    (7/25:ℝ)^3/p^2+(18/25:ℝ)^3/(1-p)^2-1=
      (p-7/25)^2*(7/25+(36/25)*p-p^2)/(p^2*(1-p)^2) := by
  field_simp [hp.ne',show 1-p≠0 by linarith] <;> ring

theorem reciprocal_square_lower {p : ℝ} (hp : 0<p) (hp1 : p<1) :
    1≤(7/25:ℝ)^3/p^2+(18/25:ℝ)^3/(1-p)^2 := by
  have hp2 : p^2≤p := by nlinarith [mul_nonneg hp.le (show 0≤1-p by linarith)]
  have hf : 0≤7/25+(36/25)*p-p^2 := by linarith
  have hh := div_nonneg (mul_nonneg (sq_nonneg (p-7/25)) hf) (by positivity : 0≤p^2*(1-p)^2)
  rw [←reciprocal_square_identity hp hp1] at hh
  linarith

theorem diagonal_reciprocal_terms_gt_one {lam p : ℝ} (hlam : ActivityDomain lam)
    (hp : 0<p) (hp1 : p<1) : 1<a lam/p^2+diagonalC lam/(1-p)^2 := by
  have ha : (7/25:ℝ)^3<a lam := by linarith [(a_bounds hlam).1]
  have hc : (18/25:ℝ)^3<diagonalC lam := by linarith [diagonalC_lower hlam]
  have h1 := (div_lt_div_iff_of_pos_right (sq_pos_of_pos hp)).2 ha
  have h2 := (div_lt_div_iff_of_pos_right (sq_pos_of_pos (show 0<1-p by linarith))).2 hc
  linarith [reciprocal_square_lower hp hp1]

theorem diagonal_negative_term_bound {lam p : ℝ} (hlam : ActivityDomain lam)
    (hp : 0≤p) (hpq : p≤q lam) :
    2*ellH lam*(1+q lam)/(1+q lam-q lam*p)^3≤2*ellH lam := by
  have hq := q_domain hlam
  have hl : 0<lam := by linarith [hlam.1]
  have hq0 := q_pos hl
  have hf := (q_factors_pos hq).2.2.2.2.2
  have hd : 1+q lam-(q lam)^2≤1+q lam-q lam*p := by nlinarith
  have hc := pow_le_pow_left₀ hf.le hd 3
  have hbase := cubic_denominator_bound hq
  have hd0 : 0<1+q lam-q lam*p := hf.trans_le hd
  have hell := (activity_rate_bounds hlam).1
  apply (div_le_iff₀ (pow_pos hd0 3)).2
  have hh := mul_le_mul_of_nonneg_left (hbase.trans hc) (by positivity : 0≤2*ellH lam)
  nlinarith only [hh]

theorem diagonalBaseCurvature_gt {lam p : ℝ} (hlam : ActivityDomain lam)
    (hp : 0<p) (hpq : p<q lam) : (1/25:ℝ)<diagonalBaseCurvature lam p := by
  have hl : 0<lam := by linarith [hlam.1]
  have hq0 := q_pos hl
  have hq1 := q_lt_one hl
  have hp1 := hpq.trans hq1
  have h1 : 0<1-p := by linarith
  have h2 : 1-p≤1-q lam*p := by nlinarith
  have h20 : 0<1-q lam*p := h1.trans_le h2
  have hs := pow_le_pow_left₀ h1.le h2 2
  have hfrac : (q lam)^2/(1-q lam*p)^2≤(q lam)^2/(1-p)^2 := by
    apply (div_le_div_iff₀ (pow_pos h20 2) (pow_pos h1 2)).2
    exact mul_le_mul_of_nonneg_left hs (sq_nonneg _)
  have ha : 0≤1-a lam := by linarith [(a_bounds hlam).2.2]
  have hloss := mul_le_mul_of_nonneg_left hfrac ha
  have hrec := diagonal_reciprocal_terms_gt_one hlam hp hp1
  have hneg := diagonal_negative_term_bound hlam hp.le hpq.le
  have hell := (activity_rate_bounds hlam).2.2.1
  have hid : (1-a lam*(1+w lam))/(1-p)^2-(1-a lam)*(q lam)^2/(1-p)^2=
      diagonalC lam/(1-p)^2 := by unfold diagonalC; ring
  unfold diagonalBaseCurvature
  have hbound : diagonalC lam/(1-p)^2≤
      (1-a lam*(1+w lam))/(1-p)^2-(1-a lam)*(q lam)^2/(1-q lam*p)^2 := by
    rw [←hid]
    simpa only [mul_div_assoc] using sub_le_sub_left hloss ((1-a lam*(1+w lam))/(1-p)^2)
  linarith

theorem hasDerivAt_diagonalBaseSlope {lam p : ℝ} (hlam : ActivityDomain lam)
    (hp : 0<p) (hpq : p<q lam) :
    HasDerivAt (diagonalBaseSlope lam) (diagonalBaseCurvature lam p) p := by
  have hl : 0<lam := by linarith [hlam.1]
  have hq := q_pos hl
  have hq1 := q_lt_one hl
  have h1 : 0<1-p := by linarith [hpq]
  have h2 : 0<1-q lam*p := by nlinarith
  have h3 : 0<1+q lam-q lam*p := by linarith
  have hd1 := (hasDerivAt_id p).const_sub 1
  have hd2 := ((hasDerivAt_id p).const_mul (q lam)).const_sub 1
  have hd3 := ((hasDerivAt_id p).const_mul (q lam)).const_sub (1+q lam)
  have ha := (hasDerivAt_const p (1-a lam*(1+w lam))).div hd1 h1.ne'
  have hb := (hasDerivAt_const p ((1-a lam)*q lam)).div hd2 h2.ne'
  have hc := (hasDerivAt_const p (a lam)).div (hasDerivAt_id p) hp.ne'
  have hd := (hasDerivAt_const p (ellH lam*(1+q lam))).div
    ((hd3.pow 2).const_mul (q lam)) (by positivity : q lam*(1+q lam-q lam*p)^2≠0)
  convert ((ha.sub hb).sub hc).sub hd using 1 <;>
    (try funext x) <;>
    simp only [diagonalBaseSlope,diagonalBaseCurvature,Pi.sub_apply,Pi.mul_apply,
      Pi.div_apply,Pi.pow_apply,id_eq,Nat.reduceSub,Nat.cast_ofNat,
      pow_succ,pow_zero,mul_one,one_mul,zero_mul,sub_zero,zero_div] <;>
    generalize hqval : q lam=qv at hq h2 h3 ⊢ <;>
    generalize ht2 : 1-qv*p=t2 at h2 ⊢ <;>
    generalize ht3 : 1+qv-qv*p=t3 at h3 ⊢ <;>
    field_simp [hq.ne',hp.ne',h1.ne',h2.ne',h3.ne'] <;> ring

theorem diagonalBaseSlope_monotone {lam : ℝ} (hlam : ActivityDomain lam) :
    MonotoneOn (diagonalBaseSlope lam) (Ioo 0 (q lam)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioo 0 _)
  · intro p hp
    exact (hasDerivAt_diagonalBaseSlope hlam hp.1 hp.2).continuousAt.continuousWithinAt
  · intro p hp
    have hm := interior_subset hp
    exact (hasDerivAt_diagonalBaseSlope hlam hm.1 hm.2).differentiableAt.differentiableWithinAt
  · intro p hp
    have hm := interior_subset hp
    rw [(hasDerivAt_diagonalBaseSlope hlam hm.1 hm.2).deriv]
    exact le_of_lt ((by norm_num : (0:ℝ)<1/25).trans (diagonalBaseCurvature_gt hlam hm.1 hm.2))

end Erdos993Lean.Analytic.V213.ZeroTiltLaplace

--
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.cubic_denominator_bound
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.cubic_denominator_bound
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.diagonalC_lower
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.diagonalC_lower
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.reciprocal_square_identity
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.reciprocal_square_identity
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.reciprocal_square_lower
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.reciprocal_square_lower
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.diagonal_reciprocal_terms_gt_one
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.diagonal_reciprocal_terms_gt_one
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.diagonal_negative_term_bound
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.diagonal_negative_term_bound
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.diagonalBaseCurvature_gt
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.diagonalBaseCurvature_gt
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.hasDerivAt_diagonalBaseSlope
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.hasDerivAt_diagonalBaseSlope
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.diagonalBaseSlope_monotone
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.diagonalBaseSlope_monotone
