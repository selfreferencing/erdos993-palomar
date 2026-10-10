module

public import Erdos993Lean.Analytic.V213.FreeCountACActivityMonotonicity
public import Erdos993Lean.Analytic.V213.FreeCountVarianceCaps

/-!
Current T1 Section 3.7, the actual large-parent AC argument. All constants are
printed there. This file proves the tail from the two precise
scalar inputs used in that argument: the uniform rate bound and equation (30).
It neither assumes AC positivity nor invokes an old variance-curve theorem.
The final cap specialization still needs those finite/scalar inputs supplied.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance.Tail

open Real Envelopes

/-- A tangent at 3 supplies the printed exponential tail without another grid. -/
theorem exp_tail_linear {y : ℝ} (hy : 3 ≤ y) :
    (56/3 : ℝ)*y+7/3 < 3*exp y := by
  have ht := Real.add_one_le_exp (y-3)
  have hp : 0 < y-2 := by linarith
  have hs : exp y = exp 3 * exp (y-3) := by rw [← Real.exp_add]; congr 1 <;> ring
  have h1 : 20*(y-2) < exp 3*(y-2) :=
    mul_lt_mul_of_pos_right exp_three_gt_twenty hp
  have h2 : exp 3*(y-2) ≤ exp 3*exp (y-3) :=
    mul_le_mul_of_nonneg_left (by linarith) (exp_pos 3).le
  rw [← hs] at h2
  linarith

theorem exp_tail_gt_twenty {y : ℝ} (hy : 3 ≤ y) : 20 < exp y :=
  lt_of_lt_of_le exp_three_gt_twenty (Real.exp_le_exp.mpr hy)

/-- The corrected beta/q bound uses monotonicity of h0, not log-star alone. -/
theorem beta_div_q_lt {lam : ℝ} (hlam : 0 < lam) (hlam7 : lam ≤ 7/3) :
    logActivity lam / q lam < 25/14 := by
  have hq := q_pos hlam
  have hq1 := q_lt_one hlam
  have hq7 : q lam ≤ q (7/3) := by
    change lam/(1+lam) ≤ (7/3:ℝ)/(1+7/3)
    norm_num
    exact (div_le_iff₀ (by linarith : 0 < 1+lam)).2 (by nlinarith)
  have hb := logActivity_pos hlam
  have hb7 := logActivity_pos (show (0:ℝ)<7/3 by norm_num)
  have hs (a : ℝ) (ha : 0<a) : scalarH (q a) = q a/logActivity a := by
    have hh : logActivity a = -log (1-q a) := by
      simpa only [logMass_zero, message_zero] using logMass_eq_neg_log ha 0
    simp only [scalarH, scalarLog, ← hh]
  have hh := scalarH_antitone ⟨hq,hq1⟩
    ⟨q_pos (show (0:ℝ)<7/3 by norm_num),q_lt_one (show (0:ℝ)<7/3 by norm_num)⟩ hq7
  rw [hs lam hlam, hs (7/3) (by norm_num)] at hh
  have hh' := (div_le_div_iff₀ hb7 hb).1 hh
  have hu := logActivity_lt_five_fourths (show (0:ℝ)<7/3 by norm_num) le_rfl
  have hqend : q (7/3) = (7/10 : ℝ) := by norm_num [q]
  rw [hqend] at hh'
  apply (div_lt_iff₀ hq).2
  nlinarith [mul_pos hq (sub_pos.mpr hu)]

theorem B_lt {lam y : ℝ} (hlam : 0 < lam) (hlam7 : lam ≤ 7/3) (hy : 0 ≤ y) :
    B lam y < 25/14 := by
  have hm := B_antitone hlam hy
  have h0 : B lam 0 = logActivity lam/q lam := by simp [B]
  rw [h0] at hm
  exact lt_of_le_of_lt hm (beta_div_q_lt hlam hlam7)

theorem gamma_div_alpha_lt {D lam : ℝ} (hD : 0<D) (hlam : 0<lam)
    (hlam7 : lam≤7/3) : gamma D lam/alpha D lam < 7/3 := by
  have hb := logActivity_pos hlam
  have hq := q_pos hlam
  have hr := beta_div_q_lt hlam hlam7
  have hr0 : 0 ≤ logActivity lam/q lam := by positivity
  have hid : gamma D lam/alpha D lam = (5/7:ℝ)*(logActivity lam/q lam)^2 := by
    unfold gamma alpha
    field_simp [hD.ne', hb.ne', hq.ne'] <;> ring
  rw [hid]
  have hh := mul_pos (sub_pos.mpr hr)
    (show 0<25/14+logActivity lam/q lam by positivity)
  nlinarith

/-- h<=1+gamma follows from the exact message/log-mass inequality. -/
theorem H_le {D lam : ℝ} (hD : 0<D) (hlam : 0<lam) (y : ℝ) :
    H D lam y ≤ message lam y*(1+gamma D lam) := by
  have hp := message_pos hlam y
  have hf := logMass_pos hlam y
  have hg := gamma_pos hD hlam
  have hu := (message_scalarH_bounds hlam y).2
  have hratio : message lam y/logMass lam y ≤ 1 := by linarith
  have hp2 : message lam y^2/logMass lam y ≤ message lam y := by
    have hh := mul_le_mul_of_nonneg_left hratio hp.le
    convert hh using 1 <;> ring
  have hid : H D lam y = message lam y*(1-message lam y)+
      gamma D lam*(message lam y^2/logMass lam y) := by unfold H; ring
  rw [hid]
  nlinarith [mul_le_mul_of_nonneg_left hp2 hg.le, sq_nonneg (message lam y)]

/-- The first displayed tail bound; no feasibility or child assumption is needed. -/
theorem L_gt_quarter {D lam y : ℝ} (hD : 0<D) (hlam : 0<lam)
    (hlam7 : lam≤7/3) (hy : 3≤y)
    (hrate : lam*(1+1/gamma D lam)<14/3) : gamma D lam/4 < L D lam y := by
  have hg := gamma_pos hD hlam
  have hp := message_pos hlam y
  have he := exp_pos y
  have hd : 0<exp y+lam := by positivity
  have hmsg : message lam y*(exp y+lam)=lam := by
    rw [message_eq_exp_quotient hlam]; field_simp
  have hH := mul_le_mul_of_nonneg_right (H_le hD hlam y) hd.le
  have hH' : H D lam y*(exp y+lam) ≤ lam*(1+gamma D lam) := by
    calc
      _ ≤ message lam y*(1+gamma D lam)*(exp y+lam) := hH
      _ = (message lam y*(exp y+lam))*(1+gamma D lam) := by ring
      _ = lam*(1+gamma D lam) := by rw [hmsg]
  have hnum : L D lam y*(exp y+lam) =
      gamma D lam*exp y-H D lam y*(exp y+lam)*y := by
    have hs : (1-message lam y)*(exp y+lam)=exp y := by nlinarith [hmsg]
    calc
      _ = gamma D lam*((1-message lam y)*(exp y+lam))-
          H D lam y*(exp y+lam)*y := by unfold L; ring
      _ = _ := by rw [hs]
  have hr : lam*(gamma D lam+1)<(14/3:ℝ)*gamma D lam := by
    have hh := mul_lt_mul_of_pos_right hrate hg
    have hid : lam*(1+1/gamma D lam)*gamma D lam = lam*(gamma D lam+1) := by
      field_simp [hg.ne'] <;> ring
    rwa [hid] at hh
  have hHy := mul_le_mul_of_nonneg_right hH' (show 0≤y by linarith)
  have hry := mul_le_mul_of_nonneg_right hr.le (show 0≤y by linarith)
  have heG := mul_lt_mul_of_pos_left (exp_tail_linear hy) hg
  have hlG := mul_le_mul_of_nonneg_left hlam7 hg.le
  apply (mul_lt_mul_iff_left₀ hd).1
  nlinarith [hnum]

/-- Equation (30) at the right cap endpoint controls the entire closed cap. -/
theorem cap_weight_bound {D lam u : ℝ} (hD : 0<D) (hlam : 0<lam)
    (hlam7 : lam≤7/3) (hlu : lam≤u)
    (hfinite : (1+u)*(1/D+25/48)<10/3) :
    (1+lam)*(1+gamma D lam)/D < 10/3 := by
  have hb := logActivity_lt_five_fourths hlam hlam7
  have hpos : 0 < 1/D+25/48 := by positivity
  have heq : (1+lam)*(1+gamma D lam)/D =
      (1+lam)*(1/D+(5/12:ℝ)*logActivity lam) := by
    unfold gamma
    field_simp [hD.ne'] <;> ring
  rw [heq]
  have h1 : (1+lam)*(1/D+(5/12:ℝ)*logActivity lam) <
      (1+lam)*(1/D+25/48) := by nlinarith
  have h2 := mul_le_mul_of_nonneg_right (show 1+lam≤1+u by linarith) hpos.le
  exact lt_trans h1 (lt_of_le_of_lt h2 hfinite)

/-- The two printed tail estimates imply the printed loss bound, including J=0. -/
theorem loss_lt {D lam t y : ℝ} (hD : 0<D) (hlam : 0<lam)
    (ht : 0≤t) (hy : 3≤y)
    (hL : gamma D lam/4<L D lam y)
    (hweight : (1+lam)*(1+gamma D lam)/D<10/3) :
    H D lam y^2*J lam t/(alpha D lam*Z D lam t y)<16/35 := by
  have ha := alpha_pos hD hlam
  have hg := gamma_pos hD hlam
  have hp := message_pos hlam y
  have hq := q_pos hlam
  have hH := H_pos hD hlam y
  have hJ := J_nonneg hlam ht
  have hL0 : 0<L D lam y := by linarith
  have hZ : 0<Z D lam t y := by unfold Z; positivity
  have he20 := exp_tail_gt_twenty hy
  have hmsg : message lam y*(exp y+lam)=lam := by
    rw [message_eq_exp_quotient hlam]; field_simp
  have hpE : message lam y*exp y<lam := by nlinarith
  have hHE := mul_le_mul_of_nonneg_right (H_le hD hlam y) (exp_pos y).le
  have hpEg := mul_lt_mul_of_pos_right hpE (show 0<1+gamma D lam by positivity)
  have hw := (div_lt_iff₀ hD).1 hweight
  have hwq := mul_lt_mul_of_pos_right hw hq
  have hql : q lam*(1+lam)=lam := by unfold q; field_simp
  have hqlg := congrArg (fun z : ℝ => z*(1+gamma D lam)) hql
  have hHexp : H D lam y*exp y<(10/3:ℝ)*D*q lam := by
    nlinarith [hqlg]
  have h20H := mul_lt_mul_of_pos_left he20 hH
  have hsmall : H D lam y < D*q lam/6 := by nlinarith
  have hsq : 36*H D lam y^2<D^2*q lam^2 := by
    nlinarith [sq_nonneg (D*q lam-6*H D lam y),
      mul_pos (show 0<D*q lam-6*H D lam y by linarith)
        (show 0<D*q lam+6*H D lam y by positivity)]
  have hZG : gamma D lam*J lam t < 4*Z D lam t y := by
    have hh := mul_le_mul_of_nonneg_right hL.le hJ
    unfold Z
    nlinarith [mul_pos hp hg]
  have hloss : H D lam y^2*J lam t/(alpha D lam*Z D lam t y) <
      4*H D lam y^2/(alpha D lam*gamma D lam) := by
    apply (div_lt_div_iff₀ (mul_pos ha hZ) (mul_pos ha hg)).2
    have hh := mul_lt_mul_of_pos_left hZG (show 0<H D lam y^2*alpha D lam by positivity)
    nlinarith
  have hag := alpha_mul_gamma (D:=D) hlam
  have hlast : 4*H D lam y^2/(alpha D lam*gamma D lam)<16/35 := by
    apply (div_lt_iff₀ (mul_pos ha hg)).2
    nlinarith [hsq, hag]
  exact lt_trans hloss hlast

theorem message_tail_lt {lam y : ℝ} (hlam : 0<lam) (hlam7 : lam≤7/3)
    (hy : 3≤y) : message lam y<7/67 := by
  rw [message_eq_exp_quotient hlam]
  apply (div_lt_iff₀ (show 0<exp y+lam by positivity)).2
  have he := exp_tail_gt_twenty hy
  nlinarith

/-- Actual AC is positive on the whole unbounded parent tail. Only the two
printed scalar inputs remain; there is no finite grid in y or t. -/
theorem AC_positive {D lam t y : ℝ} (hD : (6/5:ℝ)≤D) (hlam : 0<lam)
    (hlam7 : lam≤7/3) (ht : 0≤t) (hy : 3≤y)
    (hrate : lam*(1+1/gamma D lam)<14/3)
    (hweight : (1+lam)*(1+gamma D lam)/D<10/3) : 0<AC D lam t y := by
  have hD0 : 0<D := by linarith
  have hy0 : 0<y := by linarith
  have hp := message_pos hlam y
  have ha := alpha_pos hD0 hlam
  have hg := gamma_pos hD0 hlam
  have hf := logMass_pos hlam t
  have hL := L_gt_quarter hD0 hlam hlam7 hy hrate
  have hL0 : 0<L D lam y := by linarith
  have hJ := J_nonneg hlam ht
  have hZ : 0<Z D lam t y := by unfold Z; positivity
  have hB := B_lt hlam hlam7 (show 0≤y by linarith)
  have hBy : B lam y/y<25/42 := by
    apply (div_lt_iff₀ hy0).2
    linarith
  have hfpy : logMass lam y/y=message lam y*(B lam y/y) := by
    unfold B
    field_simp [hp.ne',hy0.ne'] <;> ring
  have hEp : 1-(67/42:ℝ)*message lam y<E lam t y := by
    have hh := mul_lt_mul_of_pos_left hBy hp
    have hc : 0 ≤ message lam y*t/logMass lam t := by positivity
    unfold E
    rw [hfpy]
    nlinarith
  have hA : 1≤capA D lam := by
    unfold capA
    have hq := q_pos hlam
    nlinarith
  have hH := H_le hD0 hlam y
  have hparent : -message lam y*gamma D lam ≤ capA D lam*message lam y-H D lam y := by
    have hh := mul_le_mul_of_nonneg_right hA hp.le
    nlinarith
  have hga := (div_lt_iff₀ ha).1 (gamma_div_alpha_lt hD0 hlam hlam7)
  have hgay : gamma D lam<(7/9:ℝ)*alpha D lam*y := by
    nlinarith [mul_nonneg ha.le (show 0≤y-3 by linarith)]
  have hterm : -(7/9:ℝ)*message lam y <
      (capA D lam*message lam y-H D lam y)/(alpha D lam*y) := by
    apply (lt_div_iff₀ (mul_pos ha hy0)).2
    have hh := mul_lt_mul_of_pos_left hgay hp
    nlinarith
  have hloss := loss_lt hD0 hlam ht hy hL hweight
  have hid : AC D lam t y/alpha D lam = E lam t y+
      (capA D lam*message lam y-H D lam y)/(alpha D lam*y)-
      H D lam y^2*J lam t/(alpha D lam*Z D lam t y) := by
    unfold AC
    field_simp [ha.ne',hy0.ne',hZ.ne'] <;> ring
  have hp7 := message_tail_lt hlam hlam7 hy
  have hnorm : (12449/42210:ℝ)<AC D lam t y/alpha D lam := by
    rw [hid]
    nlinarith
  have hpos : 0<AC D lam t y/alpha D lam := by linarith
  simpa only [zero_mul] using (lt_div_iff₀ ha).1 hpos

/-- The only finite tail input is the actual printed equation (30) for this cap. -/
theorem AC_positive_on_cap {c : Cap} {lam t y : ℝ} (hc : c.Contains lam)
    (ht : 0≤t) (hy : 3≤y)
    (hrate : lam*(1+1/gamma c.value lam)<14/3)
    (hfinite : (1+c.upper)*(1/c.value+25/48)<10/3) : 0<AC c.value lam t y := by
  have hD : (6/5:ℝ)≤c.value := by cases c <;> norm_num [Cap.value]
  exact AC_positive hD (Cap.activity_pos hc) (Cap.activity_domain hc).2 ht hy hrate
    (cap_weight_bound c.value_pos (Cap.activity_pos hc) (Cap.activity_domain hc).2 hc.2 hfinite)

end Erdos993Lean.Analytic.V213.FreeCountVariance.Tail

-- Type and axiom audit commands.
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Tail.exp_tail_linear
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Tail.exp_tail_linear
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Tail.exp_tail_gt_twenty
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Tail.exp_tail_gt_twenty
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Tail.beta_div_q_lt
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Tail.beta_div_q_lt
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Tail.B_lt
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Tail.B_lt
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Tail.gamma_div_alpha_lt
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Tail.gamma_div_alpha_lt
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Tail.H_le
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Tail.H_le
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Tail.L_gt_quarter
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Tail.L_gt_quarter
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Tail.cap_weight_bound
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Tail.cap_weight_bound
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Tail.loss_lt
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Tail.loss_lt
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Tail.message_tail_lt
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Tail.message_tail_lt
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Tail.AC_positive
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Tail.AC_positive
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Tail.AC_positive_on_cap
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Tail.AC_positive_on_cap
