module

public import Erdos993Lean.Analytic.V213.FreeCountACH0
public import Erdos993Lean.Analytic.V213.FreeCountVarianceDerivatives
public import Erdos993Lean.Analytic.V213.FreeCountACCellCalculus

/-! Actual parent curvature in (22), followed by its closed-interval
interpolation consequence. The strict exp (5/4)<4 premise is the printed F12
input; endpoint activity/gamma/q bounds remain literal scalar inputs. No
curvature or whole ell-bound is assumed under a paper-lemma name.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance

open Real Set

noncomputable def hParentSlope (D lam y : ℝ) : ℝ :=
  message lam y*(1-message lam y)-
    gamma D lam*(lam*exp (-y))*activityH0Slope (lam*exp (-y))
noncomputable def hParentCurvature (D lam y : ℝ) : ℝ :=
  message lam y*(1-message lam y)*(2*message lam y-1)+gamma D lam*
    ((lam*exp (-y))*activityH0Slope (lam*exp (-y))+
      (lam*exp (-y))^2*activityH0Curvature (lam*exp (-y)))
noncomputable def ellParentSlope (D lam y : ℝ) : ℝ :=
  ap lam y-h D lam y/gamma D lam-y*hParentSlope D lam y/gamma D lam
noncomputable def ellParentCurvature (D lam y : ℝ) : ℝ :=
  ap lam y-(2*hParentSlope D lam y+y*hParentCurvature D lam y)/gamma D lam

theorem h_eq_H0_model {lam : ℝ} (hlam : 0 < lam) (D y : ℝ) :
    h D lam y = 1-message lam y+gamma D lam*activityH0 (lam*exp (-y)) := by
  rw [h_normalized hlam]
  have hz : 0 < lam*exp (-y) := mul_pos hlam (exp_pos _)
  have hf : log (1+lam*exp (-y)) ≠ 0 := (log_pos (by linarith)).ne'
  unfold B message logMass Reserve.msg Reserve.lmass activityH0
  field_simp [hlam.ne',(exp_pos (-y)).ne',hf,show 1+lam*exp (-y) ≠ 0 by positivity] <;> ring

theorem h_hasDerivAt_parent_model {lam : ℝ} (hlam : 0 < lam) (D y : ℝ) :
    HasDerivAt (h D lam) (hParentSlope D lam y) y := by
  have hz : 0 < lam*exp (-y) := mul_pos hlam (exp_pos _)
  have hd : HasDerivAt (fun z : ℝ => lam*exp (-z)) (-lam*exp (-y)) y := by
    convert (((hasDerivAt_id y).neg.exp).const_mul lam) using 1 <;>
      (try simp only [id_eq, Pi.pow_apply, Pi.neg_apply, Function.comp_apply]) <;> ring
  have hfun : h D lam = fun z =>
      1-message lam z+gamma D lam*activityH0 (lam*exp (-z)) := by
    funext z
    exact h_eq_H0_model hlam D z
  rw [hfun]
  apply (((message_hasDerivAt hlam y).const_sub 1).add
    (((activityH0_hasDerivAt hz).comp y hd).const_mul (gamma D lam))).congr_deriv
  unfold hParentSlope
  (try simp only [id_eq, Pi.pow_apply, Pi.neg_apply, Function.comp_apply]) <;> ring

theorem hParentSlope_hasDerivAt {lam : ℝ} (hlam : 0 < lam) (D y : ℝ) :
    HasDerivAt (hParentSlope D lam) (hParentCurvature D lam y) y := by
  have hz : 0 < lam*exp (-y) := mul_pos hlam (exp_pos _)
  have hd : HasDerivAt (fun z : ℝ => lam*exp (-z)) (-lam*exp (-y)) y := by
    convert (((hasDerivAt_id y).neg.exp).const_mul lam) using 1 <;>
      (try simp only [id_eq, Pi.pow_apply, Pi.neg_apply, Function.comp_apply]) <;> ring
  have hp := message_hasDerivAt hlam y
  unfold hParentSlope
  apply ((hp.mul (hp.const_sub 1)).sub
    ((hd.const_mul (gamma D lam)).mul ((activityH0Slope_hasDerivAt hz).comp y hd))).congr_deriv
  unfold hParentCurvature
  (try simp only [id_eq, Pi.pow_apply, Pi.neg_apply, Function.comp_apply]) <;> ring

theorem hParentSlope_pos {D lam : ℝ} (hD : 0 < D) (hlam : 0 < lam) (y : ℝ) :
    0 < hParentSlope D lam y := by
  have hp := message_pos hlam y
  have hk : 0 < 1-message lam y := sub_pos.mpr (message_lt_one hlam y)
  have hg := gamma_pos hD hlam
  have hz : 0 < lam*exp (-y) := mul_pos hlam (exp_pos _)
  have hn := mul_nonpos_of_nonneg_of_nonpos (mul_pos hg hz).le (activityH0Slope_nonpos hz)
  unfold hParentSlope
  have hpk := mul_pos hp hk
  linarith

theorem hParentCurvature_lower {D lam y : ℝ} (hD : 0 < D)
    (hlam : 0 < lam) (hy : 0 ≤ y) :
    -1/4-gamma D lam*q lam/2 ≤ hParentCurvature D lam y := by
  let z := lam*exp (-y)
  have hz : 0 < z := mul_pos hlam (exp_pos _)
  have hg := gamma_pos hD hlam
  have hp := message_pos hlam y
  have hp1 := message_lt_one hlam y
  have hpk : 0 ≤ message lam y*(1-message lam y) :=
    mul_nonneg hp.le (sub_nonneg.mpr hp1.le)
  have hpk4 : message lam y*(1-message lam y) ≤ 1/4 := by
    nlinarith [sq_nonneg (message lam y-1/2)]
  have hfirst : -1/4 ≤ message lam y*(1-message lam y)*(2*message lam y-1) := by
    have hh := mul_nonneg hpk (show 0 ≤ 2*message lam y by positivity)
    nlinarith
  have hsl := mul_le_mul_of_nonneg_left (activityH0Slope_lower hz) hz.le
  have hid : z*(-1/(2*(1+z))) = -message lam y/2 := by
    change z*(-1/(2*(1+z))) = -(z/(1+z))/2
    field_simp [show 1+z ≠ 0 by positivity] <;> ring
  rw [hid] at hsl
  have hcurv : 0 ≤ z^2*activityH0Curvature z :=
    mul_nonneg (sq_nonneg _) (activityH0Curvature_nonneg hz)
  have hsum : -message lam y/2 ≤ z*activityH0Slope z+z^2*activityH0Curvature z := by
    linarith
  have hmul := mul_le_mul_of_nonneg_left hsum hg.le
  have hpq := Envelopes.message_le_q hlam hy
  have hqmul := mul_le_mul_of_nonneg_left hpq hg.le
  change _ ≤ message lam y*(1-message lam y)*(2*message lam y-1)+gamma D lam*
    (z*activityH0Slope z+z^2*activityH0Curvature z)
  nlinarith only [hfirst,hmul,hqmul]

theorem ell_hasDerivAt_parent_model {D lam : ℝ} (hD : 0 < D)
    (hlam : 0 < lam) (y : ℝ) :
    HasDerivAt (ell D lam) (ellParentSlope D lam y) y := by
  have hfun : ell D lam = fun z => ap lam z-z*h D lam z/gamma D lam := by
    funext z
    exact ell_normalized hD hlam z
  rw [hfun]
  apply ((ap_hasDerivAt hlam y).sub
    (((hasDerivAt_id y).mul (h_hasDerivAt_parent_model hlam D y)).div_const
      (gamma D lam))).congr_deriv
  unfold ellParentSlope
  (try simp only [id_eq, Pi.pow_apply, Pi.neg_apply, Function.comp_apply]) <;> ring

theorem ellParentSlope_hasDerivAt {D lam : ℝ} (hD : 0 < D)
    (hlam : 0 < lam) (y : ℝ) :
    HasDerivAt (ellParentSlope D lam) (ellParentCurvature D lam y) y := by
  unfold ellParentSlope
  apply (((ap_hasDerivAt hlam y).sub ((h_hasDerivAt_parent_model hlam D y).div_const
    (gamma D lam))).sub (((hasDerivAt_id y).mul
      (hParentSlope_hasDerivAt hlam D y)).div_const (gamma D lam))).congr_deriv
  unfold ellParentCurvature
  (try simp only [id_eq, Pi.pow_apply, Pi.neg_apply, Function.comp_apply]) <;> ring

theorem ellParentCurvature_bound {D lam y : ℝ} (hD : 0 < D)
    (hlam : 0 < lam) (hy : 0 ≤ y) :
    ellParentCurvature D lam y < ap lam y+y/(4*gamma D lam)+y*q lam/2 := by
  have hg := gamma_pos hD hlam
  have hs := hParentSlope_pos hD hlam y
  have hc := mul_le_mul_of_nonneg_left (hParentCurvature_lower hD hlam hy) hy
  have hid : (ap lam y+y/(4*gamma D lam)+y*q lam/2-
      ellParentCurvature D lam y)*gamma D lam =
      y/4+y*q lam*gamma D lam/2+2*hParentSlope D lam y+y*hParentCurvature D lam y := by
    unfold ellParentCurvature
    field_simp [hg.ne'] <;> ring
  have hh : 0 < (ap lam y+y/(4*gamma D lam)+y*q lam/2-
      ellParentCurvature D lam y)*gamma D lam := by
    rw [hid]
    nlinarith only [hs,hc]
  have hgap := (mul_pos_iff_of_pos_right hg).1 hh
  linarith

/-- The numeric side conditions are precisely those stated after (22). -/
theorem ellParentCurvature_lt_nine_halves {D u y : ℝ} (hD : 0 < D)
    (hu : 5/4 < u) (hg : 2/5 < gamma D u) (hq : q u ≤ 7/10)
    (hexp : exp (5/4 : ℝ) < 4) (hy : 0 ≤ y) (hyu : y ≤ 5/4) :
    ellParentCurvature D u y < 9/2 := by
  have hup : 0 < u := by linarith
  have hgp := gamma_pos hD hup
  have hqp := q_pos hup
  have he : exp y < 4 := (exp_le_exp.mpr hyu).trans_lt hexp
  have ha : ap u y < 16/5 := by
    unfold ap
    apply (div_lt_iff₀ hup).2
    linarith
  have hmiddle : y/(4*gamma D u) < 25/32 := by
    apply (div_lt_iff₀ (by positivity)).2
    linarith
  have hlast : y*q u/2 ≤ 7/16 := by
    have hh := mul_le_mul hyu hq hqp.le (by norm_num : (0 : ℝ) ≤ 5/4)
    nlinarith
  have hc := ellParentCurvature_bound hD hup hy
  linarith

/-- The exact 9(d-c)^2/16 correction in every printed C face row. -/
theorem ell_parent_cell_lower {D u c d y : ℝ} (hD : 0 < D)
    (hu : 5/4 < u) (hg : 2/5 < gamma D u) (hq : q u ≤ 7/10)
    (hexp : exp (5/4 : ℝ) < 4) (hc : 0 ≤ c) (hcd : c < d) (hd : d ≤ 5/4)
    (hy : y ∈ Icc c d) :
    min (ell D u c) (ell D u d)-(9/16)*(d-c)^2 ≤ ell D u y := by
  have hup : 0 < u := by linarith
  have hfirst : ∀ z ∈ Icc c d,
      HasDerivAt (fun x => -ell D u x) (-ellParentSlope D u z) z := by
    intro z hz
    exact (ell_hasDerivAt_parent_model hD hup z).neg
  have hsecond : ∀ z ∈ Icc c d,
      HasDerivAt (fun x => -ellParentSlope D u x) (-ellParentCurvature D u z) z := by
    intro z hz
    exact (ellParentSlope_hasDerivAt hD hup z).neg
  have hcurv : ∀ z ∈ Icc c d, -(9/2 : ℝ) ≤ -ellParentCurvature D u z := by
    intro z hz
    have hh := ellParentCurvature_lt_nine_halves hD hu hg hq hexp
      (hc.trans hz.1) (hz.2.trans hd)
    linarith
  have hbound := second_lower_endpoint_upper hcd (by norm_num : (0 : ℝ) ≤ 9/2)
    hfirst hsecond hcurv hy
  have hid : max (-ell D u c) (-ell D u d) = -min (ell D u c) (ell D u d) := by
    rcases le_total (ell D u c) (ell D u d) with h | h
    · rw [min_eq_left h,max_eq_left (neg_le_neg h)]
    · rw [min_eq_right h,max_eq_right (neg_le_neg h)]
  rw [hid] at hbound
  nlinarith only [hbound]

end Erdos993Lean.Analytic.V213.FreeCountVariance

#check Erdos993Lean.Analytic.V213.FreeCountVariance.h_eq_H0_model
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.h_eq_H0_model
#check Erdos993Lean.Analytic.V213.FreeCountVariance.h_hasDerivAt_parent_model
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.h_hasDerivAt_parent_model
#check Erdos993Lean.Analytic.V213.FreeCountVariance.hParentSlope_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.hParentSlope_hasDerivAt
#check Erdos993Lean.Analytic.V213.FreeCountVariance.hParentSlope_pos
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.hParentSlope_pos
#check Erdos993Lean.Analytic.V213.FreeCountVariance.hParentCurvature_lower
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.hParentCurvature_lower
#check Erdos993Lean.Analytic.V213.FreeCountVariance.ell_hasDerivAt_parent_model
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.ell_hasDerivAt_parent_model
#check Erdos993Lean.Analytic.V213.FreeCountVariance.ellParentSlope_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.ellParentSlope_hasDerivAt
#check Erdos993Lean.Analytic.V213.FreeCountVariance.ellParentCurvature_bound
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.ellParentCurvature_bound
#check Erdos993Lean.Analytic.V213.FreeCountVariance.ellParentCurvature_lt_nine_halves
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.ellParentCurvature_lt_nine_halves
#check Erdos993Lean.Analytic.V213.FreeCountVariance.ell_parent_cell_lower
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.ell_parent_cell_lower
