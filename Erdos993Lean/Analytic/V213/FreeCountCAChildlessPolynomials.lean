module

public import Erdos993Lean.Analytic.V213.FreeCountCAChildlessSlope

/-! Literal N4/N5 and beta-endpoint reduction for the current childless face.
Only the two printed values at the cap's upper q endpoint are retained as
finite premises. The decrease in q and the concave beta interpolation are
proved here on their full stated domains. This file contains no table replay.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance

open Real Set

noncomputable def childlessN4 (D q : ℝ) : ℝ :=
  D*(40+20*q-46*q^2-13*q^3-7*q^4)+48*q^2-96*q
noncomputable def childlessN5 (D q : ℝ) : ℝ :=
  D*(40-20*q-52*q^2+40*q^3-18*q^4-5*q^5)-48*q^3+144*q^2-96*q
noncomputable def childlessP (D q beta : ℝ) : ℝ :=
  12*beta-7*q*(1+q/2)-12*q*beta/(D*(1+q))-5*q*beta^2*(2+q)/(2*(1+q))
noncomputable def betaLower (q : ℝ) : ℝ := 2*q/(2-q)
noncomputable def betaUpper (q : ℝ) : ℝ := q*(2-q)/(2*(1-q))

theorem childlessN4_hasDerivAt (D q : ℝ) :
    HasDerivAt (childlessN4 D)
      (D*(20-92*q-39*q^2-28*q^3)+96*q-96) q := by
  have hi := hasDerivAt_id q
  have hp := ((((hasDerivAt_const q 40).add (hi.const_mul 20)).sub
    ((hi.pow 2).const_mul 46)).sub ((hi.pow 3).const_mul 13)).sub
    ((hi.pow 4).const_mul 7)
  have hd := ((hp.const_mul D).add ((hi.pow 2).const_mul 48)).sub (hi.const_mul 96)
  change HasDerivAt (childlessN4 D) _ q at hd
  exact hd.congr_deriv (by (try simp only [id_eq, Pi.pow_apply]) <;> ring)

theorem childlessN5_hasDerivAt (D q : ℝ) :
    HasDerivAt (childlessN5 D)
      (D*(-20-104*q+120*q^2-72*q^3-25*q^4)-144*q^2+288*q-96) q := by
  have hi := hasDerivAt_id q
  have hp := (((((hasDerivAt_const q 40).sub (hi.const_mul 20)).sub
    ((hi.pow 2).const_mul 52)).add ((hi.pow 3).const_mul 40)).sub
    ((hi.pow 4).const_mul 18)).sub ((hi.pow 5).const_mul 5)
  have hd := (((hp.const_mul D).sub ((hi.pow 3).const_mul 48)).add
    ((hi.pow 2).const_mul 144)).sub (hi.const_mul 96)
  change HasDerivAt (childlessN5 D) _ q at hd
  exact hd.congr_deriv (by (try simp only [id_eq, Pi.pow_apply]) <;> ring)

theorem childlessN4_deriv_neg {D q : ℝ} (hD : 6/5 ≤ D)
    (hql : 1/4 ≤ q) (hqu : q ≤ 7/10) :
    deriv (childlessN4 D) q < 0 := by
  rw [(childlessN4_hasDerivAt D q).deriv]
  have hq : 0 ≤ q := by linarith
  have hc : 20-92*q-39*q^2-28*q^3 < 0 := by
    nlinarith [sq_nonneg q,pow_nonneg hq 3]
  have hh := mul_neg_of_pos_of_neg (show 0 < D by linarith) hc
  linarith

/-- The paper's explicit upper bound for N5', with every sign accounted for. -/
theorem childlessN5_deriv_bound {D q : ℝ} (hD : 6/5 ≤ D)
    (hql : 1/4 ≤ q) (hqu : q ≤ 7/10) :
    deriv (childlessN5 D) q ≤ 24*(1-q)*(6*q-5) := by
  have hq : 0 ≤ q := by linarith
  have hq2 : q^2 ≤ (7/10)*q := by nlinarith
  have hq3 : 0 ≤ q^3 := pow_nonneg hq 3
  have hq4 : 0 ≤ q^4 := pow_nonneg hq 4
  have hc : -20-104*q+120*q^2-72*q^3-25*q^4 ≤ 0 := by nlinarith
  have hm := mul_le_mul_of_nonpos_right hD hc
  have hsmall : 144*q^2-(504/5)*q-(432/5)*q^3-30*q^4 ≤ 0 := by
    nlinarith only [hq2,hq3,hq4]
  rw [(childlessN5_hasDerivAt D q).deriv]
  nlinarith only [hm,hsmall]

theorem childlessN5_deriv_neg {D q : ℝ} (hD : 6/5 ≤ D)
    (hql : 1/4 ≤ q) (hqu : q ≤ 7/10) :
    deriv (childlessN5 D) q < 0 := by
  have hb := childlessN5_deriv_bound hD hql hqu
  have hn : 24*(1-q)*(6*q-5) < 0 := by
    exact mul_neg_of_pos_of_neg (by nlinarith) (by linarith)
  exact hb.trans_lt hn

theorem childlessN4_antitone {D : ℝ} (hD : 6/5 ≤ D) :
    AntitoneOn (childlessN4 D) (Icc (1/4) (7/10)) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc (1/4) (7/10))
    (f' := fun q => deriv (childlessN4 D) q)
  · intro q hq
    exact (childlessN4_hasDerivAt D q).continuousAt.continuousWithinAt
  · intro q hq
    rw [(childlessN4_hasDerivAt D q).deriv]
    exact (childlessN4_hasDerivAt D q).hasDerivWithinAt
  · intro q hq
    have hh := interior_subset hq
    exact (childlessN4_deriv_neg hD hh.1 hh.2).le

theorem childlessN5_antitone {D : ℝ} (hD : 6/5 ≤ D) :
    AntitoneOn (childlessN5 D) (Icc (1/4) (7/10)) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc (1/4) (7/10))
    (f' := fun q => deriv (childlessN5 D) q)
  · intro q hq
    exact (childlessN5_hasDerivAt D q).continuousAt.continuousWithinAt
  · intro q hq
    rw [(childlessN5_hasDerivAt D q).deriv]
    exact (childlessN5_hasDerivAt D q).hasDerivWithinAt
  · intro q hq
    have hh := interior_subset hq
    exact (childlessN5_deriv_neg hD hh.1 hh.2).le

theorem beta_endpoint_gap {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    betaUpper q-betaLower q = q^3/(2*(1-q)*(2-q)) ∧
      betaLower q < betaUpper q := by
  have h1 : 1-q ≠ 0 := ne_of_gt (by linarith)
  have h2 : 2-q ≠ 0 := ne_of_gt (by linarith)
  have h1p : 0 < 1-q := by linarith
  have h2p : 0 < 2-q := by linarith
  have hid : betaUpper q-betaLower q = q^3/(2*(1-q)*(2-q)) := by
    unfold betaLower betaUpper
    field_simp [h1,h2] <;> ring
  refine ⟨hid,?_⟩
  have hr : 0 < q^3/(2*(1-q)*(2-q)) := by positivity
  linarith

theorem childlessP_endpoints {D q : ℝ} (hD : 0 < D)
    (hq : 0 < q) (hq1 : q < 1) :
    childlessP D q (betaLower q) = q*childlessN4 D q/(2*D*(2-q)^2*(1+q)) ∧
    childlessP D q (betaUpper q) = q*childlessN5 D q/(8*D*(1-q)^2*(1+q)) := by
  have h1 : 1-q ≠ 0 := ne_of_gt (by linarith)
  have h2 : 2-q ≠ 0 := ne_of_gt (by linarith)
  have h3 : 1+q ≠ 0 := ne_of_gt (by linarith)
  constructor <;> simp only [childlessP, childlessN4, childlessN5, betaLower, betaUpper] <;>
    field_simp [hD.ne',h1,h2,h3] <;> ring

theorem childlessP_chord {D q beta : ℝ} (hD : 0 < D)
    (hq : 0 < q) (hq1 : q < 1)
    (hl : betaLower q ≤ beta) (hu : beta ≤ betaUpper q) :
    ((betaUpper q-beta)*childlessP D q (betaLower q) +
      (beta-betaLower q)*childlessP D q (betaUpper q))/(betaUpper q-betaLower q) ≤
      childlessP D q beta := by
  have hg := (beta_endpoint_gap hq hq1).2
  have hgap := sub_pos.mpr hg
  have hid : childlessP D q beta -
      ((betaUpper q-beta)*childlessP D q (betaLower q) +
      (beta-betaLower q)*childlessP D q (betaUpper q))/(betaUpper q-betaLower q) =
      (5*q*(2+q)/(2*(1+q)))*(beta-betaLower q)*(betaUpper q-beta) := by
    unfold childlessP
    field_simp [hD.ne',hgap.ne',show 1+q ≠ 0 by positivity] <;> ring
  rw [← sub_nonneg,hid]
  exact mul_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr hl)) (sub_nonneg.mpr hu)

/-- Exactly two point comparisons at an upper cap endpoint remain explicit. -/
theorem childlessP_pos_of_upper_endpoint {D q r beta : ℝ}
    (hD : 6/5 ≤ D) (hql : 1/4 ≤ q) (hqr : q ≤ r) (hr : r ≤ 7/10)
    (hN4 : 0 < childlessN4 D r) (hN5 : 0 < childlessN5 D r)
    (hl : betaLower q ≤ beta) (hu : beta ≤ betaUpper q) :
    0 < childlessP D q beta := by
  have hDp : 0 < D := by linarith
  have hq : 0 < q := by linarith
  have hq1 : q < 1 := by linarith
  have h1p : 0 < 1-q := by linarith
  have h2p : 0 < 2-q := by linarith
  have hN4q := hN4.trans_le (childlessN4_antitone hD ⟨hql,by linarith⟩
    ⟨by linarith,hr⟩ hqr)
  have hN5q := hN5.trans_le (childlessN5_antitone hD ⟨hql,by linarith⟩
    ⟨by linarith,hr⟩ hqr)
  have he := childlessP_endpoints hDp hq hq1
  have hlo : 0 < childlessP D q (betaLower q) := by rw [he.1]; positivity
  have hhi : 0 < childlessP D q (betaUpper q) := by rw [he.2]; positivity
  have hg := (beta_endpoint_gap hq hq1).2
  have hn : 0 < (betaUpper q-beta)*childlessP D q (betaLower q) +
      (beta-betaLower q)*childlessP D q (betaUpper q) := by
    by_cases heq : beta = betaUpper q
    · rw [heq,sub_self,zero_mul,zero_add]
      exact mul_pos (sub_pos.mpr hg) hhi
    · have hu' : 0 < betaUpper q-beta := by rcases eq_or_lt_of_le hu with h | h; exact False.elim (heq h); linarith
      exact add_pos_of_pos_of_nonneg (mul_pos hu' hlo)
        (mul_nonneg (sub_nonneg.mpr hl) hhi.le)
  have hc := childlessP_chord hDp hq hq1 hl hu
  exact (div_pos hn (sub_pos.mpr hg)).trans_le hc

end Erdos993Lean.Analytic.V213.FreeCountVariance

#check Erdos993Lean.Analytic.V213.FreeCountVariance.childlessN4_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.childlessN4_hasDerivAt
#check Erdos993Lean.Analytic.V213.FreeCountVariance.childlessN5_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.childlessN5_hasDerivAt
#check Erdos993Lean.Analytic.V213.FreeCountVariance.childlessN4_deriv_neg
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.childlessN4_deriv_neg
#check Erdos993Lean.Analytic.V213.FreeCountVariance.childlessN5_deriv_bound
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.childlessN5_deriv_bound
#check Erdos993Lean.Analytic.V213.FreeCountVariance.childlessN5_deriv_neg
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.childlessN5_deriv_neg
#check Erdos993Lean.Analytic.V213.FreeCountVariance.childlessN4_antitone
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.childlessN4_antitone
#check Erdos993Lean.Analytic.V213.FreeCountVariance.childlessN5_antitone
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.childlessN5_antitone
#check Erdos993Lean.Analytic.V213.FreeCountVariance.beta_endpoint_gap
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.beta_endpoint_gap
#check Erdos993Lean.Analytic.V213.FreeCountVariance.childlessP_endpoints
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.childlessP_endpoints
#check Erdos993Lean.Analytic.V213.FreeCountVariance.childlessP_chord
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.childlessP_chord
#check Erdos993Lean.Analytic.V213.FreeCountVariance.childlessP_pos_of_upper_endpoint
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.childlessP_pos_of_upper_endpoint
