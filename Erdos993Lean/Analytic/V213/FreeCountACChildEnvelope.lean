module

public import Erdos993Lean.Analytic.V213.FreeCountACParentFunctions
public import Erdos993Lean.Analytic.V213.FreeCountRealScalarBounds

/-!+Actual child elimination, current (24). The derivative and supporting-line
arguments use the genuine message/logMass functions; no old completed
variance theorem or named unproved convexity premise is imported.+-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance

open Real Set

noncomputable def childGap (lam t : ℝ) : ℝ :=
  (q lam ^ 2 / message lam t ^ 2 - 1) * logMass lam t

noncomputable def childGapSlope (lam t : ℝ) : ℝ :=
  message lam t - q lam ^ 2 / message lam t +
    (2 * q lam ^ 2) * ((1 - message lam t) * logMass lam t) / message lam t ^ 2

noncomputable def childGapCurvature (lam t : ℝ) : ℝ :=
  (1 - message lam t) / message lam t ^ 2 *
    (q lam ^ 2 * ((4 - 2 * message lam t) * logMass lam t - 3 * message lam t) -
      message lam t ^ 3)

theorem childGap_hasDerivAt {lam : ℝ} (hlam : 0 < lam) (t : ℝ) :
    HasDerivAt (childGap lam) (childGapSlope lam t) t := by
  have hu := (message_pos hlam t).ne'
  change HasDerivAt (fun s => (q lam ^ 2 / message lam s ^ 2 - 1) * logMass lam s) _ t
  apply ((((hasDerivAt_const t (q lam ^ 2)).div
    ((message_hasDerivAt hlam t).pow 2) (pow_ne_zero 2 hu)).sub_const 1).mul
      (logMass_hasDerivAt hlam t)).congr_deriv
  unfold childGapSlope
  (try dsimp) <;> (try simp only [id_eq, Pi.pow_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply]) <;> field_simp [hu] <;> ring

theorem childGapSlope_hasDerivAt {lam : ℝ} (hlam : 0 < lam) (t : ℝ) :
    HasDerivAt (childGapSlope lam) (childGapCurvature lam t) t := by
  have hu := (message_pos hlam t).ne'
  have hup := message_hasDerivAt hlam t
  have hphi := logMass_hasDerivAt hlam t
  unfold childGapSlope
  apply ((hup.sub ((hasDerivAt_const t (q lam ^ 2)).div hup hu)).add
    (((((hup.const_sub 1).mul hphi).const_mul (2 * q lam ^ 2))).div
      (hup.pow 2) (pow_ne_zero 2 hu))).congr_deriv
  unfold childGapCurvature
  (try dsimp) <;> (try simp only [id_eq, Pi.pow_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply]) <;> field_simp [hu] <;> ring

theorem childGapCurvature_nonneg {lam t : ℝ} (hlam : 0 < lam) (ht : 0 ≤ t) :
    0 ≤ childGapCurvature lam t := by
  have hu := message_pos hlam t
  have hk : 0 ≤ 1 - message lam t := (sub_pos.mpr (message_lt_one hlam t)).le
  have hphi := logMass_pos hlam t
  have hq := q_pos hlam
  have hmq := Envelopes.message_le_q hlam ht
  have hup := (Envelopes.message_scalarH_bounds hlam t).2
  have hcleared := (div_le_iff₀ hphi).mp hup
  have hbase : 4 * message lam t ≤
      (4 - 2 * message lam t) * logMass lam t := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hbase (sq_nonneg (q lam))
  have hsq : message lam t ^ 2 ≤ q lam ^ 2 := by nlinarith
  have hlast := mul_nonneg (sub_nonneg.mpr hsq) hu.le
  have hn : 0 ≤ q lam ^ 2 *
      ((4 - 2 * message lam t) * logMass lam t - 3 * message lam t) - message lam t ^ 3 := by
    nlinarith only [hmul, hlast]
  exact mul_nonneg (div_nonneg hk (sq_nonneg _)) hn

@[simp] theorem childGap_zero {lam : ℝ} (hlam : 0 < lam) : childGap lam 0 = 0 := by
  have hq := (q_pos hlam).ne'
  simp [childGap, hq]

@[simp] theorem childGapSlope_zero {lam : ℝ} (hlam : 0 < lam) :
    childGapSlope lam 0 = cStar lam := by
  have hq := (q_pos hlam).ne'
  simp only [childGapSlope, message_zero, logMass_zero, cStar]
  (try dsimp) <;> (try simp only [id_eq, Pi.pow_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply]) <;> field_simp [hq] <;> ring

theorem childGapSlope_ge_initial {lam t : ℝ} (hlam : 0 < lam) (ht : 0 ≤ t) :
    cStar lam ≤ childGapSlope lam t := by
  have hh := Envelopes.zero_le_value_of_nonneg_deriv
    (f := fun s => childGapSlope lam s - cStar lam)
    (f' := childGapCurvature lam) ht (by simp [childGapSlope_zero hlam])
    (fun s hs => (childGapSlope_hasDerivAt hlam s).sub_const (cStar lam))
    (fun s hs => childGapCurvature_nonneg hlam hs.1)
  linarith

theorem childGap_ge_tangent {lam t : ℝ} (hlam : 0 < lam) (ht : 0 ≤ t) :
    cStar lam * t ≤ childGap lam t := by
  have hh := Envelopes.zero_le_value_of_nonneg_deriv
    (f := fun s => childGap lam s - cStar lam * s)
    (f' := fun s => childGapSlope lam s - cStar lam) ht (by simp [childGap_zero hlam])
    (fun s hs => by
      exact (childGap_hasDerivAt hlam s).fun_sub
        (hasDerivAt_const_mul (cStar lam)))
    (fun s hs => sub_nonneg.mpr (childGapSlope_ge_initial hlam hs.1))
  linarith

/-- Full first inequality of (24), including the childless endpoint. -/
theorem J_le_rational_child {lam t : ℝ} (hlam : 0 < lam) (ht : 0 ≤ t) :
    J lam t ≤ q lam ^ 2 * childRatio lam t / (1 + cStar lam * childRatio lam t) := by
  have hu := message_pos hlam t
  have hphi := logMass_pos hlam t
  have hc := cStar_pos hlam
  have hr := childRatio_nonneg hlam ht
  have hden : 0 < 1 + cStar lam * childRatio lam t := by positivity
  have hg := childGap_ge_tangent hlam ht
  have hmult := mul_le_mul_of_nonneg_right hg (sq_nonneg (message lam t))
  have hcore : message lam t ^ 2 *
      (1 + cStar lam * childRatio lam t) ≤ q lam ^ 2 := by
    apply (le_of_mul_le_mul_right ?_ hphi)
    have hid : childGap lam t * message lam t ^ 2 =
        (q lam ^ 2 - message lam t ^ 2) * logMass lam t := by
      unfold childGap
      (try dsimp) <;> (try simp only [id_eq, Pi.pow_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply]) <;> field_simp [hu.ne'] <;> ring
    rw [hid] at hmult
    unfold childRatio
    field_simp [hphi.ne']
    nlinarith only [hmult]
  apply (le_div_iff₀ hden).2
  have hh := mul_le_mul_of_nonneg_right hcore hr
  have hid : J lam t = message lam t ^ 2 * childRatio lam t := by
    unfold J childRatio
    (try dsimp) <;> (try simp only [id_eq, Pi.pow_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply]) <;> ring
  rw [hid]
  nlinarith only [hh]

theorem logMass_ge_initial_tangent {lam t : ℝ} (hlam : 0 < lam) (ht : 0 ≤ t) :
    logActivity lam - q lam * t ≤ logMass lam t := by
  have hh := Envelopes.zero_le_value_of_nonneg_deriv
    (f := fun s => logMass lam s - logActivity lam + q lam * s)
    (f' := fun s => -message lam s + q lam) ht (by simp)
    (fun s hs => by
      exact ((logMass_hasDerivAt hlam s).sub_const (logActivity lam)).fun_add
        (hasDerivAt_const_mul (q lam)))
    (fun s hs => by linarith [Envelopes.message_le_q hlam hs.1])
  linarith

/-- Feasibility is exactly phi (t)<=y; no bound is asserted at y=0. -/
theorem childRatio_feasible_lower {lam t y : ℝ} (hlam : 0 < lam) (ht : 0 ≤ t)
    (hy : 0 < y) (hfeasible : logMass lam t ≤ y) :
    max 0 (logActivity lam / y - 1) / q lam ≤ childRatio lam t := by
  have hq := q_pos hlam
  have hphi := logMass_pos hlam t
  have hr := childRatio_nonneg hlam ht
  have hbase := logMass_ge_initial_tangent hlam ht
  have hfac : 0 ≤ 1 + q lam * childRatio lam t := by positivity
  have hmul := mul_le_mul_of_nonneg_right hfeasible hfac
  have hid : logMass lam t * (1 + q lam * childRatio lam t) =
      logMass lam t + q lam * t := by
    unfold childRatio
    (try dsimp) <;> (try simp only [id_eq, Pi.pow_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply]) <;> field_simp [hphi.ne'] <;> ring
  rw [hid] at hmul
  have hratio : logActivity lam / y ≤ 1 + q lam * childRatio lam t :=
    (div_le_iff₀ hy).2 (by nlinarith only [hbase, hmul])
  apply (div_le_iff₀ hq).2
  apply max_le
  · positivity
  · nlinarith only [hratio]

theorem cStar_over_q_sq_lower {lam : ℝ} (hlam : 0 < lam) (hlam7 : lam ≤ 7 / 3) :
    (120 / 91 : ℝ) ≤ cStar lam / q lam ^ 2 := by
  have hl : 0 < lam := hlam
  have h1 : 0 < 1 + lam := by linarith
  have h2 : 0 < 2 + lam := by linarith
  have hb := (Envelopes.log_star hlam.le).1
  have hb' : 2 * lam ≤ logActivity lam * (2 + lam) :=
    (div_le_iff₀ h2).mp hb
  have h7 : 0 ≤ 7 - 3 * lam := by linarith
  have hp : 0 ≤ (7 - 3 * lam) * (40 * lam + 52) :=
    mul_nonneg h7 (by positivity)
  have hm := mul_le_mul_of_nonneg_right hb' (show 0 ≤ 2 * (1 + lam) by positivity)
  have htarget : (120 / 91 : ℝ) * lam ^ 2 ≤ 2 * logActivity lam * (1 + lam) := by
    apply (mul_le_mul_iff_of_pos_right h2).mp
    have hlp := mul_nonneg hlam.le hp
    nlinarith only [hm, hlp]
  unfold cStar q
  apply (le_div_iff₀ (sq_pos_of_pos (div_pos hlam h1))).2
  field_simp [hlam.ne', h1.ne']
  nlinarith only [htarget]

theorem child_correction_den_pos {D lam y : ℝ} (hlam : 0 < lam)
    (hlam7 : lam ≤ 7 / 3) (hell : -(3 / 4 : ℝ) < ell D lam y) :
    0 < cStar lam + ell D lam y * q lam ^ 2 := by
  have hq := q_pos hlam
  have hc := (le_div_iff₀ (sq_pos_of_pos hq)).mp (cStar_over_q_sq_lower hlam hlam7)
  have he := mul_lt_mul_of_pos_right hell (sq_pos_of_pos hq)
  nlinarith [sq_pos_of_pos hq]

end Erdos993Lean.Analytic.V213.FreeCountVariance

#check Erdos993Lean.Analytic.V213.FreeCountVariance.childGap_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.childGap_hasDerivAt
#check Erdos993Lean.Analytic.V213.FreeCountVariance.childGapSlope_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.childGapSlope_hasDerivAt
#check Erdos993Lean.Analytic.V213.FreeCountVariance.childGapCurvature_nonneg
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.childGapCurvature_nonneg
#check Erdos993Lean.Analytic.V213.FreeCountVariance.childGap_zero
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.childGap_zero
#check Erdos993Lean.Analytic.V213.FreeCountVariance.childGapSlope_zero
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.childGapSlope_zero
#check Erdos993Lean.Analytic.V213.FreeCountVariance.childGapSlope_ge_initial
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.childGapSlope_ge_initial
#check Erdos993Lean.Analytic.V213.FreeCountVariance.childGap_ge_tangent
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.childGap_ge_tangent
#check Erdos993Lean.Analytic.V213.FreeCountVariance.J_le_rational_child
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.J_le_rational_child
#check Erdos993Lean.Analytic.V213.FreeCountVariance.logMass_ge_initial_tangent
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.logMass_ge_initial_tangent
#check Erdos993Lean.Analytic.V213.FreeCountVariance.childRatio_feasible_lower
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.childRatio_feasible_lower
#check Erdos993Lean.Analytic.V213.FreeCountVariance.cStar_over_q_sq_lower
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.cStar_over_q_sq_lower
#check Erdos993Lean.Analytic.V213.FreeCountVariance.child_correction_den_pos
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.child_correction_den_pos
