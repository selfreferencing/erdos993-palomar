module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceDefs
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!+# Exact derivatives for the current free-count reserve

Source: current Section 3, equations (15)--(17) and the childless-child
paragraph. Activity is strictly positive and D is fixed. These identities do
not differentiate the selected five-cap function across one of its seams.
No finite worksheet, completed variance theorem, or analytic sign premise is
used here. All y-derivative formulas that divide by y state y != 0 explicitly.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance

open Real

theorem message_hasDerivAt {lam : ℝ} (hlam : 0 < lam) (x : ℝ) :
    HasDerivAt (message lam) (-message lam x * (1 - message lam x)) x := by
  have hd : exp x + lam ≠ 0 := ne_of_gt (by positivity)
  have hr : message lam = fun z => lam / (exp z + lam) := by
    funext z
    exact message_eq_exp_quotient hlam z
  rw [hr]
  apply ((hasDerivAt_const x lam).div ((Real.hasDerivAt_exp x).add_const lam) hd).congr_deriv
  (try simp only [id_eq]) <;> field_simp [hd] <;> ring

theorem logMass_hasDerivAt {lam : ℝ} (hlam : 0 < lam) (x : ℝ) :
    HasDerivAt (logMass lam) (-message lam x) x := by
  have hd : 1 + lam * exp (-x) ≠ 0 := ne_of_gt (by positivity)
  have hdif := ((((hasDerivAt_id x).neg.exp).const_mul lam).const_add 1).log hd
  change HasDerivAt (fun z => log (1 + lam * exp (-z))) (-message lam x) x
  apply hdif.congr_deriv
  simp [message, Reserve.msg] <;> ring

theorem message_hasDerivAt_activity {lam : ℝ} (hlam : 0 < lam) (x : ℝ) :
    HasDerivAt (fun a => message a x)
      (message lam x * (1 - message lam x) / lam) lam := by
  have hd : 1 + lam * exp (-x) ≠ 0 := ne_of_gt (by positivity)
  have hnum := (hasDerivAt_id lam).mul_const (exp (-x))
  have hdif := hnum.div (hnum.const_add 1) hd
  change HasDerivAt (fun a => a * exp (-x) / (1 + a * exp (-x))) _ lam
  apply hdif.congr_deriv
  unfold message Reserve.msg
  (try simp only [id_eq]) <;> field_simp [hlam.ne', hd] <;> ring

theorem logMass_hasDerivAt_activity {lam : ℝ} (hlam : 0 < lam) (x : ℝ) :
    HasDerivAt (fun a => logMass a x) (message lam x / lam) lam := by
  have hd : 1 + lam * exp (-x) ≠ 0 := ne_of_gt (by positivity)
  have hdif := (((hasDerivAt_id lam).mul_const (exp (-x))).const_add 1).log hd
  change HasDerivAt (fun a => log (1 + a * exp (-x))) _ lam
  apply hdif.congr_deriv
  unfold message Reserve.msg
  (try simp only [id_eq]) <;> field_simp [hlam.ne', hd] <;> ring

theorem ap_hasDerivAt {lam : ℝ} (hlam : 0 < lam) (y : ℝ) :
    HasDerivAt (ap lam) (ap lam y) y := by
  unfold ap
  exact (Real.hasDerivAt_exp y).div_const lam

/-- The paper's varpi = 1 - (1-p) B. -/
noncomputable def varpi (lam y : ℝ) : ℝ :=
  1 - (1 - message lam y) * B lam y

/-- This sign uses only log x >= 1 - 1/x, not a tabulated bound. -/
theorem varpi_nonneg {lam : ℝ} (hlam : 0 < lam) (y : ℝ) : 0 ≤ varpi lam y := by
  have hp := message_pos hlam y
  have hk : 0 < 1 - message lam y := sub_pos.mpr (message_lt_one hlam y)
  have hlog := Real.one_sub_inv_le_log_of_pos hk
  have hmul := mul_le_mul_of_nonneg_left hlog hk.le
  have hid : (1 - message lam y) * (1 - (1 - message lam y)⁻¹) =
      -message lam y := by
    field_simp [hk.ne']
    ring
  rw [hid] at hmul
  have hf : (1 - message lam y) * logMass lam y ≤ message lam y := by
    rw [logMass_eq_neg_log hlam]
    nlinarith
  unfold varpi B
  apply sub_nonneg.mpr
  rw [← mul_div_assoc, div_le_iff₀ hp]
  simpa only [one_mul] using hf

theorem B_hasDerivAt {lam : ℝ} (hlam : 0 < lam) (y : ℝ) :
    HasDerivAt (B lam) (-varpi lam y) y := by
  have hp := (message_pos hlam y).ne'
  have hdif := (logMass_hasDerivAt hlam y).div (message_hasDerivAt hlam y) hp
  change HasDerivAt (fun z => logMass lam z / message lam z) _ y
  apply hdif.congr_deriv
  unfold varpi B
  (try simp only [id_eq]) <;> field_simp [hp] <;> ring

theorem h_hasDerivAt {D lam : ℝ} (hlam : 0 < lam) (y : ℝ) :
    HasDerivAt (h D lam)
      (message lam y * (1 - message lam y) +
        gamma D lam * varpi lam y / B lam y ^ 2) y := by
  have hB := (B_pos hlam y).ne'
  have hr : h D lam = fun z => 1 - message lam z + gamma D lam / B lam z := by
    funext z
    exact h_normalized hlam z
  rw [hr]
  apply (((message_hasDerivAt hlam y).const_sub 1).add
    ((hasDerivAt_const y (gamma D lam)).div (B_hasDerivAt hlam y) hB)).congr_deriv
  (try simp only [id_eq]) <;> ring

theorem h_deriv_pos {D lam : ℝ} (hD : 0 < D) (hlam : 0 < lam) (y : ℝ) :
    0 < deriv (h D lam) y := by
  rw [(h_hasDerivAt (D := D) hlam y).deriv]
  have hp := message_pos hlam y
  have hk : 0 < 1 - message lam y := sub_pos.mpr (message_lt_one hlam y)
  have hg := gamma_pos hD hlam
  have hv := varpi_nonneg hlam y
  have hB := B_pos hlam y
  positivity

theorem bp_hasDerivAt {lam y : ℝ} (hlam : 0 < lam) (hy : y ≠ 0) :
    HasDerivAt (bp lam)
      (ap lam y + varpi lam y / y + B lam y / y ^ 2) y := by
  have hdif := (ap_hasDerivAt hlam y).sub ((B_hasDerivAt hlam y).div (hasDerivAt_id y) hy)
  change HasDerivAt (fun z => ap lam z - B lam z / z) _ y
  apply hdif.congr_deriv
  (try simp only [id_eq]) <;> field_simp [hy] <;> ring

theorem ell_hasDerivAt {D lam : ℝ} (hD : 0 < D) (hlam : 0 < lam) (y : ℝ) :
    HasDerivAt (ell D lam)
      (ap lam y - h D lam y / gamma D lam -
        y * (message lam y * (1 - message lam y) +
          gamma D lam * varpi lam y / B lam y ^ 2) / gamma D lam) y := by
  have hr : ell D lam = fun z => ap lam z - z * h D lam z / gamma D lam := by
    funext z
    exact ell_normalized hD hlam z
  rw [hr]
  apply ((ap_hasDerivAt hlam y).sub
    (((hasDerivAt_id y).mul (h_hasDerivAt (D := D) hlam y)).div_const (gamma D lam))).congr_deriv
  (try simp only [id_eq]) <;> ring

/-- C0 is the normalized t=0 comparison; its identification with CA is in the
boundary layer. This theorem records only its exact derivative. -/
theorem childless_expression_hasDerivAt {D lam y : ℝ}
    (hD : 0 < D) (hlam : 0 < lam) (hy : y ≠ 0) :
    HasDerivAt (fun z => bp lam z + (5 / 7 : ℝ) * ell D lam z)
      (ap lam y + varpi lam y / y + B lam y / y ^ 2 +
        (5 / 7 : ℝ) * (ap lam y - h D lam y / gamma D lam -
          y * (message lam y * (1 - message lam y) +
            gamma D lam * varpi lam y / B lam y ^ 2) / gamma D lam)) y := by
  exact (bp_hasDerivAt hlam hy).add ((ell_hasDerivAt hD hlam y).const_mul (5 / 7))

end Erdos993Lean.Analytic.V213.FreeCountVariance

#check Erdos993Lean.Analytic.V213.FreeCountVariance.message_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.message_hasDerivAt
#check Erdos993Lean.Analytic.V213.FreeCountVariance.logMass_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.logMass_hasDerivAt
#check Erdos993Lean.Analytic.V213.FreeCountVariance.message_hasDerivAt_activity
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.message_hasDerivAt_activity
#check Erdos993Lean.Analytic.V213.FreeCountVariance.logMass_hasDerivAt_activity
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.logMass_hasDerivAt_activity
#check Erdos993Lean.Analytic.V213.FreeCountVariance.ap_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.ap_hasDerivAt
#check Erdos993Lean.Analytic.V213.FreeCountVariance.varpi_nonneg
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.varpi_nonneg
#check Erdos993Lean.Analytic.V213.FreeCountVariance.B_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.B_hasDerivAt
#check Erdos993Lean.Analytic.V213.FreeCountVariance.h_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.h_hasDerivAt
#check Erdos993Lean.Analytic.V213.FreeCountVariance.h_deriv_pos
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.h_deriv_pos
#check Erdos993Lean.Analytic.V213.FreeCountVariance.bp_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.bp_hasDerivAt
#check Erdos993Lean.Analytic.V213.FreeCountVariance.ell_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.ell_hasDerivAt
#check Erdos993Lean.Analytic.V213.FreeCountVariance.childless_expression_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.childless_expression_hasDerivAt
