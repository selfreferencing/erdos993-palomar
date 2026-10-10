module

public import Erdos993Lean.Analytic.V213.FreeCountCAChildlessPolynomials
public import Erdos993Lean.Analytic.V213.FreeCountVarianceCaps

/-! The actual childless CA face. The two N-polynomial endpoint comparisons
and the printed lambda/gamma budget are explicit scalar premises. All
normalizations, beta enclosure, and propagation to every y>=beta are proved.
This is not a completed current-cap theorem until those finite premises are
supplied by the reviewed scalar layer.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance

open Real Set

theorem CA_childless_normalized {D lam y : ℝ} (hD : 0 < D)
    (hlam : 0 < lam) (hy : 0 < y) :
    CA D lam 0 y = alpha D lam * message lam y * childlessC0 D lam y := by
  have hp := (message_pos hlam y).ne'
  have hg := (gamma_pos hD hlam).ne'
  have hb := (logActivity_pos hlam).ne'
  have hcoef : gamma D lam*q lam^2/logActivity lam^2 = (5/7)*alpha D lam := by
    unfold alpha gamma
    field_simp [hb] <;> ring
  rw [CA_zero hD hlam]
  unfold CC
  rw [E_normalized hlam hy]
  simp only [zero_div,zero_add]
  calc
    alpha D lam * (message lam y * bp lam y) + L D lam y * (q lam/logActivity lam)^2 =
        alpha D lam * (message lam y * bp lam y) +
          (L D lam y/gamma D lam)*(gamma D lam*q lam^2/logActivity lam^2) := by
            field_simp [hg,hb] <;> ring
    _ = alpha D lam * message lam y * childlessC0 D lam y := by
      rw [hcoef]
      unfold childlessC0 ell
      field_simp [hp,hg] <;> ring

theorem message_at_logActivity {lam : ℝ} (hlam : 0 < lam) :
    message lam (logActivity lam) = q lam/(1+q lam) := by
  rw [message_eq_exp_quotient hlam]
  unfold logActivity q
  rw [Real.exp_log (by linarith : 0 < 1+lam)]
  field_simp <;> ring

theorem logMass_at_logActivity {lam : ℝ} (hlam : 0 < lam) :
    logMass lam (logActivity lam) = log (1+q lam) := by
  rw [logMass_eq_log]
  unfold logActivity q
  rw [Real.exp_neg,Real.exp_log (by linarith : 0 < 1+lam)] <;> rfl

theorem ap_at_logActivity {lam : ℝ} (hlam : 0 < lam) :
    ap lam (logActivity lam) = 1/q lam := by
  unfold ap logActivity q
  rw [Real.exp_log (by linarith : 0 < 1+lam)]
  field_simp

theorem childless_B_at_logActivity {lam : ℝ} (hlam : 0 < lam) :
    B lam (logActivity lam) ≤ 1+q lam/2 ∧
      1/B lam (logActivity lam) ≤ (2+q lam)/(2*(1+q lam)) := by
  have hq := q_pos hlam
  have hq1 := q_lt_one hlam
  have hlogs := Envelopes.log_star hq.le
  have hpm := message_at_logActivity hlam
  constructor
  · unfold B
    rw [hpm,logMass_at_logActivity hlam]
    apply (div_le_iff₀ (div_pos hq (by positivity))).2
    have hid : (1+q lam/2)*(q lam/(1+q lam)) =
        q lam*(2+q lam)/(2*(1+q lam)) := by
          field_simp [show 1+q lam ≠ 0 by positivity] <;> ring
    rw [hid]
    exact hlogs.2
  · have hh := (childless_inverse_B_bounds hlam (logActivity lam)).2
    rw [hpm] at hh
    have hid : 1-(q lam/(1+q lam))/2 = (2+q lam)/(2*(1+q lam)) := by
      field_simp <;> ring
    rwa [hid] at hh

theorem logActivity_beta_endpoints {lam : ℝ} (hlam : 0 < lam) :
    betaLower (q lam) ≤ logActivity lam ∧ logActivity lam ≤ betaUpper (q lam) := by
  have hq := q_pos hlam
  have hq1 := q_lt_one hlam
  have hid : Envelopes.scalarLog (q lam) = logActivity lam := by
    have hh := logMass_eq_neg_log hlam 0
    simpa only [logMass_zero,message_zero,Envelopes.scalarLog] using hh.symm
  have hl := Envelopes.scalarLog_lower hq hq1
  have h1q : 0 < 1-q lam := by linarith
  have hu := (Envelopes.log_star
    (show 0 ≤ q lam/(1-q lam) by positivity)).2
  rw [Envelopes.log_odds_eq hq1] at hu
  have hidu : (q lam/(1-q lam))*(2+q lam/(1-q lam))/(2*(1+q lam/(1-q lam))) =
      betaUpper (q lam) := by
    unfold betaUpper
    field_simp [show 1-q lam ≠ 0 by linarith,
      show 1+q lam/(1-q lam) ≠ 0 by positivity] <;> ring
  rw [hidu] at hu
  rw [hid] at hl hu
  exact ⟨hl,hu⟩

theorem childlessP_le_scaled_C0 {D lam : ℝ} (hD : 0 < D) (hlam : 0 < lam) :
    childlessP D (q lam) (logActivity lam) ≤
      7*q lam*logActivity lam*childlessC0 D lam (logActivity lam) := by
  have hq := q_pos hlam
  have hb := logActivity_pos hlam
  have hg := gamma_pos hD hlam
  have hB := B_pos hlam (logActivity lam)
  have hBounds := childless_B_at_logActivity hlam
  have hBterm := mul_le_mul_of_nonneg_left hBounds.1 (by positivity : 0 ≤ 7*q lam)
  have hInvterm := mul_le_mul_of_nonneg_left hBounds.2
    (by positivity : 0 ≤ 5*q lam*logActivity lam^2)
  have hid : 7*q lam*logActivity lam*childlessC0 D lam (logActivity lam) =
      12*logActivity lam-7*q lam*B lam (logActivity lam) -
      12*q lam*logActivity lam/(D*(1+q lam)) -
      5*q lam*logActivity lam^2*(1/B lam (logActivity lam)) := by
    unfold childlessC0 bp
    rw [ell_normalized hD hlam,h_normalized hlam,ap_at_logActivity hlam,
      message_at_logActivity hlam]
    unfold gamma
    field_simp [hD.ne',hq.ne',hb.ne',hB.ne',show 1+q lam ≠ 0 by positivity] <;> ring
  rw [hid]
  unfold childlessP
  simp only [mul_div_assoc] at hInvterm ⊢
  linarith only [hBterm,hInvterm]

theorem childlessC0_at_beta_pos {D lam r : ℝ} (hD : 6/5 ≤ D)
    (hl : 1/3 ≤ lam) (hu : lam ≤ 7/3) (hqr : q lam ≤ r) (hr : r ≤ 7/10)
    (hN4 : 0 < childlessN4 D r) (hN5 : 0 < childlessN5 D r) :
    0 < childlessC0 D lam (logActivity lam) := by
  have hlam : 0 < lam := by linarith
  have hDp : 0 < D := by linarith
  have hq := q_pos hlam
  have hb := logActivity_pos hlam
  have hbet := logActivity_beta_endpoints hlam
  have hP := childlessP_pos_of_upper_endpoint hD (q_closed_domain hl hu).1 hqr hr
    hN4 hN5 hbet.1 hbet.2
  have hbnd := childlessP_le_scaled_C0 hDp hlam
  have hmul : 0 < 7*q lam*logActivity lam := by positivity
  exact (mul_pos_iff_of_pos_left hmul).1 (hP.trans_le hbnd)

/-- The whole physical t=0 face, from the literal cap endpoint premises. -/
theorem CA_pos_on_childless_face {D lam r y : ℝ} (hD : 6/5 ≤ D)
    (hl : 1/3 ≤ lam) (hu : lam ≤ 7/3) (hqr : q lam ≤ r) (hr : r ≤ 7/10)
    (hN4 : 0 < childlessN4 D r) (hN5 : 0 < childlessN5 D r)
    (hbudget : lam/gamma D lam ≤ 10/3) (hy : logActivity lam ≤ y) :
    0 < CA D lam 0 y := by
  have hlam : 0 < lam := by linarith
  have hDp : 0 < D := by linarith
  have hb := logActivity_pos hlam
  have hyp : 0 < y := hb.trans_le hy
  have hstart := childlessC0_at_beta_pos hD hl hu hqr hr hN4 hN5
  have hmono := (childlessC0_strictMono hDp hl hu hbudget).monotoneOn
  have hC : 0 < childlessC0 D lam y :=
    hstart.trans_le (hmono hb hyp hy)
  rw [CA_childless_normalized hDp hlam hyp]
  exact mul_pos (mul_pos (alpha_pos hDp hlam) (message_pos hlam y)) hC

end Erdos993Lean.Analytic.V213.FreeCountVariance

#check Erdos993Lean.Analytic.V213.FreeCountVariance.CA_childless_normalized
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.CA_childless_normalized
#check Erdos993Lean.Analytic.V213.FreeCountVariance.message_at_logActivity
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.message_at_logActivity
#check Erdos993Lean.Analytic.V213.FreeCountVariance.logMass_at_logActivity
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.logMass_at_logActivity
#check Erdos993Lean.Analytic.V213.FreeCountVariance.ap_at_logActivity
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.ap_at_logActivity
#check Erdos993Lean.Analytic.V213.FreeCountVariance.childless_B_at_logActivity
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.childless_B_at_logActivity
#check Erdos993Lean.Analytic.V213.FreeCountVariance.logActivity_beta_endpoints
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.logActivity_beta_endpoints
#check Erdos993Lean.Analytic.V213.FreeCountVariance.childlessP_le_scaled_C0
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.childlessP_le_scaled_C0
#check Erdos993Lean.Analytic.V213.FreeCountVariance.childlessC0_at_beta_pos
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.childlessC0_at_beta_pos
#check Erdos993Lean.Analytic.V213.FreeCountVariance.CA_pos_on_childless_face
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.CA_pos_on_childless_face
