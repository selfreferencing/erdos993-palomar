module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceEntropy
public import Erdos993Lean.Analytic.V213.FreeCountRealScalarBounds

/-!
The actual feasible-face inequality (23).
The printed J bound and positive 1+j ell are explicit scalar premises;
no finite worksheet or unproved face positivity is assumed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance
open Real Envelopes

theorem negative_quotient_increases_with_denominator {n d0 d : ℝ}
    (hn : n ≤ 0) (hd0 : 0 < d0) (hdd : d0 ≤ d) : n/d0 ≤ n/d := by
  have hd : 0 < d := hd0.trans_le hdd
  apply (div_le_div_iff₀ hd0 hd).2
  exact mul_le_mul_of_nonpos_left hdd hn

theorem gamma_div_alpha {D lam : ℝ} (hD : 0 < D) (hlam : 0 < lam) :
    gamma D lam/alpha D lam = 5*logActivity lam^2/(7*q lam^2) := by
  have hDn := hD.ne'
  have hb := (logActivity_pos hlam).ne'
  have hq := (q_pos hlam).ne'
  unfold gamma alpha
  field_simp [hDn, hb, hq] <;> ring

theorem face_correction_identity {D lam t y : ℝ} (hD : 0 < D)
    (hlam : 0 < lam) (hface : y = logMass lam t)
    (hden : 0 < 1+ell D lam y*J lam t) :
    y*CA D lam t y/alpha D lam = y*E lam t y +
      (gamma D lam/alpha D lam)*(message lam t^2/logMass lam t)*
        (message lam y*ell D lam y)/(1+ell D lam y*J lam t) := by
  subst y
  have hp := (message_pos hlam (logMass lam t)).ne'
  have hg := (gamma_pos hD hlam).ne'
  have ha := (alpha_pos hD hlam).ne'
  have hf := (logMass_pos hlam t).ne'
  have hL : L D lam (logMass lam t) =
      message lam (logMass lam t)*gamma D lam*ell D lam (logMass lam t) := by
    unfold ell
    field_simp [hp, hg]
  unfold CA
  rw [Z_normalized hD hlam, hL]
  field_simp [ha, hp, hg, hf, hden.ne'] <;> ring

theorem scaled_child_square_bound {D lam t : ℝ} (hD : 0 < D)
    (hlam : 0 < lam) (hlam7 : lam ≤ 7/3) (ht : 0 ≤ t) :
    (gamma D lam/alpha D lam)*(message lam t^2/logMass lam t) ≤
      5*logActivity lam/7 := by
  have hb := logActivity_pos hlam
  have hq := q_pos hlam
  rw [gamma_div_alpha hD hlam]
  have hc : 0 ≤ 5*logActivity lam^2/(7*q lam^2) := by positivity
  have hm := mul_le_mul_of_nonneg_left (message_square_over_logMass_le hlam hlam7 ht) hc
  have hid : (5*logActivity lam^2/(7*q lam^2))*(q lam^2/logActivity lam) =
      5*logActivity lam/7 := by
    field_simp [hb.ne', hq.ne'] <;> ring
  rwa [hid] at hm

/-- Exactly (23), with the current messages, actual entropy, and closed ell=0
case included. It supplies an inequality, not an assumed positive face. -/
theorem CA_feasible_face_lower {D lam t y j : ℝ} (hD : 0 < D)
    (hlam : 0 < lam) (hlam7 : lam ≤ 7/3) (ht : 0 ≤ t)
    (hface : y = logMass lam t) (hell : ell D lam y ≤ 0)
    (hJ : J lam t < j) (hden0 : 0 < 1+j*ell D lam y) :
    2*(message lam y-message lam t)^2 +
        (5/7)*logActivity lam*message lam y*ell D lam y/(1+j*ell D lam y) ≤
      y*CA D lam t y/alpha D lam := by
  have hy := (logMass_pos hlam t)
  have hfeasible : logMass lam t ≤ y := by rw [hface]
  have he := E_pinsker hlam ht hfeasible
  have he' : 2*(message lam y-message lam t)^2 ≤ y*E lam t y := by
    simpa only [hface, sub_self, zero_mul, add_zero, mul_comm] using he
  have hdd : 1+j*ell D lam y ≤ 1+ell D lam y*J lam t := by
    have hh := mul_le_mul_of_nonpos_left hJ.le hell
    nlinarith only [hh]
  have hden : 0 < 1+ell D lam y*J lam t := hden0.trans_le hdd
  have hb := logActivity_pos hlam
  have hp := message_pos hlam y
  have hn : (5/7)*logActivity lam*message lam y*ell D lam y ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) hell
  have hquot := negative_quotient_increases_with_denominator hn hden0 hdd
  have hm : message lam y*ell D lam y/(1+ell D lam y*J lam t) ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (message_pos hlam y).le hell) hden.le
  have hscaled := mul_le_mul_of_nonpos_right (scaled_child_square_bound hD hlam hlam7 ht) hm
  have hscaled' : (5/7)*logActivity lam*message lam y*ell D lam y/
        (1+ell D lam y*J lam t) ≤
      (gamma D lam/alpha D lam)*(message lam t^2/logMass lam t)*
        (message lam y*ell D lam y)/(1+ell D lam y*J lam t) := by
    convert hscaled using 1 <;> ring
  rw [face_correction_identity hD hlam hface hden]
  exact add_le_add he' (hquot.trans hscaled')

end Erdos993Lean.Analytic.V213.FreeCountVariance

#check Erdos993Lean.Analytic.V213.FreeCountVariance.negative_quotient_increases_with_denominator
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.negative_quotient_increases_with_denominator
#check Erdos993Lean.Analytic.V213.FreeCountVariance.gamma_div_alpha
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.gamma_div_alpha
#check Erdos993Lean.Analytic.V213.FreeCountVariance.face_correction_identity
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.face_correction_identity
#check Erdos993Lean.Analytic.V213.FreeCountVariance.scaled_child_square_bound
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.scaled_child_square_bound
#check Erdos993Lean.Analytic.V213.FreeCountVariance.CA_feasible_face_lower
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.CA_feasible_face_lower
