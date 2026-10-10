module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceDefs
public import Erdos993Lean.Analytic.Reserve.Entropy

/-!
Actual current (19), its Pinsker consequence and
the CC / positive-ell CA implications. The existing generic entropy proof
has the same message and logMass definitions.
No old cap or completed
variance theorem is used here.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance

open Real

theorem entropy_identity {lam y : ℝ} (hlam : 0 < lam) (hy : 0 < y) (t : ℝ) :
    E lam t y * logMass lam t =
      (message lam y * (log (message lam y)-log (message lam t)) +
        (1-message lam y) *
          (log (1-message lam y)-log (1-message lam t))) +
      (y-logMass lam t)*(message lam y+logMass lam y/y) := by
  have hk := Reserve.Entropy.kl_msg hlam t y
  have he := Reserve.Entropy.coefE_mul_lmass hlam t y hy.ne'
  change message lam y * (log (message lam y)-log (message lam t)) +
    (1-message lam y) * (log (1-message lam y)-log (1-message lam t)) =
    message lam y*(t-y)+logMass lam t-logMass lam y at hk
  change E lam t y * logMass lam t =
    (message lam y*(t-y)+logMass lam t-logMass lam y) +
      (y-logMass lam t)*(message lam y+logMass lam y/y) at he
  rwa [← hk] at he

theorem E_pinsker {lam t y : ℝ} (hlam : 0 < lam) (ht : 0 ≤ t)
    (hfeasible : logMass lam t ≤ y) :
    2*(message lam y-message lam t)^2 +
      (y-logMass lam t)*(message lam y+logMass lam y/y) ≤
      E lam t y * logMass lam t :=
  (Reserve.entropyOK lam t y hlam ht hfeasible).2

theorem E_nonneg {lam t y : ℝ} (hlam : 0 < lam) (ht : 0 ≤ t)
    (hfeasible : logMass lam t ≤ y) : 0 ≤ E lam t y :=
  (Reserve.entropyOK lam t y hlam ht hfeasible).1

theorem CC_nonneg {D lam t y : ℝ} (hD : 0 < D) (hlam : 0 < lam)
    (ht : 0 ≤ t) (hfeasible : logMass lam t ≤ y) : 0 ≤ CC D lam t y := by
  exact mul_nonneg (alpha_pos hD hlam).le (E_nonneg hlam ht hfeasible)

theorem CA_pos_of_ell_pos {D lam t y : ℝ} (hD : 0 < D) (hlam : 0 < lam)
    (ht : 0 ≤ t) (hfeasible : logMass lam t ≤ y)
    (hell : 0 < ell D lam y) : 0 < CA D lam t y := by
  have hp := message_pos hlam y
  have hg := gamma_pos hD hlam
  have hpg := mul_pos hp hg
  have hL : 0 < L D lam y := by
    unfold ell at hell
    have hh := (lt_div_iff₀ hpg).mp hell
    simpa only [zero_mul] using hh
  have hJ : 0 ≤ J lam t := by
    unfold J
    exact div_nonneg (mul_nonneg (sq_nonneg _) ht) (logMass_pos hlam t).le
  have hZ : 0 < Z D lam t y := by
    unfold Z
    exact add_pos_of_pos_of_nonneg hpg (mul_nonneg hL.le hJ)
  have hu := div_pos (message_pos hlam t) (logMass_pos hlam t)
  have hfirst : 0 ≤ alpha D lam * E lam t y :=
    mul_nonneg (alpha_pos hD hlam).le (E_nonneg hlam ht hfeasible)
  unfold CA
  exact add_pos_of_nonneg_of_pos hfirst
    (div_pos (mul_pos (mul_pos hpg hL) (sq_pos_of_pos hu)) hZ)

end Erdos993Lean.Analytic.V213.FreeCountVariance

#check Erdos993Lean.Analytic.V213.FreeCountVariance.entropy_identity
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.entropy_identity
#check Erdos993Lean.Analytic.V213.FreeCountVariance.E_pinsker
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.E_pinsker
#check Erdos993Lean.Analytic.V213.FreeCountVariance.E_nonneg
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.E_nonneg
#check Erdos993Lean.Analytic.V213.FreeCountVariance.CC_nonneg
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.CC_nonneg
#check Erdos993Lean.Analytic.V213.FreeCountVariance.CA_pos_of_ell_pos
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.CA_pos_of_ell_pos

