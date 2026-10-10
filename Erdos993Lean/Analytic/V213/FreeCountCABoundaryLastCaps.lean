module

public import Erdos993Lean.Analytic.V213.FreeCountCABoundaryReduction

/-! Remaining-three-cap child monotonicity and actual least-feasible-child reduction.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance
open Real Set Envelopes

theorem CA_child_strictMono_last_three {D lam y : ℝ}
    (hD : 0 < D) (hlam3 : 3/2 ≤ lam) (hlam7 : lam ≤ 7/3) (hy : 0 < y)
    (hell : ell D lam y ≤ 0) (hellLower : -(1/2 : ℝ) ≤ ell D lam y)
    (hden : ∀ s : ℝ, 0 ≤ s → 3/4 ≤ 1+ell D lam y*J lam s) :
    StrictMonoOn (fun s => CA D lam s y/message lam y) (Ici 0) := by
  have hlam : 0 < lam := by linarith
  apply CA_child_strictMono_of_budget hD hlam hy (by norm_num : (0 : ℝ) ≤ 2/3) hell
    (by norm_num; exact hellLower) hden
  intro s hs
  simpa only [show (2/3 : ℝ)^2 = 4/9 by norm_num] using
    child_budget_last_three hD hlam3 hlam7 hs


theorem CA_boundary_lower_last_three {D lam t y : ℝ}
    (hD : 0 < D) (hlam3 : 3/2 ≤ lam) (hlam7 : lam ≤ 7/3) (ht : 0 ≤ t) (hy : 0 < y)
    (hfeasible : logMass lam t ≤ y)
    (hell : ell D lam y ≤ 0) (hellLower : -(1/2 : ℝ) ≤ ell D lam y)
    (hden : ∀ s : ℝ, 0 ≤ s → 3/4 ≤ 1+ell D lam y*J lam s) :
    CA D lam (if logActivity lam ≤ y then 0 else leastChild lam y) y ≤ CA D lam t y := by
  have hlam : 0 < lam := by linarith
  have hm := (CA_child_strictMono_last_three hD hlam3 hlam7 hy hell hellLower hden).monotoneOn
  have hp := message_pos hlam y
  by_cases hb : logActivity lam ≤ y
  · simp only [if_pos hb]
    have hh := hm (show (0 : ℝ) ∈ Ici 0 from (show (0 : ℝ) ≤ 0 from le_rfl)) ht ht
    exact (div_le_div_iff_of_pos_right hp).mp hh
  · simp only [if_neg hb]
    have hs := leastChild_nonneg hlam hy (le_of_lt (lt_of_not_ge hb))
    have hst := leastChild_le_feasible hlam hy hfeasible
    have hh := hm hs ht hst
    exact (div_le_div_iff_of_pos_right hp).mp hh


end Erdos993Lean.Analytic.V213.FreeCountVariance

#check Erdos993Lean.Analytic.V213.FreeCountVariance.CA_child_strictMono_last_three
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.CA_child_strictMono_last_three
#check Erdos993Lean.Analytic.V213.FreeCountVariance.CA_boundary_lower_last_three
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.CA_boundary_lower_last_three
