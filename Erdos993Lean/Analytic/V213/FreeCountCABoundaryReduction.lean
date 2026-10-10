module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceChildBudget

/-!
Current Section3 CA boundary reduction. Explicit ell and
normalized-denominator bounds are future scalar premises. Actual cap
budgets and h0 bounds discharge the derivative cost. Least feasible child
uses the genuine logMass, including its physical t=0 branch.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance
open Real Set Envelopes

noncomputable def leastChild (lam y : ℝ) : ℝ := log (lam/(exp y-1))

theorem logMass_strictAnti {lam : ℝ} (hlam : 0 < lam) : StrictAnti (logMass lam) := by
  apply strictAnti_of_deriv_neg
  intro t
  rw [(logMass_hasDerivAt hlam t).deriv]
  exact neg_neg_of_pos (message_pos hlam t)

theorem leastChild_nonneg {lam y : ℝ} (hlam : 0 < lam) (hy : 0 < y)
    (hybeta : y ≤ logActivity lam) : 0 ≤ leastChild lam y := by
  have he : 0 < exp y-1 := by
    have := Real.one_lt_exp_iff.mpr hy
    linarith
  have hex : exp y ≤ 1+lam := by
    have hx := Real.exp_le_exp.mpr hybeta
    simpa only [logActivity, Real.exp_log (by linarith : 0 < 1+lam)] using hx
  unfold leastChild
  apply Real.log_nonneg
  exact (le_div_iff₀ he).2 (by linarith)

theorem logMass_leastChild {lam y : ℝ} (hlam : 0 < lam) (hy : 0 < y) :
    logMass lam (leastChild lam y) = y := by
  have he : 0 < exp y-1 := by
    have := Real.one_lt_exp_iff.mpr hy
    linarith
  have hquot : 0 < lam/(exp y-1) := div_pos hlam he
  have hex : exp (-leastChild lam y) = (lam/(exp y-1))⁻¹ := by
    rw [leastChild, Real.exp_neg, Real.exp_log hquot]
  rw [logMass_eq_log, hex]
  have hid : 1+lam*(lam/(exp y-1))⁻¹ = exp y := by
    field_simp [hlam.ne', he.ne'] <;> ring
  rw [hid, Real.log_exp]

theorem leastChild_le_feasible {lam t y : ℝ} (hlam : 0 < lam) (hy : 0 < y)
    (hfeasible : logMass lam t ≤ y) : leastChild lam y ≤ t := by
  apply le_of_not_gt
  intro hlt
  have hh := logMass_strictAnti hlam hlt
  rw [logMass_leastChild hlam hy] at hh
  linarith

theorem CA_child_strictMono_of_budget {D lam y c : ℝ}
    (hD : 0 < D) (hlam : 0 < lam) (hy : 0 < y) (hc : 0 ≤ c)
    (hell : ell D lam y ≤ 0) (hellLower : -c*(3/4) ≤ ell D lam y)
    (hden : ∀ s : ℝ, 0 ≤ s → 3/4 ≤ 1+ell D lam y*J lam s)
    (hbudget : ∀ s : ℝ, 0 ≤ s → gamma D lam*message lam s^2*
      (c*childH lam s+c^2*childH lam s^2) < alpha D lam) :
    StrictMonoOn (fun s => CA D lam s y/message lam y) (Ici 0) := by
  have hd : ∀ s : ℝ, 0 ≤ s → 0 < 1+ell D lam y*J lam s := by
    intro s hs
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3/4) (hden s hs)
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
  · intro s hs
    exact (CA_div_message_hasDerivAt hD hlam hy s (hd s hs).ne').continuousAt.continuousWithinAt
  · intro s hs
    have hs0 : 0 ≤ s := interior_subset hs
    have hlow : -(c*(3/4)) ≤ ell D lam y := by nlinarith only [hellLower]
    have hw := negative_child_weight_le hell hlow
      (by norm_num : (0 : ℝ) < 3/4) hc rfl (hden s hs0)
    exact CA_deriv_pos_of_child_budget hD hlam hs0 hy hell (hd s hs0) hc hw.2
      (message_scalarH_bounds hlam s).2 (hbudget s hs0)

theorem CA_child_strictMono_first_two {D lam y : ℝ}
    (hD : 0 < D) (hlam : 0 < lam) (hlam3 : lam ≤ 3/2) (hy : 0 < y)
    (hell : ell D lam y ≤ 0) (hellLower : -(3/4 : ℝ) ≤ ell D lam y)
    (hden : ∀ s : ℝ, 0 ≤ s → 3/4 ≤ 1+ell D lam y*J lam s) :
    StrictMonoOn (fun s => CA D lam s y/message lam y) (Ici 0) := by
  apply CA_child_strictMono_of_budget hD hlam hy (by norm_num : (0 : ℝ) ≤ 1) hell
    (by simpa only [neg_mul, one_mul] using hellLower) hden
  intro s hs
  simpa only [one_mul, one_pow] using child_budget_first_two hD hlam hlam3 hs


theorem CA_boundary_lower_first_two {D lam t y : ℝ}
    (hD : 0 < D) (hlam : 0 < lam) (hlam3 : lam ≤ 3/2) (ht : 0 ≤ t) (hy : 0 < y)
    (hfeasible : logMass lam t ≤ y)
    (hell : ell D lam y ≤ 0) (hellLower : -(3/4 : ℝ) ≤ ell D lam y)
    (hden : ∀ s : ℝ, 0 ≤ s → 3/4 ≤ 1+ell D lam y*J lam s) :
    CA D lam (if logActivity lam ≤ y then 0 else leastChild lam y) y ≤ CA D lam t y := by
  have hm := (CA_child_strictMono_first_two hD hlam hlam3 hy hell hellLower hden).monotoneOn
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

#check Erdos993Lean.Analytic.V213.FreeCountVariance.logMass_strictAnti
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.logMass_strictAnti
#check Erdos993Lean.Analytic.V213.FreeCountVariance.leastChild_nonneg
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.leastChild_nonneg
#check Erdos993Lean.Analytic.V213.FreeCountVariance.logMass_leastChild
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.logMass_leastChild
#check Erdos993Lean.Analytic.V213.FreeCountVariance.leastChild_le_feasible
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.leastChild_le_feasible
#check Erdos993Lean.Analytic.V213.FreeCountVariance.CA_child_strictMono_of_budget
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.CA_child_strictMono_of_budget
#check Erdos993Lean.Analytic.V213.FreeCountVariance.CA_child_strictMono_first_two
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.CA_child_strictMono_first_two
#check Erdos993Lean.Analytic.V213.FreeCountVariance.CA_boundary_lower_first_two
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.CA_boundary_lower_first_two
