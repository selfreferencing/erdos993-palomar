module

public import Erdos993Lean.Analytic.V213.ZeroTiltLaplaceRates
public import Erdos993Lean.Analytic.V213.ZeroTiltLaplaceMobius

/-! Assembly of the actual current Lemma4.2. No finite family is used. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace

theorem scalar_bounds {lam : ℝ} (h : ActivityDomain lam) :
    0 < ellH lam ∧ ellH lam ≤ q lam ∧ ellH lam < 12/25 ∧
    7/300 ≤ a lam ∧ a lam ≤ 31/300 ∧ a lam < 11/100 ∧
    ellH lam ≤ (1-a lam)*q lam*(1-q lam)*(1+q lam)^2 ∧
    wMinus (q lam) ≤ w lam ∧ w lam ≤ wPlus (q lam) ∧
    wPlus (q lam) < 3/5 ∧ w lam ≤ q lam ∧
    (∀ t : ℝ, 0 < t → f lam t ≤ Pi lam t) ∧
    (∀ p : ℝ, 0 < p → p < q lam → b p ≤ H lam p) := by
  have hlam : 0 < lam := by linarith [h.1]
  have hr := activity_rate_bounds h
  have ha := a_bounds h
  have hw := w_mobius_bounds hlam
  exact ⟨hr.1, hr.2.1, hr.2.2.1, ha.1, ha.2.1, ha.2.2, hr.2.2.2,
    hw.2.1, hw.2.2, wPlus_lt_three_fifths (q_domain h), w_le_q hlam,
    fun _ ht => Pi_ge_f h ht, fun _ hp hpq => H_ge_b h hp hpq⟩

end Erdos993Lean.Analytic.V213.ZeroTiltLaplace

-- Audit commands.
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.scalar_bounds
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.scalar_bounds
