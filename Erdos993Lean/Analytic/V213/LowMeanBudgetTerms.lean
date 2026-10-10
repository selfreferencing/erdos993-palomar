module

public import Erdos993Lean.Analytic.V213.LowMeanBudgetAll

/-!
The printed F list combines equal exponent pairs and omits zero terms.
Every checked budget already binds the combined coefficients and checks
nonzero coefficients; this additional check establishes distinct powers
for every actual exported list, not merely equality of monomial sums.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

theorem lowMean_budget_terms_distinct_kernel :
    (List.range 1114).all (fun i => decide (((lowMeanBudgetAt i).input.terms.map fun t => t.2).Nodup)) = true := by
  decide +kernel

theorem lowMean_budget_terms_distinct (i : ℕ) (hi : i < 1114) :
    ((lowMeanBudgetAt i).input.terms.map fun t => t.2).Nodup := by
  exact of_decide_eq_true (Erdos993Lean.F4Fast.forall_lt_of_range_all lowMean_budget_terms_distinct_kernel i hi)

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMean_budget_terms_distinct_kernel
