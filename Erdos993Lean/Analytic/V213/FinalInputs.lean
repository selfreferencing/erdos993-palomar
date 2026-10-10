module

public import Erdos993Lean.Analytic.V213.FinalAboveStartingMean
public import Erdos993Lean.Analytic.V213.Theorem51.Closed

/-! Theorem 5.1 in the per-input forest interface used in the final assembly. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

theorem theorem51_input :
  ∀ (F : FiniteForest) (i : ℕ), i < 55 → ∀ {lam : ℝ},
    lam ∈ Set.Icc (N44.Data.pieceLo.getD i 0 : ℝ) (N44.Data.pieceHi.getD i 0 : ℝ) →
    ∀ A : Finset (Fin F.n), IsMaxWeight F lam A →
      hardCoreVar F lam ≤ (1 + lowMeanFractionReal (lowMeanInputRowAt i).theta) *
        (1 - FreeCountVariance.q lam) * weightW F lam A := by
  intro F i hi lam hlam A hA
  have hrow := input_in_table_row i hi hlam
  have hpos := Theorem51.table_activity_pos hrow
  have h := Theorem51.finiteForest_variance_ratio_bound_closed F hrow A hA
  rw [(input_table_row_facts i hi).2.2] at h
  simpa only [FreeCountVariance.q_eq_actQ, one_sub_actQ hpos.le,
    div_eq_mul_inv, mul_assoc, one_mul] using h

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.theorem51_input
