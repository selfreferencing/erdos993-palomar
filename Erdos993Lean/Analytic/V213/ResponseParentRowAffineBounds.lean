module

public import Erdos993Lean.Analytic.V213.ResponseParentRowDBounds
public import Erdos993Lean.Analytic.V213.ResponseParentRowE1Bounds
public import Erdos993Lean.Analytic.V213.ResponseParentRowE2Bounds
public import Erdos993Lean.Analytic.V213.ResponseParentRowHBounds

/-! Ported to the Lean module system for the Palomar registry. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows

/-- All four original affine fields are positive throughout every closed parent row. -/
theorem all_rows_fields_positive {i : Fin 4} {lam : ℝ} (h : inRow i lam) :
    0 < alpha i lam ∧ 0 < beta i lam ∧ 0 < gamma i lam ∧ 0 < delta i lam := by
  fin_cases i
  · exact D_fields_positive h
  · exact E1_fields_positive h
  · exact E2_fields_positive h
  · exact H_fields_positive h

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.all_rows_fields_positive
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.all_rows_fields_positive
