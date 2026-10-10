module

public import Erdos993Lean.Analytic.V213.ResponseParentRowRecords

/-! Names for the exact parent-field expressions in T7 Sections 5.3--5.4.
The reviewed Table1 data are used directly; no new finite array is supplied. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows

noncomputable def capitalGamma (i : Fin 4) (lam : ℝ) : ℝ := gamma i lam-delta i lam
noncomputable def parentE (i : Fin 4) (lam : ℝ) : ℝ := 2+2*gamma i lam-alpha i lam-beta i lam

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.capitalGamma
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.capitalGamma
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentE
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentE
