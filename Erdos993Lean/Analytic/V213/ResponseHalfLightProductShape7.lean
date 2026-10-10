module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightCacheP7Bridge
public import Erdos993Lean.Analytic.V213.ResponseHalfLightProductShapeDefs

/-! Full matrix and row-length bounds transported through the exact cached polynomial equality. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates

theorem productShape_7 : ProductShape ⟨7,by decide⟩ := by
  unfold ProductShape
  simp only [← HalfLightPolys.StagedP7.trimmedNF_exact]
  decide +kernel

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.productShape_7
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.productShape_7
