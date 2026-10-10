module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightCacheP3Bridge
public import Erdos993Lean.Analytic.V213.ResponseHalfLightProductShapeDefs

/-! Full matrix and row-length bounds transported through the exact cached polynomial equality. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates

theorem productShape_3 : ProductShape ⟨3,by decide⟩ := by
  unfold ProductShape
  simp only [← HalfLightPolys.StagedP3.trimmedNF_exact]
  decide +kernel

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.productShape_3
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.productShape_3
