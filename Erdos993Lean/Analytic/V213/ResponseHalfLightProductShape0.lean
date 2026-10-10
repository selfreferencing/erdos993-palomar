module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightCacheP0Bridge
public import Erdos993Lean.Analytic.V213.ResponseHalfLightProductShapeDefs

/-! Declared two-degree upper bounds for printed Table2 product row 0.
The exact expression is expanded only by the Lean kernel; no coefficient list is supplied. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates

theorem productShape_0 : ProductShape ⟨0,by decide⟩ := by
  unfold ProductShape
  simp only [← HalfLightPolys.StagedP0.trimmedNF_exact]
  decide +kernel

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.productShape_0
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.productShape_0
