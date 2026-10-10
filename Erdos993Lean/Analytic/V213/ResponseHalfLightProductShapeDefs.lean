module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightControlDefs

/-! Explicit full coefficient-list bounds for the printed two declared degrees.
This definition does not truncate or omit any coefficient. The eight actual
shape theorems are separate kernel computations from the printed expression. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates

def ProductShape (r : Fin 8) : Prop :=
  (trimmedDeterminant r).length <= (productSpec r).degreeXi+1 ∧
    ∀ p ∈ trimmedDeterminant r, p.length <= (productSpec r).degreeLambda+1

instance productShapeDecidable (r : Fin 8) : Decidable (ProductShape r) := by
  unfold ProductShape
  infer_instance

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.ProductShape
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.ProductShape
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.productShapeDecidable
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.productShapeDecidable
