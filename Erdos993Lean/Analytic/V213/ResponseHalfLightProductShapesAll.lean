module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightProductShape0
public import Erdos993Lean.Analytic.V213.ResponseHalfLightProductShape1
public import Erdos993Lean.Analytic.V213.ResponseHalfLightProductShape2
public import Erdos993Lean.Analytic.V213.ResponseHalfLightProductShape3
public import Erdos993Lean.Analytic.V213.ResponseHalfLightProductShape4
public import Erdos993Lean.Analytic.V213.ResponseHalfLightProductShape5
public import Erdos993Lean.Analytic.V213.ResponseHalfLightProductShape6
public import Erdos993Lean.Analytic.V213.ResponseHalfLightProductShape7

/-! Literal finite proof references only; no external polynomial computation. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates

theorem productShape_all (r : Fin 8) : ProductShape r := by
  fin_cases r
  · exact productShape_0
  · exact productShape_1
  · exact productShape_2
  · exact productShape_3
  · exact productShape_4
  · exact productShape_5
  · exact productShape_6
  · exact productShape_7

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.productShape_all
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.productShape_all
