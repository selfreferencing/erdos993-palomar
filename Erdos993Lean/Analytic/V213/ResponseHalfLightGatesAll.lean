module

public import Erdos993Lean.Analytic.V213.HalfLightFast.GateCheckP0
public import Erdos993Lean.Analytic.V213.HalfLightFast.GateCheckP1
public import Erdos993Lean.Analytic.V213.HalfLightFast.GateCheckP2
public import Erdos993Lean.Analytic.V213.HalfLightFast.GateCheckP3
public import Erdos993Lean.Analytic.V213.HalfLightFast.GateCheckP4
public import Erdos993Lean.Analytic.V213.HalfLightFast.GateCheckP5
public import Erdos993Lean.Analytic.V213.HalfLightFast.GateCheckP6
public import Erdos993Lean.Analytic.V213.HalfLightFast.GateCheckP7

/-! Literal finite proof references only; no external polynomial computation. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates

theorem gateHolds_all (g : Fin 277) : gateHolds g := by
  generalize hr : (controlSpec (gateSpec g).control).product = r
  match r, hr with
  | ⟨0, _⟩, hr =>
    exact Erdos993Lean.Analytic.V213.HalfLightFast.gateHolds_of_productCheck
      HalfLightPolys.StagedP0.trimmedNF_exact Erdos993Lean.Analytic.V213.HalfLightFast.productCheck_0 g hr
  | ⟨1, _⟩, hr =>
    exact Erdos993Lean.Analytic.V213.HalfLightFast.gateHolds_of_productCheck
      HalfLightPolys.StagedP1.trimmedNF_exact Erdos993Lean.Analytic.V213.HalfLightFast.productCheck_1 g hr
  | ⟨2, _⟩, hr =>
    exact Erdos993Lean.Analytic.V213.HalfLightFast.gateHolds_of_productCheck
      HalfLightPolys.StagedP2.trimmedNF_exact Erdos993Lean.Analytic.V213.HalfLightFast.productCheck_2 g hr
  | ⟨3, _⟩, hr =>
    exact Erdos993Lean.Analytic.V213.HalfLightFast.gateHolds_of_productCheck
      HalfLightPolys.StagedP3.trimmedNF_exact Erdos993Lean.Analytic.V213.HalfLightFast.productCheck_3 g hr
  | ⟨4, _⟩, hr =>
    exact Erdos993Lean.Analytic.V213.HalfLightFast.gateHolds_of_productCheck
      HalfLightPolys.StagedP4.trimmedNF_exact Erdos993Lean.Analytic.V213.HalfLightFast.productCheck_4 g hr
  | ⟨5, _⟩, hr =>
    exact Erdos993Lean.Analytic.V213.HalfLightFast.gateHolds_of_productCheck
      HalfLightPolys.StagedP5.trimmedNF_exact Erdos993Lean.Analytic.V213.HalfLightFast.productCheck_5 g hr
  | ⟨6, _⟩, hr =>
    exact Erdos993Lean.Analytic.V213.HalfLightFast.gateHolds_of_productCheck
      HalfLightPolys.StagedP6.trimmedNF_exact Erdos993Lean.Analytic.V213.HalfLightFast.productCheck_6 g hr
  | ⟨7, _⟩, hr =>
    exact Erdos993Lean.Analytic.V213.HalfLightFast.gateHolds_of_productCheck
      HalfLightPolys.StagedP7.trimmedNF_exact Erdos993Lean.Analytic.V213.HalfLightFast.productCheck_7 g hr
  | ⟨n+8, h⟩, _ => exact absurd h (by omega)

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.gateHolds_all
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.gateHolds_all
