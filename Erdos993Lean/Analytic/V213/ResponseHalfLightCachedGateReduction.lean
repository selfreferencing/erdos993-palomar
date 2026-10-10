module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightControlDefs

/-! Generic transport, not a finite gate claim. The explicit Bi parameter
replaces only the trimmed determinant. All transforms and inequalities are
the current definitions. The symbolic transport is proved before any closed
gate computation, so the latter need not unfold the full printed Expr.encode.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.Cached

open scoped BigOperators
open Erdos993Lean.BCFG

def gateValueFrom (g : Fin 277) (P : Bi) : ℚ :=
  let s := gateSpec g
  let c := s.control
  let r := (controlSpec c).product
  let n := (productSpec r).degreeXi
  let N := (productSpec r).degreeLambda
  let control := Uni.trim (Uni.sumRange (fun b =>
    Uni.scale (((controlSpec c).index.choose b : ℚ)/(n.choose b : ℚ))
      (P.getD b [])) ((controlSpec c).index+1))
  let normalized := Uni.trim (Uni.sumRange (fun a =>
    Uni.scale (control.getD a 0)
      (Uni.mul (Uni.pow [0,1] a) (Uni.pow [1,-1] (N-a)))) (N+1))
  let shifted := Uni.trim (Uni.comp normalized [qCenter r,1])
  let coefficient := fun i => shifted.getD i 0
  let tail := ∑ i ∈ Finset.range (N+1),
    if 3 ≤ i then |coefficient i| *(qRadius r)^(i-2) else 0
  let lower := coefficient 2-tail
  let quadratic := fun t => coefficient 0+coefficient 1*t+lower*t^2
  match s.quantity with
  | .k => lower
  | .qMinus => quadratic (-qRadius r)
  | .qPlus => quadratic (qRadius r)
  | .slope => coefficient 1+2*|lower| *qRadius r
  | .upperCurvature => 2*coefficient 2+
      ∑ i ∈ Finset.range (N+1),
        if 3 ≤ i then (i:ℚ)*(i-1:ℕ)*|coefficient i| *(qRadius r)^(i-2) else 0
  | .polyLow => ratEval normalized (qLow r)
  | .polyHigh => ratEval normalized (qHigh r)

def gateHoldsFrom (g : Fin 277) (P : Bi) : Prop :=
  match (gateSpec g).quantity with
  | .k | .slope | .upperCurvature => gateValueFrom g P<0
  | .qMinus | .qPlus | .polyLow | .polyHigh =>
      (10:ℚ)^(productSpec (controlSpec (gateSpec g).control).product).floorPower<gateValueFrom g P

instance gateHoldsFromDecidable (g : Fin 277) (P : Bi) : Decidable (gateHoldsFrom g P) := by
  unfold gateHoldsFrom
  split <;> infer_instance

/-- Symbolic definitional correspondence. The gate and coefficient list are
not concrete here, so this does not replay a printed determinant computation. -/
theorem gateValueFrom_original (g : Fin 277) :
    gateValueFrom g (trimmedDeterminant (controlSpec (gateSpec g).control).product) =
      gateValue g := by
  rfl

theorem gateHoldsFrom_original (g : Fin 277) :
    gateHoldsFrom g (trimmedDeterminant (controlSpec (gateSpec g).control).product) ↔
      gateHolds g := by
  simp only [gateHoldsFrom, gateHolds, gateValueFrom_original]
  exact Iff.rfl

/-- Both equalities are mandatory. The finite product-index correspondence
is checked inside Lean; Python record selection has no mathematical authority. -/
theorem gateHolds_of_cached {g : Fin 277} {r : Fin 8} {P : Bi}
    (hproduct : (controlSpec (gateSpec g).control).product = r)
    (hcache : P = trimmedDeterminant r)
    (hcomputed : gateHoldsFrom g P) : gateHolds g := by
  have hP : P = trimmedDeterminant (controlSpec (gateSpec g).control).product :=
    hcache.trans (congrArg trimmedDeterminant hproduct.symm)
  rw [hP] at hcomputed
  exact (gateHoldsFrom_original g).mp hcomputed

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.Cached

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.Cached.gateValueFrom
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.Cached.gateValueFrom
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.Cached.gateHoldsFrom
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.Cached.gateHoldsFrom
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.Cached.gateHoldsFromDecidable
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.Cached.gateHoldsFromDecidable
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.Cached.gateValueFrom_original
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.Cached.gateValueFrom_original
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.Cached.gateHoldsFrom_original
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.Cached.gateHoldsFrom_original
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.Cached.gateHolds_of_cached
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.Cached.gateHolds_of_cached
