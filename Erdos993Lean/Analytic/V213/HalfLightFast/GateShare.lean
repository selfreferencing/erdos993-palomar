module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightCachedGateReduction

/-! Shared-stage gate checks for the half-light response (no existing declaration or statement
is changed by this file).

`Cached.gateValueFrom g P` recomputes, for every one of the 277 gates, the control polynomial,
its Bernstein normalisation and its shifted form.  The 277 gates belong to only 97 controls, and
all controls of one product use the same Bernstein basis.  Here the SAME definitions are split
into named stages, so that one kernel evaluation can check every gate of a product while each
control's normalised and shifted polynomial is passed along as ONE shared argument.

Nothing numerical is asserted in this file: every theorem is generic in `g` and `P`. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.HalfLightFast

open scoped BigOperators
open Erdos993Lean.BCFG
open Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows
open Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates

/-- The control polynomial of `Cached.gateValueFrom`, as a function of product, index and cache. -/
def controlOf (r : Fin 8) (j : ℕ) (P : Bi) : Uni :=
  Uni.trim (Uni.sumRange (fun b =>
    Uni.scale ((j.choose b : ℚ)/(((productSpec r).degreeXi).choose b : ℚ))
      (P.getD b [])) (j+1))

/-- The normalised control polynomial of `Cached.gateValueFrom`. -/
def normalizedOf (r : Fin 8) (j : ℕ) (P : Bi) : Uni :=
  Uni.trim (Uni.sumRange (fun a =>
    Uni.scale ((controlOf r j P).getD a 0)
      (Uni.mul (Uni.pow [0,1] a) (Uni.pow [1,-1] ((productSpec r).degreeLambda-a))))
    ((productSpec r).degreeLambda+1))

/-- The shifted polynomial of `Cached.gateValueFrom`, from the normalised one. -/
def shiftedOf (r : Fin 8) (normalized : Uni) : Uni :=
  Uni.trim (Uni.comp normalized [qCenter r,1])

/-- `lower` of `Cached.gateValueFrom`, from the shifted polynomial. -/
def lowerOf (r : Fin 8) (shifted : Uni) : ℚ :=
  shifted.getD 2 0-∑ i ∈ Finset.range ((productSpec r).degreeLambda+1),
    if 3 ≤ i then |shifted.getD i 0| *(qRadius r)^(i-2) else 0

/-- The seven gate quantities, from the three shared values. -/
def valueWith (r : Fin 8) (q : GateQuantity) (normalized shifted : Uni) (lower : ℚ) : ℚ :=
  match q with
  | .k => lower
  | .qMinus => shifted.getD 0 0+shifted.getD 1 0*(-qRadius r)+lower*(-qRadius r)^2
  | .qPlus => shifted.getD 0 0+shifted.getD 1 0*(qRadius r)+lower*(qRadius r)^2
  | .slope => shifted.getD 1 0+2*|lower| *qRadius r
  | .upperCurvature => 2*shifted.getD 2 0+
      ∑ i ∈ Finset.range ((productSpec r).degreeLambda+1),
        if 3 ≤ i then (i:ℚ)*(i-1:ℕ)*|shifted.getD i 0| *(qRadius r)^(i-2) else 0
  | .polyLow => ratEval normalized (qLow r)
  | .polyHigh => ratEval normalized (qHigh r)

/-- The staged form is the cached gate value, by unfolding only. -/
theorem gateValueFrom_eq (g : Fin 277) (P : Bi) :
    Cached.gateValueFrom g P =
      valueWith (controlSpec (gateSpec g).control).product (gateSpec g).quantity
        (normalizedOf (controlSpec (gateSpec g).control).product
          (controlSpec (gateSpec g).control).index P)
        (shiftedOf (controlSpec (gateSpec g).control).product
          (normalizedOf (controlSpec (gateSpec g).control).product
            (controlSpec (gateSpec g).control).index P))
        (lowerOf (controlSpec (gateSpec g).control).product
          (shiftedOf (controlSpec (gateSpec g).control).product
            (normalizedOf (controlSpec (gateSpec g).control).product
              (controlSpec (gateSpec g).control).index P))) := by
  rfl

def holdsWith (r : Fin 8) (q : GateQuantity) (normalized shifted : Uni) (lower : ℚ) : Prop :=
  match q with
  | .k | .slope | .upperCurvature => valueWith r q normalized shifted lower<0
  | .qMinus | .qPlus | .polyLow | .polyHigh =>
      (10:ℚ)^(productSpec r).floorPower<valueWith r q normalized shifted lower

instance holdsWithDecidable (r : Fin 8) (q : GateQuantity) (normalized shifted : Uni)
    (lower : ℚ) : Decidable (holdsWith r q normalized shifted lower) := by
  unfold holdsWith
  split <;> infer_instance

theorem gateHoldsFrom_iff (g : Fin 277) (P : Bi) :
    Cached.gateHoldsFrom g P ↔
      holdsWith (controlSpec (gateSpec g).control).product (gateSpec g).quantity
        (normalizedOf (controlSpec (gateSpec g).control).product
          (controlSpec (gateSpec g).control).index P)
        (shiftedOf (controlSpec (gateSpec g).control).product
          (normalizedOf (controlSpec (gateSpec g).control).product
            (controlSpec (gateSpec g).control).index P))
        (lowerOf (controlSpec (gateSpec g).control).product
          (shiftedOf (controlSpec (gateSpec g).control).product
            (normalizedOf (controlSpec (gateSpec g).control).product
              (controlSpec (gateSpec g).control).index P))) := by
  unfold Cached.gateHoldsFrom holdsWith
  rw [gateValueFrom_eq]
  generalize (gateSpec g).quantity = q
  cases q <;> exact Iff.rfl

/-- All listed quantities of one control, with `lower` computed once. -/
def checkLower (r : Fin 8) (qs : List GateQuantity) (normalized shifted : Uni) (lower : ℚ) :
    Bool :=
  qs.all (fun q => decide (holdsWith r q normalized shifted lower))

/-- ... with the shifted polynomial computed once. -/
def checkShifted (r : Fin 8) (qs : List GateQuantity) (normalized shifted : Uni) : Bool :=
  checkLower r qs normalized shifted (lowerOf r shifted)

/-- ... with the normalised polynomial computed once. -/
def checkNormalized (r : Fin 8) (qs : List GateQuantity) (normalized : Uni) : Bool :=
  checkShifted r qs normalized (shiftedOf r normalized)

def controlCheck (r : Fin 8) (j : ℕ) (P : Bi) (qs : List GateQuantity) : Bool :=
  checkNormalized r qs (normalizedOf r j P)

/-- The quantities that the printed gate table assigns to one control. -/
def quantitiesOf (c : Fin 97) : List GateQuantity :=
  ((List.finRange 277).filter (fun g => (gateSpec g).control = c)).map
    (fun g => (gateSpec g).quantity)

/-- One Boolean for every gate of product `r`. -/
def productCheck (r : Fin 8) (P : Bi) : Bool :=
  (List.finRange 97).all (fun c =>
    !decide ((controlSpec c).product = r) ||
      controlCheck r (controlSpec c).index P (quantitiesOf c))

/-- Generic soundness: the product Boolean gives every cached gate of that product. -/
theorem gateHoldsFrom_of_productCheck {r : Fin 8} {P : Bi} (h : productCheck r P = true)
    (g : Fin 277) (hr : (controlSpec (gateSpec g).control).product = r) :
    Cached.gateHoldsFrom g P := by
  subst hr
  have h1 := List.all_eq_true.mp h (gateSpec g).control (List.mem_finRange _)
  have h2 : controlCheck (controlSpec (gateSpec g).control).product
      (controlSpec (gateSpec g).control).index P (quantitiesOf (gateSpec g).control) = true := by
    simpa using h1
  have hmem : (gateSpec g).quantity ∈ quantitiesOf (gateSpec g).control := by
    unfold quantitiesOf
    exact List.mem_map.mpr ⟨g, List.mem_filter.mpr ⟨List.mem_finRange g, by simp⟩, rfl⟩
  have h3 : checkLower (controlSpec (gateSpec g).control).product
      (quantitiesOf (gateSpec g).control)
      (normalizedOf (controlSpec (gateSpec g).control).product
        (controlSpec (gateSpec g).control).index P)
      (shiftedOf (controlSpec (gateSpec g).control).product
        (normalizedOf (controlSpec (gateSpec g).control).product
          (controlSpec (gateSpec g).control).index P))
      (lowerOf (controlSpec (gateSpec g).control).product
        (shiftedOf (controlSpec (gateSpec g).control).product
          (normalizedOf (controlSpec (gateSpec g).control).product
            (controlSpec (gateSpec g).control).index P))) = true := h2
  have h4 := List.all_eq_true.mp h3 (gateSpec g).quantity hmem
  exact (gateHoldsFrom_iff g P).mpr (of_decide_eq_true h4)

/-- The original gate, from the product Boolean and the cache identity. -/
theorem gateHolds_of_productCheck {r : Fin 8} {P : Bi} (hP : P = trimmedDeterminant r)
    (h : productCheck r P = true) (g : Fin 277)
    (hr : (controlSpec (gateSpec g).control).product = r) : gateHolds g :=
  Cached.gateHolds_of_cached hr hP (gateHoldsFrom_of_productCheck h g hr)

end Erdos993Lean.Analytic.V213.HalfLightFast
