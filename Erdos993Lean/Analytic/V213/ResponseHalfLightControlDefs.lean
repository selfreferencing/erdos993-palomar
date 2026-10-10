module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightPolynomialDefs

/-! Exact operands of T8a(20)--(22) and Lemma6.4.
All lists are computed from the printed expression by the accepted list
operations, inside Lean. No coefficient, degree inventory or gate result is
supplied here. The finite tests and their semantic consumers are separate.
Trimming removes zero leading coefficients only. Sums retain the declared N;
missing coefficients are zero, so smaller actual degrees cause no change.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates

open scoped BigOperators
open BCFG

def trimmedDeterminant (r : Fin 8) : Bi :=
  Bi.trim (HalfLightPolys.determinantPolynomial r)

def controlPolynomial (c : Fin 97) : Uni :=
  let s := controlSpec c
  let n := (productSpec s.product).degreeXi
  Uni.trim (Uni.sumRange (fun b =>
    Uni.scale ((s.index.choose b : ℚ)/(n.choose b : ℚ))
      ((trimmedDeterminant s.product).getD b [])) (s.index+1))

def normalizedControl (c : Fin 97) : Uni :=
  let N := (productSpec (controlSpec c).product).degreeLambda
  Uni.trim (Uni.sumRange (fun a =>
    Uni.scale ((controlPolynomial c).getD a 0)
      (Uni.mul (Uni.pow [0,1] a) (Uni.pow [1,-1] (N-a)))) (N+1))

def qLow (r : Fin 8) : ℚ :=
  let l := (rowData (productSpec r).rowIndex).low
  l/(1+l)
def qHigh (r : Fin 8) : ℚ :=
  let h := (rowData (productSpec r).rowIndex).high
  h/(1+h)
def qCenter (r : Fin 8) : ℚ := (qLow r+qHigh r)/2
def qRadius (r : Fin 8) : ℚ := (qHigh r-qLow r)/2

def shiftedControl (c : Fin 97) : Uni :=
  Uni.trim (Uni.comp (normalizedControl c) [qCenter (controlSpec c).product,1])
def shiftedCoefficient (c : Fin 97) (i : ℕ) : ℚ := (shiftedControl c).getD i 0

def tailNorm (c : Fin 97) : ℚ :=
  let r := (controlSpec c).product
  ∑ i ∈ Finset.range ((productSpec r).degreeLambda+1),
    if 3 ≤ i then |shiftedCoefficient c i| *(qRadius r)^(i-2) else 0
def lowerCurvature (c : Fin 97) : ℚ := shiftedCoefficient c 2-tailNorm c
def lowerQuadratic (c : Fin 97) (t : ℚ) : ℚ :=
  shiftedCoefficient c 0+shiftedCoefficient c 1*t+lowerCurvature c*t^2
def slopeBound (c : Fin 97) : ℚ :=
  shiftedCoefficient c 1+2*|lowerCurvature c| *qRadius (controlSpec c).product
def upperCurvature (c : Fin 97) : ℚ :=
  let r := (controlSpec c).product
  2*shiftedCoefficient c 2+
    ∑ i ∈ Finset.range ((productSpec r).degreeLambda+1),
      if 3 ≤ i then (i:ℚ)*(i-1:ℕ)*|shiftedCoefficient c i| *(qRadius r)^(i-2) else 0

def ratEval : Uni → ℚ → ℚ
  | [], _ => 0
  | a::p, x => a+x*ratEval p x

def gateValue (g : Fin 277) : ℚ :=
  let s := gateSpec g
  let c := s.control
  let r := (controlSpec c).product
  match s.quantity with
  | .k => lowerCurvature c
  | .qMinus => lowerQuadratic c (-qRadius r)
  | .qPlus => lowerQuadratic c (qRadius r)
  | .slope => slopeBound c
  | .upperCurvature => upperCurvature c
  | .polyLow => ratEval (normalizedControl c) (qLow r)
  | .polyHigh => ratEval (normalizedControl c) (qHigh r)

def gateHolds (g : Fin 277) : Prop :=
  match (gateSpec g).quantity with
  | .k | .slope | .upperCurvature => gateValue g<0
  | .qMinus | .qPlus | .polyLow | .polyHigh =>
    (10:ℚ)^(productSpec (controlSpec (gateSpec g).control).product).floorPower<gateValue g

instance gateHoldsDecidable (g : Fin 277) : Decidable (gateHolds g) := by
  unfold gateHolds
  split <;> infer_instance

def gateCheck (g : Fin 277) : Bool := decide (gateHolds g)

theorem ratEval_cast (p : Uni) (x : ℚ) :
    (ratEval p x : ℝ)=Uni.evalReal p (x:ℝ) := by
  induction p with
  | nil => simp [ratEval]
  | cons a p ih => simp only [ratEval,Uni.evalReal_cons,Rat.cast_add,Rat.cast_mul,ih]

theorem gateCheck_sound (g : Fin 277) (h : gateCheck g=true) : gateHolds g :=
  of_decide_eq_true h

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.trimmedDeterminant
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.trimmedDeterminant
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.controlPolynomial
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.controlPolynomial
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.normalizedControl
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.normalizedControl
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.qLow
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.qLow
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.qHigh
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.qHigh
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.qCenter
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.qCenter
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.qRadius
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.qRadius
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.shiftedControl
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.shiftedControl
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.shiftedCoefficient
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.shiftedCoefficient
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.tailNorm
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.tailNorm
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.lowerCurvature
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.lowerCurvature
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.lowerQuadratic
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.lowerQuadratic
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.slopeBound
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.slopeBound
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.upperCurvature
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.upperCurvature
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.ratEval
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.ratEval
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.gateValue
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.gateValue
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.gateHolds
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.gateHolds
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.gateHoldsDecidable
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.gateHoldsDecidable
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.gateCheck
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.gateCheck
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.ratEval_cast
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.ratEval_cast
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.gateCheck_sound
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.gateCheck_sound
