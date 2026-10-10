module

public import Erdos993Lean.F4U.Light.Construction.PaymentAlgebra

/-! The literal W numerator as a cubic in vacancy. Each coefficient is an
explicit expression in the retained row, parent, source chord and response.
The actual child/vacancy control is defined from these proved coefficients. -/

@[expose] public section

namespace F4Unified.LightConstruction
noncomputable section

 def W_cubicCoefficient (r : Row) (phase : SourcePhase) (lam H z h L : ℝ) (k : ℕ) : ℝ :=
  let p := pH lam H
  let e := 1-p
  let f := gamma r lam*parentHBound p
  let barGamma := (rowData r).price/(1+lam)
  let n2 := barGamma*chordSlope phase lam H
  let n1 := barGamma*chordIntercept phase lam H-alpha r lam-e
  let n0 := alpha r lam-f
  let c1 := 2*p*e
  let c0 := p*(2*f-alpha r lam-beta r lam)
  let d1 := -p*z*e
  let d0 := gamma r lam-delta r lam-p*z*f
  let G1 := L*d1
  let G0 := delta r lam+L*d0
  let B2 := p*n2
  let B1 := p*n1+z*p*beta r lam*h
  let B0 := p*n0
  match k with
  | 0 => 4*G0*B0+4*delta r lam*z*(c0*h+d0*h^2)-z*L*c0^2
  | 1 => 4*(G0*B1+G1*B0)+4*delta r lam*z*(c1*h+d1*h^2)-2*z*L*c0*c1
  | 2 => 4*(G0*B2+G1*B1)-z*L*c1^2
  | 3 => 4*G1*B2
  | _ => 0

 theorem W_cubic_representation (r : Row) (phase : SourcePhase)
    (lam H rho z h L : ℝ) :
    W r phase lam H rho z h L =
      W_cubicCoefficient r phase lam H z h L 0 +
      W_cubicCoefficient r phase lam H z h L 1*rho +
      W_cubicCoefficient r phase lam H z h L 2*rho^2 +
      W_cubicCoefficient r phase lam H z h L 3*rho^3 := by
  simp only [W_cubicCoefficient, W, responseC, responseD, parentNHat, parentPPlus, sourceChord]
  ring

 def childCubicCoefficient (r : Row) (reg : Regime) (phase : SourcePhase)
    (control : ChildControl) (lam H z : ℝ) (k : ℕ) : ℝ :=
  match control with
  | .V0 =>
    let s := match reg with | .A => Support.second | .B => Support.first
    W_cubicCoefficient r phase lam H z (hMinus r H) (supportLine r s lam (hMinus r H)) k
  | .V1 => W_cubicCoefficient r phase lam H z (hCross r lam)
      (supportLine r .first lam (hCross r lam)) k
  | .M0 =>
    2*W_cubicCoefficient r phase lam H z ((hMinus r H+hCross r lam)/2)
      ((supportLine r .first lam (hMinus r H)+supportLine r .first lam (hCross r lam))/2) k -
    (W_cubicCoefficient r phase lam H z (hMinus r H)
        (supportLine r .first lam (hMinus r H)) k +
      W_cubicCoefficient r phase lam H z (hCross r lam)
        (supportLine r .first lam (hCross r lam)) k)/2

 theorem child_control_cubic_representation (r : Row) (reg : Regime) (phase : SourcePhase)
    (control : ChildControl) (lam H rho z : ℝ) :
    childControlValue r reg phase control lam H rho z =
      childCubicCoefficient r reg phase control lam H z 0 +
      childCubicCoefficient r reg phase control lam H z 1*rho +
      childCubicCoefficient r reg phase control lam H z 2*rho^2 +
      childCubicCoefficient r reg phase control lam H z 3*rho^3 := by
  cases control <;> cases reg <;>
    simp only [childControlValue, childV0, childV1, childM0, childCubicCoefficient,
      W_cubic_representation] <;> ring

/-- The actual finite vacancy control, including its native degree and phase endpoints. -/
 def actualVacancyControl (r : Row) (reg : Regime) (phase : SourcePhase)
    (endpoint : LogEndpoint) (control : ChildControl) (s : ℕ) (lam H : ℝ) : ℝ :=
  vacancyControl (childCubicCoefficient r reg phase control lam H (logEndpoint endpoint H))
    (phaseLo phase lam H) (phaseHi phase lam H) (vacancyControlDegree reg phase) s

/-- The actual retained rational function in lambda and the manuscript's parent chart t. -/
 def actualFunctionValue (r : Row) (reg : Regime) (phase : SourcePhase)
    (endpoint : LogEndpoint) (control : ChildControl) (s : ℕ) (lam t : ℝ) : ℝ :=
  actualVacancyControl r reg phase endpoint control s lam (parentChart r reg lam t)

#print axioms W_cubicCoefficient
#print axioms W_cubic_representation
#print axioms childCubicCoefficient
#print axioms child_control_cubic_representation
#print axioms actualVacancyControl
#print axioms actualFunctionValue

end
end F4Unified.LightConstruction
