module

public import Erdos993Lean.BCFG.DeterminantAlgebra

/-! Literal heavy/light analytic definitions, current T6b Eq.(8)--(14).
The definitions of envelopes do not assert that they bound logarithms or payments. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Erdos993Lean.BCFG.Analytic

def sourceA (lam : ℝ) : ℝ := (1+2*lam)/(2*lam)
def lightSourceA (lam omega : ℝ) : ℝ :=
  (2*lam+1)*(2*lam^2*omega+lam*omega^2+lam*omega+omega^2-1)/
    (4*lam^2*(1+lam*omega))
def lightSourceB (lam omega : ℝ) : ℝ := -((1+lam)*omega-1)/(2*lam^2)
def eCoeff (r : AnalyticRow) (lam omega : ℝ) : ℝ :=
  gamma r lam*cubicEnvelope (occupation lam omega)
def dCoeff (lam omega : ℝ) : ℝ := 1-occupation lam omega
def rCoeff (r : AnalyticRow) (lam omega : ℝ) : ℝ := gamma r lam/occupation lam omega

def heavyOmega (r : AnalyticRow) (lam v : ℝ) : ℝ := v^(heavyExponent r)/(1+lam)
def heavyZ (v : ℝ) : ℝ := (1-v)/(1+v)
def heavyLower (r : AnalyticRow) (lam v : ℝ) : ℝ :=
  ellLower r lam+2*(heavyExponent r : ℝ)*heavyZ v
def heavyUpper (r : AnalyticRow) (lam v : ℝ) : ℝ :=
  ellUpper r lam+(heavyExponent r : ℝ)*
    (2*heavyZ v+2*(heavyZ v)^3/(3*(1-(heavyZ v)^2)))
def heavyK (r : AnalyticRow) (lam v rho : ℝ) : ℝ :=
  price r lam*sourceA lam*occupation lam (heavyOmega r lam v)*rho^2+
    alpha r*(1-rho)+beta r*rho*massLine r lam*heavyLower r lam v
def heavyK1 (r : AnalyticRow) (lam v : ℝ) : ℝ :=
  -alpha r+beta r*massLine r lam*heavyLower r lam v
def heavyK2 (r : AnalyticRow) (lam v : ℝ) : ℝ :=
  price r lam*sourceA lam*occupation lam (heavyOmega r lam v)
def heavyRawCoefficient (r : AnalyticRow) (lam v : ℝ) : ℕ → ℝ :=
  rawCoefficient (alpha r) epsilon (centerResponse r)
    (eCoeff r lam (heavyOmega r lam v)) (dCoeff lam (heavyOmega r lam v))
    (rCoeff r lam (heavyOmega r lam v)) (heavyUpper r lam v)
    (heavyK1 r lam v) (heavyK2 r lam v)
def heavyCoefficient (r : AnalyticRow) (lam v : ℝ) : ℕ → ℝ :=
  vacancyCoefficient (heavyRawCoefficient r lam v) (rhoZero lam (heavyOmega r lam v))
def heavyBernstein (r : AnalyticRow) (lam v : ℝ) (j : ℕ) : ℝ :=
  bernsteinCoefficient (heavyCoefficient r lam v) j
def heavyDeterminant (r : AnalyticRow) (lam v rho : ℝ) : ℝ :=
  scaledDet (alpha r) epsilon (centerResponse r)
    (eCoeff r lam (heavyOmega r lam v)) (dCoeff lam (heavyOmega r lam v))
    (rCoeff r lam (heavyOmega r lam v)) (heavyUpper r lam v)
    (heavyK1 r lam v) (heavyK2 r lam v) rho

def lightOmega (lam x : ℝ) : ℝ := 1-q lam*x
def lightZ (lam x : ℝ) : ℝ := (1-lightOmega lam x)/(1+lightOmega lam x)
def lightUpper (lam x : ℝ) : ℝ :=
  2*(lightZ lam x+(lightZ lam x)^3/3)+
    2*(lightZ lam x)^5/(5*(1-(lightZ lam x)^2))
def lightK (r : AnalyticRow) (lam x rho : ℝ) : ℝ :=
  price r lam*rho*(lightSourceA lam (lightOmega lam x)*rho+
    lightSourceB lam (lightOmega lam x))+
    alpha r*(1-rho)+beta r*rho*(1-lightOmega lam x)
def lightK1 (r : AnalyticRow) (lam x : ℝ) : ℝ :=
  price r lam*lightSourceB lam (lightOmega lam x)-alpha r+
    beta r*(1-lightOmega lam x)
def lightK2 (r : AnalyticRow) (lam x : ℝ) : ℝ :=
  price r lam*lightSourceA lam (lightOmega lam x)
def lightCenter : AnalyticRow → ℝ → ℝ
  | .B, _ => 3/10 | .C, _ => 3/10
  | .F, x => (72-45*x)/100 | .G, x => (77-41*x)/100
def lightRawCoefficient (r : AnalyticRow) (lam x : ℝ) : ℕ → ℝ :=
  rawCoefficient (alpha r) epsilon (centerResponse r)
    (eCoeff r lam (lightOmega lam x)) (dCoeff lam (lightOmega lam x))
    (rCoeff r lam (lightOmega lam x)) (lightUpper lam x)
    (lightK1 r lam x) (lightK2 r lam x)
def lightCoefficient (r : AnalyticRow) (lam x : ℝ) : ℕ → ℝ :=
  vacancyCoefficient (lightRawCoefficient r lam x) (rhoZero lam (lightOmega lam x))
def lightDeterminant (r : AnalyticRow) (lam x rho : ℝ) : ℝ :=
  scaledDet (alpha r) epsilon (centerResponse r)
    (eCoeff r lam (lightOmega lam x)) (dCoeff lam (lightOmega lam x))
    (rCoeff r lam (lightOmega lam x)) (lightUpper lam x)
    (lightK1 r lam x) (lightK2 r lam x) rho

/-- All 28 actual analytic functions: four row values for each existing function ID. -/
def analyticFunction (r : AnalyticRow) (f : DeterminantFunction) (lam y : ℝ) : ℝ :=
  match f with
  | .H0 => heavyBernstein r lam y 0
  | .H3 => heavyBernstein r lam y 3
  | .H1 => heavyBernstein r lam y 1+2/3*heavyBernstein r lam y 0
  | .H2 => heavyBernstein r lam y 2-1/3*heavyBernstein r lam y 0
  | .J => lightJ (lightCoefficient r lam y) (lightCenter r y)
  | .C0 => lightC0 (lightCoefficient r lam y) (lightCenter r y)
  | .C1 => lightC1 (lightCoefficient r lam y) (lightCenter r y)

def FunctionDomain (r : AnalyticRow) (f : DeterminantFunction) (lam y : ℝ) : Prop :=
  match f with
  | .H0 | .H3 | .H1 | .H2 => HeavyDomain r lam y
  | .J | .C0 | .C1 => LightDomain r lam y

end Erdos993Lean.BCFG.Analytic

#check Erdos993Lean.BCFG.Analytic.sourceA
#print axioms Erdos993Lean.BCFG.Analytic.sourceA
#check Erdos993Lean.BCFG.Analytic.lightSourceA
#print axioms Erdos993Lean.BCFG.Analytic.lightSourceA
#check Erdos993Lean.BCFG.Analytic.lightSourceB
#print axioms Erdos993Lean.BCFG.Analytic.lightSourceB
#check Erdos993Lean.BCFG.Analytic.eCoeff
#print axioms Erdos993Lean.BCFG.Analytic.eCoeff
#check Erdos993Lean.BCFG.Analytic.dCoeff
#print axioms Erdos993Lean.BCFG.Analytic.dCoeff
#check Erdos993Lean.BCFG.Analytic.rCoeff
#print axioms Erdos993Lean.BCFG.Analytic.rCoeff
#check Erdos993Lean.BCFG.Analytic.heavyOmega
#print axioms Erdos993Lean.BCFG.Analytic.heavyOmega
#check Erdos993Lean.BCFG.Analytic.heavyZ
#print axioms Erdos993Lean.BCFG.Analytic.heavyZ
#check Erdos993Lean.BCFG.Analytic.heavyLower
#print axioms Erdos993Lean.BCFG.Analytic.heavyLower
#check Erdos993Lean.BCFG.Analytic.heavyUpper
#print axioms Erdos993Lean.BCFG.Analytic.heavyUpper
#check Erdos993Lean.BCFG.Analytic.heavyK
#print axioms Erdos993Lean.BCFG.Analytic.heavyK
#check Erdos993Lean.BCFG.Analytic.heavyK1
#print axioms Erdos993Lean.BCFG.Analytic.heavyK1
#check Erdos993Lean.BCFG.Analytic.heavyK2
#print axioms Erdos993Lean.BCFG.Analytic.heavyK2
#check Erdos993Lean.BCFG.Analytic.heavyRawCoefficient
#print axioms Erdos993Lean.BCFG.Analytic.heavyRawCoefficient
#check Erdos993Lean.BCFG.Analytic.heavyCoefficient
#print axioms Erdos993Lean.BCFG.Analytic.heavyCoefficient
#check Erdos993Lean.BCFG.Analytic.heavyBernstein
#print axioms Erdos993Lean.BCFG.Analytic.heavyBernstein
#check Erdos993Lean.BCFG.Analytic.heavyDeterminant
#print axioms Erdos993Lean.BCFG.Analytic.heavyDeterminant
#check Erdos993Lean.BCFG.Analytic.lightOmega
#print axioms Erdos993Lean.BCFG.Analytic.lightOmega
#check Erdos993Lean.BCFG.Analytic.lightZ
#print axioms Erdos993Lean.BCFG.Analytic.lightZ
#check Erdos993Lean.BCFG.Analytic.lightUpper
#print axioms Erdos993Lean.BCFG.Analytic.lightUpper
#check Erdos993Lean.BCFG.Analytic.lightK
#print axioms Erdos993Lean.BCFG.Analytic.lightK
#check Erdos993Lean.BCFG.Analytic.lightK1
#print axioms Erdos993Lean.BCFG.Analytic.lightK1
#check Erdos993Lean.BCFG.Analytic.lightK2
#print axioms Erdos993Lean.BCFG.Analytic.lightK2
#check Erdos993Lean.BCFG.Analytic.lightCenter
#print axioms Erdos993Lean.BCFG.Analytic.lightCenter
#check Erdos993Lean.BCFG.Analytic.lightRawCoefficient
#print axioms Erdos993Lean.BCFG.Analytic.lightRawCoefficient
#check Erdos993Lean.BCFG.Analytic.lightCoefficient
#print axioms Erdos993Lean.BCFG.Analytic.lightCoefficient
#check Erdos993Lean.BCFG.Analytic.lightDeterminant
#print axioms Erdos993Lean.BCFG.Analytic.lightDeterminant
#check Erdos993Lean.BCFG.Analytic.analyticFunction
#print axioms Erdos993Lean.BCFG.Analytic.analyticFunction
#check Erdos993Lean.BCFG.Analytic.FunctionDomain
#print axioms Erdos993Lean.BCFG.Analytic.FunctionDomain
