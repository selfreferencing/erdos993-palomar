module

public import Erdos993Lean.Analytic.V213.ResponseParentRowRecords
public import Erdos993Lean.Analytic.V213.ResponseHalfLightGateRecords
public import Erdos993Lean.Analytic.V213.ZeroTiltLaplaceExactBi

/-! Exact algebraic operands for T8a(19)--(22).
The accepted syntax uses first=lambda and second=xi. Encoding swaps them
to a coefficient list with outer xi and inner lambda. No coefficient array or slack
is supplied. Polynomial operations below must reduce inside the Lean kernel.
The ten-term formula follows the separately affine determinant identity in
the companion algebra module. Its equality with the printed rational
determinant still requires the semantic proof; these definitions alone prove
no degree, coefficient sign, gate or determinant claim.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys

abbrev Bivariate := ZeroTiltLaplace.FinitePolynomial.Expr
def scalar (a : ℚ) : Bivariate := ZeroTiltLaplace.FinitePolynomial.Expr.constant a
def lamVar : Bivariate := ZeroTiltLaplace.FinitePolynomial.Expr.first
def xiVar : Bivariate := ZeroTiltLaplace.FinitePolynomial.Expr.second
def onePlus : Bivariate := 1+lamVar
def factorC : Bivariate := 2-xiVar
def factorD : Bivariate := 4+4*lamVar-lamVar*xiVar
def factorE : Bivariate := 2+2*lamVar-(lamVar-1)*xiVar
def factorF : Bivariate := 2+4*lamVar+2*lamVar^2-lamVar^2*xiVar
def factorG : Bivariate := 2+2*lamVar-lamVar*xiVar

def fieldPolynomial (i : Fin 4) (a b : ℤ) : Bivariate :=
  scalar (((a:ℚ)-(b:ℚ)*(rowData i).center)/65536)+scalar ((b:ℚ)/65536)*lamVar
def alphaPoly (i : Fin 4) : Bivariate := fieldPolynomial i (rowData i).alpha0 (rowData i).alpha1
def betaPoly (i : Fin 4) : Bivariate := fieldPolynomial i (rowData i).beta0 (rowData i).beta1
def gammaPoly (i : Fin 4) : Bivariate := fieldPolynomial i (rowData i).gamma0 (rowData i).gamma1
def deltaPoly (i : Fin 4) : Bivariate := fieldPolynomial i (rowData i).delta0 (rowData i).delta1
def gammaThetaPoly (i : Fin 4) : Bivariate := scalar (rowData i).gammaTheta
def phaseDen (phase : ℕ) : Bivariate := if phase=1 then 1 else factorC
def correctionDen (i : Fin 4) (phase : ℕ) : Bivariate :=
  if i=3 ∧ phase=1 then (1+2*lamVar)*factorG else 1
def correctionPoly (i : Fin 4) (phase : ℕ) : Bivariate :=
  if i=3 ∧ phase=1 then scalar (1/3)*(1-xiVar) else 0
def upperRatioNum : Bivariate :=
  10*factorF^2-5*lamVar*factorG*factorF-lamVar^2*factorG^2

/-- Numerator of A2 over 4 lambda(1+lambda)^2 T F, T=1 or C. -/
def a2Num (i : Fin 4) (phase : ℕ) : Bivariate :=
  if phase=1 then gammaThetaPoly i*(1+2*lamVar)*
    (onePlus*factorF+lamVar*(lamVar+2)*factorG)
  else gammaThetaPoly i*(1+2*lamVar)*
    (2*onePlus^2*factorC*factorG-xiVar*factorF)
def sourceBNum (i : Fin 4) (phase : ℕ) : Bivariate :=
  if phase=1 then -gammaThetaPoly i*(1+2*lamVar)*factorF
  else gammaThetaPoly i*(-2*onePlus*factorC+(1+2*lamVar)*xiVar)*factorF
def a1Num (i : Fin 4) (phase : ℕ) : Bivariate :=
  sourceBNum i phase-4*alphaPoly i*lamVar*onePlus^2*phaseDen phase*factorF-
    8*lamVar*onePlus^3*phaseDen phase+
    2*betaPoly i*lamVar^2*onePlus*phaseDen phase*factorF*xiVar+
    4*lamVar*onePlus^2*phaseDen phase*factorF*correctionPoly i phase
def baseANum (i : Fin 4) (phase : ℕ) : Bivariate :=
  alphaPoly i*correctionDen i phase-correctionPoly i phase*factorF
def baseB (i : Fin 4) : Bivariate := -alphaPoly i-betaPoly i
def baseKNum (i : Fin 4) : Bivariate :=
  2*(gammaPoly i-deltaPoly i)*factorF^2-lamVar^2*factorD*xiVar
def mixedKNum (i : Fin 4) (phase : ℕ) : Bivariate :=
  2*onePlus*correctionDen i phase*baseKNum i+
    lamVar^2*factorD*factorF*xiVar*(baseANum i phase+baseB i*correctionDen i phase)
def mixedANum (i : Fin 4) (phase : ℕ) : Bivariate :=
  2*onePlus*factorD*factorF*baseANum i phase+
    correctionDen i phase*xiVar*baseKNum i+
    lamVar*correctionDen i phase*factorD*factorF*xiVar*baseB i

/-- The ten separately affine determinant terms with the exact printed
denominator-clearing factor; the huge positive omega is applied last. -/
def unweightedDeterminantPoly (i : Fin 4) (phase : ℕ) : Bivariate :=
  let X := lamVar; let L := onePlus; let C := factorC; let D := factorD
  let E := factorE; let F := factorF; let G := factorG; let T := phaseDen phase
  let Z := correctionDen i phase; let A := a2Num i phase; let B := a1Num i phase
  let a := baseANum i phase; let b := baseB i; let K := baseKNum i
  let U := upperRatioNum; let gam := gammaPoly i; let del := deltaPoly i
  let V := B+16*X*L^3*T
  let W := B+8*X^2*L^2*T*xiVar
  X^2*L^3*C*T*E*F^2*K*A*a-
    scalar (1/16)*X*L*C*E*F*Z*K*B^2-
    scalar (1/8)*X^4*L^2*C*T*D*E*F^3*Z*xiVar*A*b^2+
    scalar (1/2)*X^4*L^3*C*T*D*E*F^2*Z*xiVar*B*b-
    8*X^5*L^6*C*T^2*D*E*F^2*xiVar*a+
    scalar (1/320)*X^3*C*D*E*Z*gam*U*xiVar*V^2-
    scalar (1/20)*X^2*L^2*C*T*E*gam*U*A*mixedKNum i phase+
    2*X*L^2*T*F^3*del*A*mixedANum i phase-
    scalar (1/4)*L*D*F^3*Z*del*W^2-
    scalar (1/10)*X*L*T*D*F^2*Z*A*gam*del*U*G^2

def omegaQ (r : Fin 8) : ℚ :=
  2^(HalfLightGates.productSpec r).omega2*
    3^(HalfLightGates.productSpec r).omega3*5^(HalfLightGates.productSpec r).omega5
def determinantExpression (r : Fin 8) : Bivariate :=
  scalar (omegaQ r)*unweightedDeterminantPoly
    (HalfLightGates.productSpec r).rowIndex (HalfLightGates.productSpec r).phase
def determinantPolynomial (r : Fin 8) : BCFG.Bi :=
  ZeroTiltLaplace.FinitePolynomial.Expr.encode (determinantExpression r) [[0,1]] [[],[1]]
noncomputable def evaluate (lam xi : ℝ) (p : BCFG.Bi) : ℝ :=
  BCFG.Bi.evalReal p xi lam

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.Bivariate
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.Bivariate
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.scalar
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.scalar
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.lamVar
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.lamVar
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.xiVar
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.xiVar
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.onePlus
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.onePlus
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.factorC
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.factorC
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.factorD
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.factorD
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.factorE
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.factorE
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.factorF
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.factorF
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.factorG
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.factorG
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.fieldPolynomial
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.fieldPolynomial
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.alphaPoly
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.alphaPoly
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.betaPoly
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.betaPoly
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.gammaPoly
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.gammaPoly
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.deltaPoly
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.deltaPoly
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.gammaThetaPoly
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.gammaThetaPoly
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.phaseDen
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.phaseDen
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.correctionDen
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.correctionDen
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.correctionPoly
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.correctionPoly
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.upperRatioNum
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.upperRatioNum
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.a2Num
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.a2Num
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.sourceBNum
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.sourceBNum
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.a1Num
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.a1Num
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.baseANum
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.baseANum
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.baseB
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.baseB
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.baseKNum
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.baseKNum
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.mixedKNum
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.mixedKNum
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.mixedANum
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.mixedANum
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.unweightedDeterminantPoly
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.unweightedDeterminantPoly
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.omegaQ
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.omegaQ
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.determinantExpression
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.determinantExpression
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.determinantPolynomial
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.determinantPolynomial
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.evaluate
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.evaluate
