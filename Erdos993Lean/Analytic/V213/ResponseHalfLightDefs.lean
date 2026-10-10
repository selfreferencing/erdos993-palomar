module

public import Erdos993Lean.Analytic.V213.ResponseParentRowRecords
public import Erdos993Lean.Analytic.V213.ResponseChartSource
public import Erdos993Lean.Analytic.V213.ResponseChartCoordinates
public import Erdos993Lean.Analytic.V213.ResponseChildTangents
public import Erdos993Lean.Analytic.V213.ResponseMinimum

/-! Literal current 5.24 parent coefficients and scalar minima. No sign or
positivity assertion is built into these definitions. Actual row fields are
the separately reviewed four Table1 records, not old BandData. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows

noncomputable def pStar (lam : ℝ) : ℝ := lam*(lam+2)/(lam^2+4*lam+2)
noncomputable def piStar (lam : ℝ) : ℝ := lam*(lam+2)/(3*lam^2+6*lam+2)
noncomputable def aStar (lam : ℝ) : ℝ :=
  if lam ≤ 1 then (1+lam)/lam else 2*(lam^2+4*lam+2)/(lam*(3*lam+4))
noncomputable def halfParent (lam H : ℝ) : ℝ := chartParent lam (1-H)
noncomputable def parentY (H : ℝ) : ℝ := -Real.log (1-H)
noncomputable def parentP (i : Fin 4) (lam H rho : ℝ) : ℝ :=
  rho*(1-halfParent lam H)+gamma i lam*messageRatio (halfParent lam H)
noncomputable def parentA (i : Fin 4) (lam H rho : ℝ) : ℝ :=
  halfParent lam H*(price i lam*rho*O2.src lam (halfParent lam H) rho+
    alpha i lam*(1-rho)-parentP i lam H rho)/parentY H
noncomputable def parentB (i : Fin 4) (lam H rho : ℝ) : ℝ :=
  beta i lam*rho*halfParent lam H
noncomputable def parentC (i : Fin 4) (lam H rho : ℝ) : ℝ :=
  halfParent lam H*(2*parentP i lam H rho-alpha i lam-beta i lam)
noncomputable def parentD (i : Fin 4) (lam H rho : ℝ) : ℝ :=
  gamma i lam-delta i lam-halfParent lam H*parentP i lam H rho*parentY H
noncomputable def parentMinimum (i : Fin 4) (lam H rho u : ℝ) : ℝ :=
  responseMinimum (parentA i lam H rho) (parentB i lam H rho) (parentC i lam H rho)
    (parentD i lam H rho) (delta i lam) (messageRatio u) (childJ lam u)
noncomputable def parentPayment (i : Fin 4) (lam H rho u y : ℝ) : ℝ :=
  responseQuadratic (parentA i lam H rho) (parentB i lam H rho) (parentC i lam H rho)
    (parentD i lam H rho) (delta i lam) (messageRatio u) (childJ lam u) y

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.pStar
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.pStar
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.piStar
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.piStar
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.aStar
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.aStar
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.halfParent
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.halfParent
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentY
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentY
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentP
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentP
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentA
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentA
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentB
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentB
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentC
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentC
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentD
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentD
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentMinimum
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentMinimum
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentPayment
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentPayment
