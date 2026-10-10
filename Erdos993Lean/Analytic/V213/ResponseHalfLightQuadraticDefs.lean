module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightDefs
public import Erdos993Lean.Analytic.V213.ResponseParentRowAffineDefs

/-! Literal T8a Sections6.1--6.3 boundary expressions. Phase values are the
printed 1 and2; no assertion is made for other natural phase indices. The H.1
correction is included in the definitions, not added after finite checking. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight

noncomputable def phaseDomain (phase : ℕ) (lam H rho : ℝ) : Prop :=
  (phase=1 ∧ rhoMin lam (halfParent lam H) ≤ rho ∧ rho ≤ rhoStar lam (halfParent lam H)) ∨
  (phase=2 ∧ rhoStar lam (halfParent lam H) ≤ rho ∧ rho ≤ 1)
noncomputable def sourceChordError (lam H : ℝ) : ℝ :=
  (1+2*lam)*H/(4*lam*(lam-(1+lam)*H))
noncomputable def sourceChordA (phase : ℕ) (lam H : ℝ) : ℝ :=
  if phase=1 then
    (2*lam+1)/(4*lam*(1+lam))*((1+lam)+(lam+2)*halfParent lam H)
  else sourceSlopeB (childQ lam)*halfParent lam H-sourceChordError lam H
noncomputable def sourceChordB (phase : ℕ) (lam H : ℝ) : ℝ :=
  if phase=1 then -(2*lam+1)/(4*lam*(1+lam))
  else sourceIntercept (childQ lam)+sourceChordError lam H
noncomputable def upperRatio (p : ℝ) : ℝ := 1-p/2-p^2/10
noncomputable def lowerChildRatio (H : ℝ) : ℝ := 2*(1-H)/(2-H)
noncomputable def responseFactor (i : Fin 4) (lam H : ℝ) : ℝ :=
  2*delta i lam*(1+lam*(1-H))/(lam^2*(1-H)^2-H^2)
noncomputable def halfXi (lam H : ℝ) : ℝ := 2*H/childQ lam
noncomputable def phaseCorrection (i : Fin 4) (phase : ℕ) (lam H : ℝ) : ℝ :=
  if i=3 ∧ phase=1 then (1-halfXi lam H)/3 else 0
noncomputable def quadraticA2 (i : Fin 4) (phase : ℕ) (lam H : ℝ) : ℝ :=
  price i lam*sourceChordA phase lam H
noncomputable def quadraticA1 (i : Fin 4) (phase : ℕ) (lam H : ℝ) : ℝ :=
  price i lam*sourceChordB phase lam H-alpha i lam-(1-halfParent lam H)+beta i lam*H+
    phaseCorrection i phase lam H
noncomputable def quadraticA0 (i : Fin 4) (phase : ℕ) (lam H : ℝ) : ℝ :=
  alpha i lam-gamma i lam*upperRatio (halfParent lam H)+H*responseFactor i lam H-
    phaseCorrection i phase lam H*rhoStar lam (halfParent lam H)
noncomputable def quadraticB1 (lam H : ℝ) : ℝ := 2*(1-halfParent lam H)
noncomputable def quadraticB0 (i : Fin 4) (lam H : ℝ) : ℝ :=
  2*gamma i lam*upperRatio (halfParent lam H)-alpha i lam-beta i lam-2*responseFactor i lam H
noncomputable def quadraticK (i : Fin 4) (lam H : ℝ) : ℝ :=
  capitalGamma i lam/halfParent lam H*lowerChildRatio H-
    H*(1-halfParent lam H+gamma i lam*upperRatio (halfParent lam H))+responseFactor i lam H
noncomputable def jointQuadratic (i : Fin 4) (phase : ℕ) (lam H rho z : ℝ) : ℝ :=
  quadraticA2 i phase lam H*rho^2+quadraticA1 i phase lam H*rho+quadraticA0 i phase lam H+
    H*(quadraticB0 i lam H+quadraticB1 lam H*rho)*z+H*quadraticK i lam H*z^2
noncomputable def jointXi (i : Fin 4) (phase : ℕ) (lam H : ℝ) : ℝ :=
  4*quadraticA2 i phase lam H*quadraticK i lam H-H*(quadraticB1 lam H)^2
noncomputable def jointDeterminant (i : Fin 4) (phase : ℕ) (lam H : ℝ) : ℝ :=
  quadraticK i lam H*(4*quadraticA2 i phase lam H*quadraticA0 i phase lam H-
      (quadraticA1 i phase lam H)^2)-
    H*(quadraticA2 i phase lam H*(quadraticB0 i lam H)^2-
      quadraticA1 i phase lam H*quadraticB1 lam H*quadraticB0 i lam H+
      quadraticA0 i phase lam H*(quadraticB1 lam H)^2)

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.phaseDomain
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.phaseDomain
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.sourceChordError
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.sourceChordError
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.sourceChordA
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.sourceChordA
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.sourceChordB
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.sourceChordB
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.upperRatio
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.upperRatio
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.lowerChildRatio
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.lowerChildRatio
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.responseFactor
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.responseFactor
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.halfXi
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.halfXi
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.phaseCorrection
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.phaseCorrection
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.quadraticA2
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.quadraticA2
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.quadraticA1
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.quadraticA1
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.quadraticA0
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.quadraticA0
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.quadraticB1
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.quadraticB1
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.quadraticB0
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.quadraticB0
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.quadraticK
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.quadraticK
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.jointQuadratic
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.jointQuadratic
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.jointXi
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.jointXi
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.jointDeterminant
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.jointDeterminant
