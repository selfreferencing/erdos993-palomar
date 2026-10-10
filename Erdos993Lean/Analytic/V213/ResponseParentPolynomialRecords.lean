module

public import Mathlib

/-! Six literal parent polynomials. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows

noncomputable def parentQ (lam : ℝ) : ℝ :=
  -120*lam^5+141*lam^4+1416*lam^3+580*lam^2-1456*lam+500

noncomputable def parentDMinus (lam : ℝ) : ℝ :=
  560*lam^4-178*lam^3-1075*lam^2+1049*lam-14

noncomputable def parentDPlus (lam : ℝ) : ℝ :=
  920*lam^5+1354*lam^4-3163*lam^3-801*lam^2+4140*lam-56

noncomputable def parentE1 (lam : ℝ) : ℝ :=
  -2976*lam^5-670*lam^4+6291*lam^3+4321*lam^2+60*lam-1440

noncomputable def parentE2 (lam : ℝ) : ℝ :=
  -360*lam^5-478*lam^4+417*lam^3+1783*lam^2+1580*lam+40

noncomputable def parentH (lam : ℝ) : ℝ :=
  -50*lam^5-19*lam^4+231*lam^3+364*lam^2+136*lam-32

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentQ
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentQ
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentDMinus
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentDMinus
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentDPlus
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentDPlus
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentE1
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentE1
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentE2
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentE2
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentH
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentH
