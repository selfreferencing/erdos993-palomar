module

public import Erdos993Lean.Analytic.V213.ZeroTiltLaplaceCenterCalculus

/-! The three literal rational comparisons of the joining step.
Both explicitly printed values are also checked.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial

theorem joining_upper :
    centerC1 (11/20)=(493801/190655425:ℝ) ∧
      (3/1250:ℝ)<centerC1 (11/20) := by
  norm_num [centerC1]

theorem joining_middle : centerC2 (3/7)<centerC2 (11/20) := by
  norm_num [centerC2]

theorem joining_lower :
    centerC1 (3/7)+centerC2 (3/7)=(76320036/30192903125:ℝ) ∧
      (3/1250:ℝ)<centerC1 (3/7)+centerC2 (3/7) := by
  norm_num [centerC1,centerC2]

theorem current_center_joins : CenterJoinFacts :=
  ⟨joining_upper.2,joining_middle,joining_lower.2⟩

end Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial

#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.joining_upper
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.joining_upper
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.joining_middle
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.joining_middle
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.joining_lower
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.joining_lower
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.current_center_joins
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.current_center_joins
