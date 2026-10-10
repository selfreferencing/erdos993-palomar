module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightLeaf
public import Erdos993Lean.Analytic.V213.ResponseHalfLightMinimum

/-! Current Theorem5.26, conditional on no unproved analytic or finite fact:
068 supplies the literal determinant proof,065 the boundary reduction and064
the actual attained-minimum comparison. Parent leaves use their own p*N. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows

open HalfLight Set

/-- Every feasible vacancy lies in one of the two closed source phases. -/
theorem half_light_phase_exists {lam H rho : ℝ} (hl : 0 < lam)
    (hH : 0 ≤ H) (hcap : H ≤ childQ lam/2)
    (hrho : rhoMin lam (halfParent lam H) ≤ rho) (hrho1 : rho ≤ 1) :
    ∃ phase : ℕ, (phase=1 ∨ phase=2) ∧ phaseDomain phase lam H rho := by
  by_cases hs : rho ≤ rhoStar lam (halfParent lam H)
  · exact ⟨1,Or.inl rfl,Or.inl ⟨rfl,hrho,hs⟩⟩
  · exact ⟨2,Or.inr rfl,Or.inr ⟨rfl,(lt_of_not_ge hs).le,hrho1⟩⟩

/-- Literal strict boundary statement, for every signed real response. -/
theorem half_light_boundary_positive {i : Fin 4} {lam H rho y : ℝ}
    (hrow : inRow i lam) (hH : 0 < H) (hcap : H ≤ childQ lam/2)
    (hrho : rhoMin lam (halfParent lam H) ≤ rho) (hrho1 : rho ≤ 1) :
    0 < parentPayment i lam H rho H y := by
  obtain ⟨phase,hphase,hdom⟩ := half_light_phase_exists (row_activity_bounds hrow).1
    hH.le hcap hrho hrho1
  apply boundary_positive_of_determinant hrow hH hcap hdom
  intro x hx
  exact HalfLightGates.printed_jointDeterminant_positive hrow hphase hx.1 hx.2

/-- Strict positivity of the actual attained minimum, not an infimum-only claim. -/
theorem half_light_boundary_minimum_positive {i : Fin 4} {lam H rho : ℝ}
    (hrow : inRow i lam) (hH : 0 < H) (hcap : H ≤ childQ lam/2)
    (hrho : rhoMin lam (halfParent lam H) ≤ rho) (hrho1 : rho ≤ 1) :
    0 < parentMinimum i lam H rho H := by
  obtain ⟨y,hy⟩ := (parentMinimum_is_minimum hrow hH hcap hrho1 hH (le_refl H)).2
  rw [←hy]
  exact half_light_boundary_positive hrow hH hcap hrho hrho1

/-- The full printed inequality chain includes u=0 with its assigned y=1. -/
theorem half_light_payment_chain {i : Fin 4} {lam H rho u y : ℝ}
    (hrow : inRow i lam) (hH : 0 < H) (hcap : H ≤ childQ lam/2)
    (hrho : rhoMin lam (halfParent lam H) ≤ rho) (hrho1 : rho ≤ 1)
    (hu : 0 ≤ u) (huH : u ≤ H) (hleaf : u=0 → y=1) :
    0 < parentMinimum i lam H rho H ∧
    parentMinimum i lam H rho H ≤ parentMinimum i lam H rho u ∧
    parentMinimum i lam H rho u ≤ parentPayment i lam H rho u y := by
  have h := half_light_parent_mixed hrow hH hcap hrho hrho1 hu huH hleaf
  exact ⟨half_light_boundary_minimum_positive hrow hH hcap hrho hrho1,h.2.2.1,h.2.2.2⟩

theorem half_light_payment_positive {i : Fin 4} {lam H rho u y : ℝ}
    (hrow : inRow i lam) (hH : 0 < H) (hcap : H ≤ childQ lam/2)
    (hrho : rhoMin lam (halfParent lam H) ≤ rho) (hrho1 : rho ≤ 1)
    (hu : 0 ≤ u) (huH : u ≤ H) (hleaf : u=0 → y=1) :
    0 < parentPayment i lam H rho u y := by
  have h := half_light_payment_chain hrow hH hcap hrho hrho1 hu huH hleaf
  exact h.1.trans_le (h.2.1.trans h.2.2)

/-- Explicit combined notation: the parent leaf has no child quadratic. -/
noncomputable def closedParentPayment (i : Fin 4) (lam H rho u y : ℝ) : ℝ :=
  if H=0 then parentLeafPayment i lam rho else parentPayment i lam H rho u y

/-- Closed H-domain formulation of the printed theorem, with the literal
leaf value and no determinant, curvature, variance or positivity premise. -/
theorem half_light_closed_payment_positive {i : Fin 4} {lam H rho u y : ℝ}
    (hrow : inRow i lam) (hH : 0 ≤ H) (hcap : H ≤ childQ lam/2)
    (hrho : rhoMin lam (halfParent lam H) ≤ rho) (hrho1 : rho ≤ 1)
    (hu : 0 ≤ u) (huH : u ≤ H) (hleaf : u=0 → y=1) :
    0 < closedParentPayment i lam H rho u y := by
  by_cases hzero : H=0
  · subst H
    rw [closedParentPayment,if_pos rfl]
    exact parentLeafPayment_pos hrow (by simpa only [halfParent_zero] using hrho) hrho1
  · rw [closedParentPayment,if_neg hzero]
    exact half_light_payment_positive hrow (lt_of_le_of_ne hH (Ne.symm hzero)) hcap
      hrho hrho1 hu huH hleaf

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows

-- Actual types and axioms.
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.half_light_phase_exists
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.half_light_phase_exists
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.half_light_boundary_positive
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.half_light_boundary_positive
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.half_light_boundary_minimum_positive
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.half_light_boundary_minimum_positive
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.half_light_payment_chain
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.half_light_payment_chain
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.half_light_payment_positive
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.half_light_payment_positive
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.closedParentPayment
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.closedParentPayment
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.half_light_closed_payment_positive
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.half_light_closed_payment_positive
