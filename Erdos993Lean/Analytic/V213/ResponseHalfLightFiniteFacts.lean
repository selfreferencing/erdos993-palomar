module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightGatesAll
public import Erdos993Lean.Analytic.V213.ResponseHalfLightProductShapesAll
public import Erdos993Lean.Analytic.V213.ResponseControlGateCoverage

/-! Literal finite proof references only; no external polynomial computation. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates

theorem controlGateCoverage_all : ∀ c : Fin 97, ControlGateCoverage c := by decide +kernel

theorem degreeLambda_at_least_two (r : Fin 8) : 2 <= (productSpec r).degreeLambda := by
  fin_cases r <;> norm_num [productSpec]

theorem control_indices_complete_finite :
    ∀ r : Fin 8, ∀ j : Fin ((productSpec r).degreeXi+1), ∃ c : Fin 97,
      (controlSpec c).product=r ∧ (controlSpec c).index=j.val := by decide +kernel

theorem control_indices_complete (r : Fin 8) :
    ∀ j ≤ (productSpec r).degreeXi, ∃ c : Fin 97,
      (controlSpec c).product=r ∧ (controlSpec c).index=j := by
  intro j hj
  exact control_indices_complete_finite r ⟨j,Nat.lt_succ_of_le hj⟩

theorem product_row_phase_cover (i : Fin 4) (phase : Nat) (hphase : phase=1 ∨ phase=2) :
    ∃ r : Fin 8, (productSpec r).rowIndex=i ∧ (productSpec r).phase=phase := by
  rcases hphase with rfl | rfl
  · fin_cases i
    · exact ⟨0,rfl,rfl⟩
    · exact ⟨2,rfl,rfl⟩
    · exact ⟨4,rfl,rfl⟩
    · exact ⟨6,rfl,rfl⟩
  · fin_cases i
    · exact ⟨1,rfl,rfl⟩
    · exact ⟨3,rfl,rfl⟩
    · exact ⟨5,rfl,rfl⟩
    · exact ⟨7,rfl,rfl⟩

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.controlGateCoverage_all
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.controlGateCoverage_all
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.degreeLambda_at_least_two
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.degreeLambda_at_least_two
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.control_indices_complete_finite
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.control_indices_complete_finite
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.control_indices_complete
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.control_indices_complete
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.product_row_phase_cover
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.product_row_phase_cover
