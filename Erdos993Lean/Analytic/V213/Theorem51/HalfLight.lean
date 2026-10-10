module

public import Erdos993Lean.Analytic.V213.Theorem51.ScalarBinding
public import Erdos993Lean.Analytic.V213.ResponseHalfLightTheorem

/-! The unified contract's half-light proposition follows from the accepted
attained minimum and boundary positivity. No light-core premise is used. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.Theorem51

open VarianceResponse

theorem halfLight (r : F4Unified.Row) : F4Unified.HalfLight r := by
  intro lam Y rho hrow hY hcap hr
  have hrow' := (inRow_iff r lam).mp hrow
  have hl := row_activity_pos hrow
  have hH := parentH_pos hY
  have hcap' : F4Unified.parentH Y ≤ childQ lam / 2 := hcap
  have hrmin : rhoMin lam (ParentRows.halfParent lam (F4Unified.parentH Y)) ≤ rho := by
    rw [← p_eq_halfParent lam Y]
    exact hr.1
  have hJ : 0 < VarianceResponse.childJ lam (F4Unified.parentH Y) :=
    (half_child_bounds hl hH hcap').2.2.2.1
  have hJ' : 0 < F4Unified.childJ lam (F4Unified.parentH Y) := by
    rw [contract_childJ_eq_childJ]
    exact hJ
  obtain ⟨hLower, y, hy⟩ :=
    ParentRows.parentMinimum_is_minimum hrow' hH hcap' hr.2 hH le_rfl
  refine ⟨ParentRows.parentMinimum (parentRowIndex r) lam
    (F4Unified.parentH Y) rho (F4Unified.parentH Y), ⟨?_, ?_⟩, ?_⟩
  · intro z hz
    rw [payment_eq_parentPayment hl hY.le hr hz]
    exact hLower z
  · refine ⟨y, Or.inl hJ', ?_⟩
    rw [payment_eq_parentPayment hl hY.le hr (Or.inl hJ')]
    exact hy
  · exact ParentRows.half_light_boundary_minimum_positive hrow' hH hcap' hrmin hr.2

theorem halfLight_all : ∀ r : F4Unified.Row, F4Unified.HalfLight r := halfLight

end Erdos993Lean.Analytic.V213.Theorem51

#check Erdos993Lean.Analytic.V213.Theorem51.halfLight
#print axioms Erdos993Lean.Analytic.V213.Theorem51.halfLight
#check Erdos993Lean.Analytic.V213.Theorem51.halfLight_all
#print axioms Erdos993Lean.Analytic.V213.Theorem51.halfLight_all
