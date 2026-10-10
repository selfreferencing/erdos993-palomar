module

public import Erdos993Lean.Analytic.V213.ForestPaymentAssembly
public import Erdos993Lean.Analytic.V213.RowAProposition

/-! The row A part of printed Theorem 5.1. All local
payment hypotheses are discharged by Proposition 5.12. The other rows and the
F4 binding are outside this theorem. -/

@[expose] public section

set_option autoImplicit false

namespace Erdos993Lean.Analytic.V213.VarianceResponse.RowA

open Finset Tail Reserve O2

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The Row A component conclusion with the actual payment premise discharged. -/
theorem rowA_component_variance_bound (hG : G.IsAcyclic) {lam : ℝ}
    (hl : (1:ℝ)/3 ≤ lam) (hu : lam ≤ 3/5)
    {K : Finset V} (hK : ConnectedIn G K)
    (hKc : ∀ x ∈ K, ∀ y, G.Adj x y → y ∈ K) {r : V} (hr : r ∈ K) :
    varB G univ lam K ≤ (2/(1+lam))*∑ v ∈ K, gMarg G lam v*sRef G lam v := by
  have hl0 : 0 < lam := by linarith
  exact response_component_le_refined_of_payments hG hl0 (2/(1+lam)) 1 (7/6)
    (7*lam/20) 0 (by positivity) (by positivity) (by norm_num) hK hKc hr
    (fun s v rho t hrec => (rowA_payment_pos hG hl hu hK hKc hr hrec).le)

/-- The Row A forest variance bound before the final maximum-weight comparison. -/
theorem rowA_forest_variance_refined (hG : G.IsAcyclic) {lam : ℝ}
    (hl : (1:ℝ)/3 ≤ lam) (hu : lam ≤ 3/5) :
    varB G univ lam univ ≤ (2/(1+lam))*∑ v : V, gMarg G lam v*sRef G lam v := by
  have hl0 : 0 < lam := by linarith
  exact response_closed_le_refined_of_components hG hl0 (2/(1+lam))
    (fun K hK hKc r hr => rowA_component_variance_bound hG hl hu hK hKc hr)
    univ (fun _ _ _ _ => mem_univ _)

/-- Printed Theorem 5.1 on Row A, with an actual maximum-weight independent set. -/
theorem rowA_forest_variance_bound (hG : G.IsAcyclic) {lam : ℝ}
    (hl : (1:ℝ)/3 ≤ lam) (hu : lam ≤ 3/5)
    (A : Finset V) (_hA : IsIndepFinset G A)
    (hmax : ∀ B : Finset V, IsIndepFinset G B →
      (∑ v ∈ B, gMarg G lam v) ≤ ∑ v ∈ A, gMarg G lam v) :
    varB G univ lam univ ≤ (2/(1+lam))*∑ v ∈ A, gMarg G lam v := by
  have hl0 : 0 < lam := by linarith
  exact (rowA_forest_variance_refined hG hl hu).trans
    (mul_le_mul_of_nonneg_left (refined_source_le_maximum_weight hG hl0 A hmax)
      (by positivity))

end Erdos993Lean.Analytic.V213.VarianceResponse.RowA

#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.rowA_component_variance_bound
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.rowA_component_variance_bound
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.rowA_forest_variance_refined
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.rowA_forest_variance_refined
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.rowA_forest_variance_bound
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.rowA_forest_variance_bound
