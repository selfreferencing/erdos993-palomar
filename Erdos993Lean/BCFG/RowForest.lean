module

public import Erdos993Lean.BCFG.RowPayment
public import Erdos993Lean.Analytic.V213.ForestPaymentAssembly

/-! B,C,F,G part of the forest assembly. The actual row payment theorem
discharges every local payment premise. Other rows and F4 are separate. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Erdos993Lean.BCFG.Analytic

open Finset Erdos993Lean.Analytic
open Erdos993Lean.Analytic.Tail Erdos993Lean.Analytic.Reserve Erdos993Lean.Analytic.O2
open Erdos993Lean.Analytic.V213.VarianceResponse

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

theorem bcfg_component_variance_bound (hG : G.IsAcyclic)
    {r : AnalyticRow} {lam : ℝ} (hrow : InRow r lam)
    {K : Finset V} (hK : ConnectedIn G K)
    (hKc : ∀ x ∈ K, ∀ y, G.Adj x y → y ∈ K) {r0 : V} (hr0 : r0 ∈ K) :
    varB G univ lam K ≤ price r lam*∑ v ∈ K, gMarg G lam v*sRef G lam v := by
  have hl := activity_pos hrow
  exact response_component_le_refined_of_payments hG hl (price r lam) (alpha r) (beta r)
    (gamma r lam) 0 (price_pos hl).le (gamma_pos hl).le (by norm_num) hK hKc hr0
    (fun s v rho t hrec => actual_bcfg_payment_nonneg hG hrow hK hr0 hrec)

theorem bcfg_forest_variance_refined (hG : G.IsAcyclic)
    {r : AnalyticRow} {lam : ℝ} (hrow : InRow r lam) :
    varB G univ lam univ ≤ price r lam*∑ v : V, gMarg G lam v*sRef G lam v := by
  exact response_closed_le_refined_of_components hG (activity_pos hrow) (price r lam)
    (fun K hK hKc r0 hr0 => bcfg_component_variance_bound hG hrow hK hKc hr0)
    univ (fun _ _ _ _ => mem_univ _)

/-- The B,C,F,G portion of printed Theorem 5.1 with an actual independent-set maximizer. -/
theorem bcfg_forest_variance_bound (hG : G.IsAcyclic)
    {r : AnalyticRow} {lam : ℝ} (hrow : InRow r lam)
    (A : Finset V) (_hA : IsIndepFinset G A)
    (hmax : ∀ B : Finset V, IsIndepFinset G B →
      (∑ v ∈ B, gMarg G lam v) ≤ ∑ v ∈ A, gMarg G lam v) :
    varB G univ lam univ ≤ price r lam*∑ v ∈ A, gMarg G lam v := by
  exact (bcfg_forest_variance_refined hG hrow).trans
    (mul_le_mul_of_nonneg_left
      (refined_source_le_maximum_weight hG (activity_pos hrow) A hmax)
      (price_pos (r := r) (activity_pos hrow)).le)

end Erdos993Lean.BCFG.Analytic

#check Erdos993Lean.BCFG.Analytic.bcfg_component_variance_bound
#print axioms Erdos993Lean.BCFG.Analytic.bcfg_component_variance_bound
#check Erdos993Lean.BCFG.Analytic.bcfg_forest_variance_refined
#print axioms Erdos993Lean.BCFG.Analytic.bcfg_forest_variance_refined
#check Erdos993Lean.BCFG.Analytic.bcfg_forest_variance_bound
#print axioms Erdos993Lean.BCFG.Analytic.bcfg_forest_variance_bound
