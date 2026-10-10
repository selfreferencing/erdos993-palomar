module

public import Erdos993Lean.Analytic.V213.Theorem51.LeafBinding
public import Erdos993Lean.Analytic.V213.Theorem51.PaymentBinding
public import Erdos993Lean.Analytic.V213.Theorem51.MultiplierSigns
public import Erdos993Lean.Analytic.V213.ForestPaymentAssembly

/-! Forest assembly from the contract's pair and leaf propositions. All scalar
premises stay explicit here; the final module supplies them from the regional
targets and the single light-core hypothesis. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.Theorem51

open Finset Erdos993Lean.Analytic Tail Reserve O2 VarianceResponse

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

theorem heavy_actual_payment_nonneg {r : F4Unified.Row}
    (hpair : F4Unified.PairPositive r) (hleaf : F4Unified.LeafPositive r)
    (hG : G.IsAcyclic) {lam : ℝ} (hrow : F4Unified.InRow r lam)
    {K : Finset V} (hK : ConnectedIn G K)
    (hKc : ∀ x ∈ K, ∀ y, G.Adj x y → y ∈ K) {r0 : V} (hr0 : r0 ∈ K)
    {s : Finset V} {v : V} {rho t : ℝ}
    (hrec : RootRecord G lam K r0 s v rho t) :
    0 ≤ responsePayment G lam ((F4Unified.rowData r).price/(1+lam))
      (F4Unified.alpha r lam) (F4Unified.beta r lam) (F4Unified.gamma r lam)
      (F4Unified.delta r lam) s v rho t := by
  by_cases hchild : nbrsIn G s v = ∅
  · exact (actual_leaf_payment_pos hleaf hG hrow hK hr0 hrec hchild).le
  · apply rootRecord_payment_nonneg_of_children hG (row_activity_pos hrow)
      _ _ _ _ _ (gamma_pos hrow).le (delta_pos hrow) hK hKc hr0 hrec
      (Finset.nonempty_iff_ne_empty.mpr hchild)
    intro w hw
    simpa only [price_eq r lam, ← alpha_eq r lam, ← beta_eq r lam,
      ← gamma_eq r lam, ← delta_eq r lam] using
      (actual_child_payment_nonneg hpair hrow hG hK hr0 hrec hw)

theorem heavy_component_variance_bound_of_pairPositive {r : F4Unified.Row}
    (hpair : F4Unified.PairPositive r) (hleaf : F4Unified.LeafPositive r)
    (hG : G.IsAcyclic) {lam : ℝ} (hrow : F4Unified.InRow r lam)
    {K : Finset V} (hK : ConnectedIn G K)
    (hKc : ∀ x ∈ K, ∀ y, G.Adj x y → y ∈ K) {r0 : V} (hr0 : r0 ∈ K) :
    varB G univ lam K ≤ ((F4Unified.rowData r).price/(1+lam))*
      ∑ v ∈ K, gMarg G lam v*sRef G lam v := by
  exact response_component_le_refined_of_payments hG (row_activity_pos hrow)
    _ _ _ _ _ (price_nonneg hrow) (gamma_pos hrow).le (delta_pos hrow).le
    hK hKc hr0 (fun s v rho t hrec =>
      heavy_actual_payment_nonneg hpair hleaf hG hrow hK hKc hr0 hrec)

theorem heavy_forest_variance_refined_of_pairPositive {r : F4Unified.Row}
    (hpair : F4Unified.PairPositive r) (hleaf : F4Unified.LeafPositive r)
    (hG : G.IsAcyclic) {lam : ℝ} (hrow : F4Unified.InRow r lam) :
    varB G univ lam univ ≤ ((F4Unified.rowData r).price/(1+lam))*
      ∑ v : V, gMarg G lam v*sRef G lam v := by
  exact response_closed_le_refined_of_components hG (row_activity_pos hrow) _
    (fun K hK hKc r0 hr0 =>
      heavy_component_variance_bound_of_pairPositive hpair hleaf hG hrow hK hKc hr0)
    univ (fun _ _ _ _ => mem_univ _)

theorem heavy_forest_variance_bound_of_pairPositive {r : F4Unified.Row}
    (hpair : F4Unified.PairPositive r) (hleaf : F4Unified.LeafPositive r)
    (hG : G.IsAcyclic) {lam : ℝ} (hrow : F4Unified.InRow r lam)
    (A : Finset V) (_hA : IsIndepFinset G A)
    (hmax : ∀ B : Finset V, IsIndepFinset G B →
      (∑ v ∈ B, gMarg G lam v) ≤ ∑ v ∈ A, gMarg G lam v) :
    varB G univ lam univ ≤ ((F4Unified.rowData r).price/(1+lam))*
      ∑ v ∈ A, gMarg G lam v := by
  exact (heavy_forest_variance_refined_of_pairPositive hpair hleaf hG hrow).trans
    (mul_le_mul_of_nonneg_left
      (refined_source_le_maximum_weight hG (row_activity_pos hrow) A hmax)
      (price_nonneg hrow))

end Erdos993Lean.Analytic.V213.Theorem51

#check Erdos993Lean.Analytic.V213.Theorem51.heavy_actual_payment_nonneg
#print axioms Erdos993Lean.Analytic.V213.Theorem51.heavy_actual_payment_nonneg
#check Erdos993Lean.Analytic.V213.Theorem51.heavy_component_variance_bound_of_pairPositive
#print axioms Erdos993Lean.Analytic.V213.Theorem51.heavy_component_variance_bound_of_pairPositive
#check Erdos993Lean.Analytic.V213.Theorem51.heavy_forest_variance_refined_of_pairPositive
#print axioms Erdos993Lean.Analytic.V213.Theorem51.heavy_forest_variance_refined_of_pairPositive
#check Erdos993Lean.Analytic.V213.Theorem51.heavy_forest_variance_bound_of_pairPositive
#print axioms Erdos993Lean.Analytic.V213.Theorem51.heavy_forest_variance_bound_of_pairPositive
