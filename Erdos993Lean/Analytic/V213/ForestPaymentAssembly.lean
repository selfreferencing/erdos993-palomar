module

public import Erdos993Lean.Analytic.V213.ResponsePayment

/-!
The final component and independent-set steps in
T8b. The generic component theorem is infrastructure, not an accepted all-row
Theorem 5.1: its payment premise must be discharged by each actual row proof.
-/

@[expose] public section

set_option autoImplicit false

namespace Erdos993Lean.Analytic.V213.VarianceResponse

open Finset Tail Reserve O2

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Printed Lemma 5.8 along the actual component fold. -/
theorem responseSourceFold_le_refined (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    {K : Finset V} (hK : ConnectedIn G K)
    (hKc : ∀ x ∈ K, ∀ y, G.Adj x y → y ∈ K) {r : V} (hr : r ∈ K) :
    dfold G lam (responseSourceMass G lam) K r 1 0 ≤
      ∑ v ∈ K, gMarg G lam v*sRef G lam v := by
  change dfold G lam (gT G lam) K r 1 0 ≤ _
  rw [← dfold_const hG lam (fun v => gMarg G lam v*sRef G lam v) hK hr 1 0]
  exact dfold_le_of_inv hG lam (SrcInv G lam)
    (fun s v rho t _ hv h w hw => srcInv_child hG hl hv h hw)
    (fun s v rho t hs hv h => gT_le hG hl hs hv h)
    hK hr (srcInv_top hl hKc 0)

/-- The exact payment identity plus the refined source gives the component bound. -/
theorem response_component_le_refined_of_payments (hG : G.IsAcyclic)
    {lam : ℝ} (hl : 0 < lam) (price alpha beta gamma delta : ℝ)
    (hprice : 0 ≤ price) (hgamma : 0 ≤ gamma) (hdelta : 0 ≤ delta)
    {K : Finset V} (hK : ConnectedIn G K)
    (hKc : ∀ x ∈ K, ∀ y, G.Adj x y → y ∈ K) {r : V} (hr : r ∈ K)
    (hpay : ∀ s v rho t, RootRecord G lam K r s v rho t →
      0 ≤ responsePayment G lam price alpha beta gamma delta s v rho t) :
    varB G univ lam K ≤ price*∑ v ∈ K, gMarg G lam v*sRef G lam v :=
  (response_variance_le_of_payments hG hl price alpha beta gamma delta
    hgamma hdelta hK hr hpay).trans
      (mul_le_mul_of_nonneg_left (responseSourceFold_le_refined hG hl hK hKc hr) hprice)

/-- Independent components add. Each concrete application discharges hcomponent. -/
theorem response_closed_le_refined_of_components (hG : G.IsAcyclic)
    {lam : ℝ} (hl : 0 < lam) (price : ℝ)
    (hcomponent : ∀ K : Finset V, ConnectedIn G K →
      (∀ x ∈ K, ∀ y, G.Adj x y → y ∈ K) → ∀ r ∈ K,
      varB G univ lam K ≤ price*∑ v ∈ K, gMarg G lam v*sRef G lam v) :
    ∀ s : Finset V, (∀ x ∈ s, ∀ y, G.Adj x y → y ∈ s) →
      varB G univ lam s ≤ price*∑ v ∈ s, gMarg G lam v*sRef G lam v := by
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
      intro hsc
      rcases s.eq_empty_or_nonempty with hs0 | ⟨x,hx⟩
      · rw [hs0,varB_empty,Finset.sum_empty,mul_zero]
      · have hKs : compIn G s x ⊆ s := compIn_subset _ _
        have hxK : x ∈ compIn G s x := self_mem_compIn hx
        have hKc : ∀ v ∈ compIn G s x, ∀ w, G.Adj v w → w ∈ compIn G s x :=
          fun v hv w hvw => mem_compIn_of_adjIn hv ⟨hKs hv,hsc v (hKs hv) w hvw,hvw⟩
        have hno : ∀ a ∈ compIn G s x, ∀ b ∈ s \ compIn G s x, ¬ G.Adj a b := by
          intro a ha b hb hab
          rw [Finset.mem_sdiff] at hb
          exact hb.2 (mem_compIn_of_adjIn ha ⟨hKs ha,hb.1,hab⟩)
        have hRc : ∀ v ∈ s \ compIn G s x, ∀ w, G.Adj v w → w ∈ s \ compIn G s x := by
          intro v hv w hvw
          rw [Finset.mem_sdiff] at hv ⊢
          refine ⟨hsc v hv.1 w hvw,fun hwK => hv.2 ?_⟩
          exact mem_compIn_of_adjIn hwK ⟨hKs hwK,hv.1,hvw.symm⟩
        have hK1 := hcomponent (compIn G s x) (connectedIn_compIn s x) hKc x hxK
        have hR1 := ih (s \ compIn G s x) (Finset.sdiff_ssubset hKs ⟨x,hxK⟩) hRc
        have hsplit : s = compIn G s x ∪ (s \ compIn G s x) :=
          (Finset.union_sdiff_of_subset hKs).symm
        rw [hsplit,varB_union hl.le Finset.disjoint_sdiff hno,
          Finset.sum_union Finset.disjoint_sdiff]
        linarith

/-- The only maximum-weight step in T8b; the competitor is an actual independent set. -/
theorem refined_source_le_maximum_weight (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    (A : Finset V)
    (hmax : ∀ B : Finset V, IsIndepFinset G B →
      (∑ v ∈ B, gMarg G lam v) ≤ ∑ v ∈ A, gMarg G lam v) :
    (∑ v : V, gMarg G lam v*sRef G lam v) ≤ ∑ v ∈ A, gMarg G lam v := by
  obtain ⟨B,hBs,hBi,hB⟩ := dp_closed (gMarg G lam) (sRef G lam) hG
    (fun v => sRef_nonneg hl v) (fun v => sRef_le_one hl v)
    (fun u v huv => sRef_edge huv) univ (fun _ _ _ _ => mem_univ _)
  exact hB.trans (hmax B hBi)

end Erdos993Lean.Analytic.V213.VarianceResponse

#check Erdos993Lean.Analytic.V213.VarianceResponse.responseSourceFold_le_refined
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.responseSourceFold_le_refined
#check Erdos993Lean.Analytic.V213.VarianceResponse.response_component_le_refined_of_payments
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.response_component_le_refined_of_payments
#check Erdos993Lean.Analytic.V213.VarianceResponse.response_closed_le_refined_of_components
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.response_closed_le_refined_of_components
#check Erdos993Lean.Analytic.V213.VarianceResponse.refined_source_le_maximum_weight
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.refined_source_le_maximum_weight
