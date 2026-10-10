module

public import Erdos993Lean.Analytic.V213.ResponseMessages
public import Erdos993Lean.Analytic.O2.Ledger

/-!
# Current Lemma 5.4: local data on the actual descendants of a component root

Version 2.13 of the manuscript, f4:lem2.3. A `RootRecord` is generated from a chosen root
by the actual branch operation. The invariant of actual full-graph marginals
is proved from that construction, not taken as a hypothesis. The signed total
response is the finite-law `O2.zR`; no sign assumption is imposed on it.

The accepted Tail/Reserve/O2 finite-law and branch proofs retain their original
credits. Only their generic identities are used, not any old band payment,
variance bound, certificate table, or completed profile theorem.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse

open Finset

variable {V : Type*} [DecidableEq V]

/-- Actual ancestry from the selected component root, with incoming parent message.
The unused incoming message at the component root is assigned zero. -/
inductive RootRecord (G : SimpleGraph V) [DecidableRel G.Adj]
    (lam : ℝ) (K : Finset V) (r0 : V) : Finset V → V → ℝ → ℝ → Prop
  | top : RootRecord G lam K r0 K r0 1 0
  | child {s : Finset V} {v : V} {rho t : ℝ} {w : V}
      (parent : RootRecord G lam K r0 s v rho t) (hw : w ∈ nbrsIn G s v) :
      RootRecord G lam K r0 (compIn G (s.erase v) w) w
        (1 - rho * Tail.rootProb G lam s v) (Tail.rootProb G lam s v)

variable {G : SimpleGraph V} [DecidableRel G.Adj]
  {lam : ℝ} {K : Finset V} {r0 : V}

theorem rootRecord_mem (hr0 : r0 ∈ K) {s : Finset V} {v : V} {rho t : ℝ}
    (hrec : RootRecord G lam K r0 s v rho t) : v ∈ s := by
  induction hrec with
  | top => exact hr0
  | child parent hw ih => exact self_mem_branch hw

theorem rootRecord_connected (hG : G.IsAcyclic) (hK : ConnectedIn G K)
    (hr0 : r0 ∈ K) {s : Finset V} {v : V} {rho t : ℝ}
    (hrec : RootRecord G lam K r0 s v rho t) : ConnectedIn G s := by
  induction hrec with
  | top => exact hK
  | child parent hw ih =>
      exact (compIn_branch hG ih (rootRecord_mem hr0 parent) hw).1

/-- Every vertex is represented by an actual generated descendant record. -/
theorem rootRecord_covers_component (hG : G.IsAcyclic) (hK : ConnectedIn G K)
    (hr0 : r0 ∈ K) {x : V} (hx : x ∈ K) :
    ∃ s rho t, RootRecord G lam K r0 s x rho t := by
  have hcover : ∀ {s : Finset V} (hs : ConnectedIn G s) {v : V} (hv : v ∈ s),
      ∀ rho t, RootRecord G lam K r0 s v rho t →
        ∀ x ∈ s, ∃ s' rho' t', RootRecord G lam K r0 s' x rho' t' := by
    intro s hs v hv
    refine Tail.rooted_induction hG (P := fun s v =>
      ∀ rho t, RootRecord G lam K r0 s v rho t →
        ∀ x ∈ s, ∃ s' rho' t', RootRecord G lam K r0 s' x rho' t') ?_ hs hv
    intro s v hs hv ih rho t hrec x hx
    by_cases heq : x = v
    · subst x
      exact ⟨s, rho, t, hrec⟩
    · have hxe : x ∈ s.erase v := Finset.mem_erase.mpr ⟨heq, hx⟩
      rw [erase_eq_biUnion hs hv, Finset.mem_biUnion] at hxe
      obtain ⟨w, hw, hxw⟩ := hxe
      exact ih w hw _ _ (RootRecord.child hrec hw) x hxw
  exact hcover hK hr0 1 0 RootRecord.top x hx

section FiniteGraph

variable [Fintype V]

theorem rootRecord_source_invariant (hG : G.IsAcyclic) (hlam : 0 < lam)
    (hKc : ∀ x ∈ K, ∀ y, G.Adj x y → y ∈ K) (hr0 : r0 ∈ K)
    {s : Finset V} {v : V} {rho t : ℝ}
    (hrec : RootRecord G lam K r0 s v rho t) : O2.SrcInv G lam s v rho t := by
  induction hrec with
  | top => exact O2.srcInv_top hlam hKc 0
  | child parent hw ih =>
      exact O2.srcInv_child hG hlam (rootRecord_mem hr0 parent) ih hw

theorem rootRecord_rho_bounds (hG : G.IsAcyclic) (hlam : 0 < lam)
    (hKc : ∀ x ∈ K, ∀ y, G.Adj x y → y ∈ K) (hr0 : r0 ∈ K)
    {s : Finset V} {v : V} {rho t : ℝ}
    (hrec : RootRecord G lam K r0 s v rho t) : 0 ≤ rho ∧ rho ≤ 1 :=
  (rootRecord_source_invariant hG hlam hKc hr0 hrec).2.2

/-- Lemma 5.4(a): the actual full-graph marginal is the boundary mixture weight times p. -/
theorem rootRecord_marginal (hG : G.IsAcyclic) (hlam : 0 < lam)
    (hKc : ∀ x ∈ K, ∀ y, G.Adj x y → y ∈ K) (hr0 : r0 ∈ K)
    {s : Finset V} {v : V} {rho t : ℝ}
    (hrec : RootRecord G lam K r0 s v rho t) :
    O2.gMarg G lam v = rho * Tail.rootProb G lam s v := by
  have hv := rootRecord_mem hr0 hrec
  rw [(rootRecord_source_invariant hG hlam hKc hr0 hrec).1 v hv,
    Tail.mu_root hv]

/-- The boundary weight is the actual vacancy probability of the external parent. -/
theorem rootRecord_parent_vacancy (hG : G.IsAcyclic) (hlam : 0 < lam)
    (hKc : ∀ x ∈ K, ∀ y, G.Adj x y → y ∈ K) (hr0 : r0 ∈ K)
    {s : Finset V} {v : V} {rho t : ℝ}
    (hrec : RootRecord G lam K r0 s v rho t) {w : V}
    (hvw : G.Adj v w) (hw : w ∉ s) : rho = 1 - O2.gMarg G lam w := by
  have h := (rootRecord_source_invariant hG hlam hKc hr0 hrec).2.1
    v (rootRecord_mem hr0 hrec) w hvw hw
  linarith [h.2]

/-- Each child's generated boundary is exactly one minus its parent's actual marginal. -/
theorem rootRecord_child_vacancy (hG : G.IsAcyclic) (hlam : 0 < lam)
    (hKc : ∀ x ∈ K, ∀ y, G.Adj x y → y ∈ K) (hr0 : r0 ∈ K)
    {s : Finset V} {v : V} {rho t : ℝ}
    (hrec : RootRecord G lam K r0 s v rho t) {w : V}
    (hw : w ∈ nbrsIn G s v) :
    RootRecord G lam K r0 (compIn G (s.erase v) w) w
      (1 - O2.gMarg G lam v) (Tail.rootProb G lam s v) := by
  rw [rootRecord_marginal hG hlam hKc hr0 hrec]
  exact RootRecord.child hrec hw

theorem response_eq_mean_difference (s : Finset V) (v : V) :
    O2.zR G lam s v = 1 +
      Reserve.meanB G Finset.univ lam (outsideClosedNbhd G s v) -
      Reserve.meanB G Finset.univ lam (s.erase v) := rfl

theorem response_recursion (hG : G.IsAcyclic) (hlam : 0 < lam)
    {s : Finset V} (hs : ConnectedIn G s) {v : V} (hv : v ∈ s) :
    O2.zR G lam s v = 1 - ∑ w ∈ nbrsIn G s v,
      Tail.rootProb G lam (compIn G (s.erase v) w) w *
        O2.zR G lam (compIn G (s.erase v) w) w :=
  O2.zR_rec hG hlam.le hs hv

theorem response_leaf (hG : G.IsAcyclic) (hlam : 0 < lam)
    {s : Finset V} (hs : ConnectedIn G s) {v : V} (hv : v ∈ s)
    (hchild : nbrsIn G s v = ∅) : O2.zR G lam s v = 1 :=
  O2.zR_of_nbrsIn_empty hG hlam.le hs hv hchild

end FiniteGraph

theorem children_logmass_inverse (hG : G.IsAcyclic) (hlam : 0 < lam)
    {s : Finset V} (hs : ConnectedIn G s) {v : V} (hv : v ∈ s) :
    Reserve.Tmass G lam s v =
      Real.log (lam * (1 - Tail.rootProb G lam s v) / Tail.rootProb G lam s v) := by
  simpa only [O2.logMass] using (O2.logMass_eq_Tmass hG hlam hs hv).symm

end Erdos993Lean.Analytic.V213.VarianceResponse

#check Erdos993Lean.Analytic.V213.VarianceResponse.RootRecord
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RootRecord
#check Erdos993Lean.Analytic.V213.VarianceResponse.rootRecord_mem
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.rootRecord_mem
#check Erdos993Lean.Analytic.V213.VarianceResponse.rootRecord_connected
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.rootRecord_connected
#check Erdos993Lean.Analytic.V213.VarianceResponse.rootRecord_covers_component
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.rootRecord_covers_component
#check Erdos993Lean.Analytic.V213.VarianceResponse.rootRecord_source_invariant
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.rootRecord_source_invariant
#check Erdos993Lean.Analytic.V213.VarianceResponse.rootRecord_rho_bounds
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.rootRecord_rho_bounds
#check Erdos993Lean.Analytic.V213.VarianceResponse.rootRecord_marginal
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.rootRecord_marginal
#check Erdos993Lean.Analytic.V213.VarianceResponse.rootRecord_parent_vacancy
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.rootRecord_parent_vacancy
#check Erdos993Lean.Analytic.V213.VarianceResponse.rootRecord_child_vacancy
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.rootRecord_child_vacancy
#check Erdos993Lean.Analytic.V213.VarianceResponse.response_eq_mean_difference
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.response_eq_mean_difference
#check Erdos993Lean.Analytic.V213.VarianceResponse.response_recursion
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.response_recursion
#check Erdos993Lean.Analytic.V213.VarianceResponse.response_leaf
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.response_leaf
#check Erdos993Lean.Analytic.V213.VarianceResponse.children_logmass_inverse
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.children_logmass_inverse
