module

public import Erdos993Lean.Analytic.V213.ResponseLocalData

/-!
Current printed Lemma 5.6, f4:lem2.5.
Every field here comes from actual component-root ancestry. A physical-record
condition is proved by induction, then eliminated from the public printed range.
No parent parameter or physical-record assertion is a hypothesis of that range.
The accepted generic parent-product bound is reused with its original credits.

-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse

open Finset

variable {V : Type*} [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {lam : ℝ} {K : Finset V} {r0 : V}

theorem rootRecord_physical (hG : G.IsAcyclic) (hlam : 0 < lam)
    (hK : ConnectedIn G K) (hr0 : r0 ∈ K)
    {s : Finset V} {v : V} {rho t : ℝ}
    (hrec : RootRecord G lam K r0 s v rho t) :
    O2.PhysRecord lam (Tail.rootProb G lam s v) rho t := by
  induction hrec with
  | top =>
      have hp1 : 0 < 1-Tail.rootProb G lam K r0 := by
        linarith [message_lt_one (G := G) hlam hr0]
      refine ⟨Tail.rootProb_pos (G := G) hlam K r0, Tail.rootProb_le_actQ (G := G) hlam.le hr0,
        le_rfl, ?_, ?_, ?_⟩
      · norm_num
      · positivity
      · simp
  | child parent hw ih =>
      exact O2.physRecord_child hG hlam (rootRecord_connected hG hK hr0 parent)
        (rootRecord_mem hr0 parent) ih.rho_le_one (ih.one_le_rho_mul hlam) hw

theorem rootRecord_vacancy_lower (hG : G.IsAcyclic) (hlam : 0 < lam)
    (hK : ConnectedIn G K) (hr0 : r0 ∈ K)
    {s : Finset V} {v : V} {rho t : ℝ}
    (hrec : RootRecord G lam K r0 s v rho t) :
    1/(1+lam*(1-Tail.rootProb G lam s v)) ≤ rho := by
  have hphys := rootRecord_physical hG hlam hK hr0 hrec
  have hp1 : 0 < 1-Tail.rootProb G lam s v := by
    linarith [message_lt_one (G := G) hlam (rootRecord_mem hr0 hrec)]
  have hd : 0 < 1+lam*(1-Tail.rootProb G lam s v) := by positivity
  rw [div_le_iff₀ hd]
  exact hphys.one_le_rho_mul hlam

theorem feasible_message_range (hG : G.IsAcyclic) (hlam : 0 < lam)
    (hK : ConnectedIn G K) (hr0 : r0 ∈ K)
    {s : Finset V} {v : V} {rho t : ℝ}
    (hrec : RootRecord G lam K r0 s v rho t) :
    0 < Tail.rootProb G lam s v ∧ Tail.rootProb G lam s v ≤ actQ lam ∧
      1/(1+lam*(1-Tail.rootProb G lam s v)) ≤ rho ∧ rho ≤ 1 := by
  have hphys := rootRecord_physical hG hlam hK hr0 hrec
  exact ⟨hphys.1,hphys.2.1,rootRecord_vacancy_lower hG hlam hK hr0 hrec,hphys.rho_le_one⟩

theorem feasible_message_range_root (hG : G.IsAcyclic) (hlam : 0 < lam)
    (hK : ConnectedIn G K) (hr0 : r0 ∈ K) :
    0 < Tail.rootProb G lam K r0 ∧ Tail.rootProb G lam K r0 ≤ actQ lam ∧
      1/(1+lam*(1-Tail.rootProb G lam K r0)) ≤ 1 := by
  have h := feasible_message_range hG hlam hK hr0
    (RootRecord.top : RootRecord G lam K r0 K r0 1 0)
  exact ⟨h.1,h.2.1,h.2.2.1⟩

theorem feasible_message_range_leaf (hG : G.IsAcyclic) (hlam : 0 < lam)
    (hK : ConnectedIn G K) (hr0 : r0 ∈ K)
    {s : Finset V} {v : V} {rho t : ℝ}
    (hrec : RootRecord G lam K r0 s v rho t) (hchild : nbrsIn G s v = ∅) :
    Tail.rootProb G lam s v = actQ lam ∧
      1/(1+lam*(1-actQ lam)) ≤ rho ∧ rho ≤ 1 := by
  have hpq := (message_eq_q_iff_no_children hlam (rootRecord_mem hr0 hrec)).mpr hchild
  have h := feasible_message_range hG hlam hK hr0 hrec
  refine ⟨hpq,?_,h.2.2.2⟩
  simpa only [hpq] using h.2.2.1

end Erdos993Lean.Analytic.V213.VarianceResponse

#check Erdos993Lean.Analytic.V213.VarianceResponse.rootRecord_physical
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.rootRecord_physical
#check Erdos993Lean.Analytic.V213.VarianceResponse.rootRecord_vacancy_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.rootRecord_vacancy_lower
#check Erdos993Lean.Analytic.V213.VarianceResponse.feasible_message_range
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.feasible_message_range
#check Erdos993Lean.Analytic.V213.VarianceResponse.feasible_message_range_root
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.feasible_message_range_root
#check Erdos993Lean.Analytic.V213.VarianceResponse.feasible_message_range_leaf
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.feasible_message_range_leaf

-- Inherited interface audits.
#check Erdos993Lean.Analytic.O2.PhysRecord.rho_le_one
#print axioms Erdos993Lean.Analytic.O2.PhysRecord.rho_le_one
#check Erdos993Lean.Analytic.O2.PhysRecord.one_le_rho_mul
#print axioms Erdos993Lean.Analytic.O2.PhysRecord.one_le_rho_mul
#check Erdos993Lean.Analytic.O2.physRecord_child
#print axioms Erdos993Lean.Analytic.O2.physRecord_child
