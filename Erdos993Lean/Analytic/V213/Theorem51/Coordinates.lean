module

public import Erdos993Lean.Analytic.V213.Theorem51.ScalarBinding
public import Erdos993Lean.Analytic.V213.ResponseLocalSplit
public import Erdos993Lean.Analytic.V213.ResponseFeasibleMessages

/-! Bridge 7: the contract coordinates are the messages and signed responses of
actual rooted forest branches. The zero-J case is the actual leaf convention. -/
@[expose] public section
noncomputable section

namespace Erdos993Lean.Analytic.V213.Theorem51

open Finset Erdos993Lean.Analytic Tail Reserve O2 VarianceResponse

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

theorem contract_p_actual (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    {s : Finset V} (hs : ConnectedIn G s) {v : V} (hv : v ∈ s) :
    F4Unified.p lam (Tmass G lam s v) = rootProb G lam s v := by
  simpa only [F4Unified.p, msg] using (message_recursion hG hl hs hv).symm

theorem contract_phi_actual {lam : ℝ} (hl : 0 < lam) (s : Finset V) (v : V) :
    F4Unified.phi (rootProb G lam s v) = yLog G lam s v := by
  simp only [F4Unified.phi, if_neg (rootProb_pos (G := G) hl s v).ne', yLog]

theorem contract_childH_actual {lam : ℝ} (hl : 0 < lam) (s : Finset V) (v : V) :
    F4Unified.childH (rootProb G lam s v) = responseH G lam s v := by
  simp only [F4Unified.childH, if_neg (rootProb_pos (G := G) hl s v).ne',
    contract_phi_actual hl, responseH]

theorem contract_childJ_actual (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    {s : Finset V} (hs : ConnectedIn G s) {v : V} (hv : v ∈ s) :
    F4Unified.childJ lam (rootProb G lam s v) = responseJ G lam s v := by
  rw [F4Unified.childJ, if_neg (rootProb_pos (G := G) hl s v).ne',
    contract_childH_actual hl, ← children_logmass_inverse hG hl hs hv]
  rfl

theorem contract_child_logmass_actual (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    {s : Finset V} (hs : ConnectedIn G s) {v : V} (hv : v ∈ s) :
    Real.log (lam*(1-rootProb G lam s v)/rootProb G lam s v) =
      Tmass G lam s v :=
  (children_logmass_inverse hG hl hs hv).symm

theorem contract_phi_sum_actual {lam : ℝ} (hl : 0 < lam) (s : Finset V) (v : V) :
    (∑ w ∈ nbrsIn G s v,
      F4Unified.phi (rootProb G lam (compIn G (s.erase v) w) w)) =
      Tmass G lam s v := by
  unfold Tmass
  exact Finset.sum_congr rfl fun w _ => contract_phi_actual hl _ w

theorem actual_feasible_vacancy (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    {K : Finset V} (hK : ConnectedIn G K) {r0 : V} (hr0 : r0 ∈ K)
    {s : Finset V} {v : V} {rho t : ℝ}
    (hrec : RootRecord G lam K r0 s v rho t) :
    F4Unified.FeasibleVacancy lam (Tmass G lam s v) rho := by
  have hs := rootRecord_connected hG hK hr0 hrec
  have hv := rootRecord_mem hr0 hrec
  have h := feasible_message_range hG hl hK hr0 hrec
  change 1/(1+lam*(1-F4Unified.p lam (Tmass G lam s v))) ≤ rho ∧ rho ≤ 1
  rw [contract_p_actual hG hl hs hv]
  exact h.2.2

theorem actual_record_rho_nonneg (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    {K : Finset V} (hK : ConnectedIn G K) {r0 : V} (hr0 : r0 ∈ K)
    {s : Finset V} {v : V} {rho t : ℝ}
    (hrec : RootRecord G lam K r0 s v rho t) : 0 ≤ rho := by
  have hp1 := rootProb_lt_one (G := G) hl.le (rootRecord_mem hr0 hrec)
  have hd : 0 < 1+lam*(1-rootProb G lam s v) := by positivity
  exact ((one_div_pos.mpr hd).trans_le
    (feasible_message_range hG hl hK hr0 hrec).2.2.1).le

theorem actual_child_cap (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    {s : Finset V} (hs : ConnectedIn G s) {v : V} (hv : v ∈ s)
    {w : V} (hw : w ∈ nbrsIn G s v) :
    0 < rootProb G lam (compIn G (s.erase v) w) w ∧
      rootProb G lam (compIn G (s.erase v) w) w ≤
        F4Unified.childCap lam (Tmass G lam s v) := by
  refine ⟨rootProb_pos hl _ _, ?_⟩
  have h := child_le_cavH hG hl hs hv hw
  rw [← contract_p_actual hG hl hs hv, contract_cavH hl] at h
  exact h

/-- The response y is unrestricted in sign; admissibility comes from the actual
child having positive mass or being a leaf, never from a response sign bound. -/
theorem actual_admissible (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    {s : Finset V} (hs : ConnectedIn G s) {v : V} (hv : v ∈ s) :
    F4Unified.Admissible lam (rootProb G lam s v) (responseY G lam s v) := by
  by_cases he : nbrsIn G s v = ∅
  · obtain ⟨hJ, hy⟩ := response_leaf_coordinates hG hl hs hv he
    refine Or.inr ⟨?_, ?_⟩
    · rwa [contract_childJ_actual hG hl hs hv]
    · rwa [contract_childH_actual hl]
  · apply Or.inl
    rw [contract_childJ_actual hG hl hs hv]
    have hp := rootProb_pos (G := G) hl s v
    have hphi := yLog_pos hG hl hs hv
    have hT := Tmass_pos hG hl hs hv (Finset.nonempty_iff_ne_empty.mpr he)
    exact mul_pos (mul_pos hp (div_pos hp hphi)) hT

/-- Every actual parent-child record lies in the contract's full pair domain. -/
theorem actual_child_pairDomain {r : F4Unified.Row} {lam : ℝ}
    (hrow : F4Unified.InRow r lam) (hG : G.IsAcyclic)
    {K : Finset V} (hK : ConnectedIn G K) {r0 : V} (hr0 : r0 ∈ K)
    {s : Finset V} {v : V} {rho t : ℝ}
    (hrec : RootRecord G lam K r0 s v rho t) {w : V}
    (hw : w ∈ nbrsIn G s v) :
    F4Unified.PairDomain r lam (Tmass G lam s v) rho
      (rootProb G lam (compIn G (s.erase v) w) w)
      (responseY G lam (compIn G (s.erase v) w) w) := by
  have hl := row_activity_pos hrow
  have hs := rootRecord_connected hG hK hr0 hrec
  have hv := rootRecord_mem hr0 hrec
  have hc := actual_child_cap hG hl hs hv hw
  exact ⟨hrow, Tmass_pos hG hl hs hv ⟨w,hw⟩,
    actual_feasible_vacancy hG hl hK hr0 hrec, hc.1.le, hc.2,
    actual_admissible hG hl (compIn_branch hG hs hv hw).1 (self_mem_branch hw)⟩

end Erdos993Lean.Analytic.V213.Theorem51

#check Erdos993Lean.Analytic.V213.Theorem51.contract_p_actual
#print axioms Erdos993Lean.Analytic.V213.Theorem51.contract_p_actual
#check Erdos993Lean.Analytic.V213.Theorem51.contract_phi_actual
#print axioms Erdos993Lean.Analytic.V213.Theorem51.contract_phi_actual
#check Erdos993Lean.Analytic.V213.Theorem51.contract_childH_actual
#print axioms Erdos993Lean.Analytic.V213.Theorem51.contract_childH_actual
#check Erdos993Lean.Analytic.V213.Theorem51.contract_childJ_actual
#print axioms Erdos993Lean.Analytic.V213.Theorem51.contract_childJ_actual
#check Erdos993Lean.Analytic.V213.Theorem51.contract_child_logmass_actual
#print axioms Erdos993Lean.Analytic.V213.Theorem51.contract_child_logmass_actual
#check Erdos993Lean.Analytic.V213.Theorem51.contract_phi_sum_actual
#print axioms Erdos993Lean.Analytic.V213.Theorem51.contract_phi_sum_actual
#check Erdos993Lean.Analytic.V213.Theorem51.actual_feasible_vacancy
#print axioms Erdos993Lean.Analytic.V213.Theorem51.actual_feasible_vacancy
#check Erdos993Lean.Analytic.V213.Theorem51.actual_record_rho_nonneg
#print axioms Erdos993Lean.Analytic.V213.Theorem51.actual_record_rho_nonneg
#check Erdos993Lean.Analytic.V213.Theorem51.actual_child_cap
#print axioms Erdos993Lean.Analytic.V213.Theorem51.actual_child_cap
#check Erdos993Lean.Analytic.V213.Theorem51.actual_admissible
#print axioms Erdos993Lean.Analytic.V213.Theorem51.actual_admissible
#check Erdos993Lean.Analytic.V213.Theorem51.actual_child_pairDomain
#print axioms Erdos993Lean.Analytic.V213.Theorem51.actual_child_pairDomain
