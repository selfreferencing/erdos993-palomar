module

public import Erdos993Lean.Analytic.V213.ResponseRootedPartitions
public import Erdos993Lean.Analytic.Reserve.Tree

/-!
# Current Lemma 5.2: positive messages of actual rooted subtrees

Version 2.13 of the manuscript, f4:lem2.1. The actual finite-law interpretation is supplied
by ResponseRootedPartitions. The accepted Tail and Reserve recursion proofs
are specialized to the printed objects; their original credits are retained.
No component-size restriction or numerical enclosure occurs here.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem message_odds (hG : G.IsAcyclic) {lam : ℝ} (hlam : 0 < lam)
    {s : Finset V} (hs : ConnectedIn G s) {v : V} (hv : v ∈ s) :
    Tail.rootProb G lam s v / (1 - Tail.rootProb G lam s v) =
      lam * ∏ w ∈ nbrsIn G s v,
        (1 - Tail.rootProb G lam (compIn G (s.erase v) w) w) :=
  Tail.rootProb_odds hG hlam hs hv

theorem message_recursion (hG : G.IsAcyclic) {lam : ℝ} (hlam : 0 < lam)
    {s : Finset V} (hs : ConnectedIn G s) {v : V} (hv : v ∈ s) :
    Tail.rootProb G lam s v = Reserve.msg lam (Reserve.Tmass G lam s v) :=
  Reserve.rootProb_eq_msg hG hlam hs hv

theorem logmass_recursion (hG : G.IsAcyclic) {lam : ℝ} (hlam : 0 < lam)
    {s : Finset V} (hs : ConnectedIn G s) {v : V} (hv : v ∈ s) :
    Reserve.yLog G lam s v = Reserve.lmass lam (Reserve.Tmass G lam s v) :=
  Reserve.yLog_eq_lmass hG hlam hs hv

theorem message_bounds {lam : ℝ} (hlam : 0 < lam) {s : Finset V}
    {v : V} (hv : v ∈ s) :
    0 < Tail.rootProb G lam s v ∧ Tail.rootProb G lam s v ≤ actQ lam :=
  ⟨Tail.rootProb_pos hlam s v, Tail.rootProb_le_actQ hlam.le hv⟩

theorem message_lt_one {lam : ℝ} (hlam : 0 < lam) {s : Finset V}
    {v : V} (hv : v ∈ s) : Tail.rootProb G lam s v < 1 :=
  Tail.rootProb_lt_one hlam.le hv

theorem message_eq_q_iff_no_children {lam : ℝ} (hlam : 0 < lam)
    {s : Finset V} {v : V} (hv : v ∈ s) :
    Tail.rootProb G lam s v = actQ lam ↔ nbrsIn G s v = ∅ := by
  constructor
  · intro heq
    by_contra hne
    exact (Tail.rootProb_lt_actQ hlam hv (Finset.nonempty_iff_ne_empty.mpr hne)).ne heq
  · exact Tail.rootProb_eq_actQ hlam.le hv

theorem children_logmass_nonneg (hG : G.IsAcyclic) {lam : ℝ} (hlam : 0 < lam)
    {s : Finset V} (hs : ConnectedIn G s) {v : V} (hv : v ∈ s) :
    0 ≤ Reserve.Tmass G lam s v :=
  Reserve.Tmass_nonneg hG hlam hs hv

theorem children_logmass_pos (hG : G.IsAcyclic) {lam : ℝ} (hlam : 0 < lam)
    {s : Finset V} (hs : ConnectedIn G s) {v : V} (hv : v ∈ s)
    (hne : (nbrsIn G s v).Nonempty) : 0 < Reserve.Tmass G lam s v :=
  Reserve.Tmass_pos hG hlam hs hv hne

theorem logmass_bounds (hG : G.IsAcyclic) {lam : ℝ} (hlam : 0 < lam)
    {s : Finset V} (hs : ConnectedIn G s) {v : V} (hv : v ∈ s) :
    0 < Reserve.yLog G lam s v ∧
      Reserve.yLog G lam s v ≤ Real.log (1 + lam) := by
  refine ⟨Reserve.yLog_pos hG hlam hs hv, ?_⟩
  rw [logmass_recursion hG hlam hs hv]
  unfold Reserve.lmass
  have hY := children_logmass_nonneg hG hlam hs hv
  have he : Real.exp (-Reserve.Tmass G lam s v) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr hY)
  have hmul := mul_le_mul_of_nonneg_left he hlam.le
  apply Real.log_le_log (by positivity)
  nlinarith

end Erdos993Lean.Analytic.V213.VarianceResponse

#check Erdos993Lean.Analytic.V213.VarianceResponse.message_odds
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.message_odds
#check Erdos993Lean.Analytic.V213.VarianceResponse.message_recursion
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.message_recursion
#check Erdos993Lean.Analytic.V213.VarianceResponse.logmass_recursion
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.logmass_recursion
#check Erdos993Lean.Analytic.V213.VarianceResponse.message_bounds
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.message_bounds
#check Erdos993Lean.Analytic.V213.VarianceResponse.message_lt_one
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.message_lt_one
#check Erdos993Lean.Analytic.V213.VarianceResponse.message_eq_q_iff_no_children
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.message_eq_q_iff_no_children
#check Erdos993Lean.Analytic.V213.VarianceResponse.children_logmass_nonneg
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.children_logmass_nonneg
#check Erdos993Lean.Analytic.V213.VarianceResponse.children_logmass_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.children_logmass_pos
#check Erdos993Lean.Analytic.V213.VarianceResponse.logmass_bounds
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.logmass_bounds
