module

public import Erdos993Lean.Analytic.V213.Theorem51.ScalarBinding
public import Erdos993Lean.Analytic.V213.ResponseFeasibleMessages
public import Erdos993Lean.Analytic.V213.ResponseOneVertex

/-! The contract leaf payment is the literal forest payment, including the
nonzero delta multiplier whose reserve contribution vanishes at a leaf. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.Theorem51

open Finset Erdos993Lean.Analytic Tail Reserve O2 VarianceResponse

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

theorem leaf_payment_identity (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    (c a b g d rho t : ℝ) {s : Finset V} (hs : ConnectedIn G s) {v : V} (hv : v ∈ s)
    (hchild : nbrsIn G s v = ∅) :
    responsePayment G lam c a b g d s v rho t =
      rootProb G lam s v * (c*rho*O2.src lam (rootProb G lam s v) rho +
        a*(1-rho)-rho*(1-rootProb G lam s v)-g*messageRatio (rootProb G lam s v)) := by
  have hz := zR_of_nbrsIn_empty hG hl.le hs hv hchild
  have hratio := messageRatio_root_eq (G := G) hl s v
  have hreserve := responseReserve_leaf hG hl g d hs hv hchild
  unfold responsePayment responseSourceMass
  simp only [hchild, Finset.sum_empty, hreserve, hz, mul_one, sub_self,
    mul_zero, add_zero, zero_mul]
  rw [hratio]
  ring

theorem contract_p_zero (lam : ℝ) : F4Unified.p lam 0 = actQ lam := by
  simp only [F4Unified.p, neg_zero, Real.exp_zero, mul_one, actQ]

theorem actual_leaf_feasible (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    {K : Finset V} (hK : ConnectedIn G K) {r0 : V} (hr0 : r0 ∈ K)
    {s : Finset V} {v : V} {rho t : ℝ}
    (hrec : RootRecord G lam K r0 s v rho t) (hchild : nbrsIn G s v = ∅) :
    F4Unified.FeasibleVacancy lam 0 rho := by
  have hf := feasible_message_range_leaf hG hl hK hr0 hrec hchild
  simpa only [F4Unified.FeasibleVacancy, F4Unified.lowerVacancy, contract_p_zero] using hf.2

theorem actual_leaf_payment_eq_contract (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    (r : F4Unified.Row) {K : Finset V} (hK : ConnectedIn G K) {r0 : V} (hr0 : r0 ∈ K)
    {s : Finset V} {v : V} {rho t : ℝ}
    (hrec : RootRecord G lam K r0 s v rho t) (hchild : nbrsIn G s v = ∅) :
    responsePayment G lam ((F4Unified.rowData r).price/(1+lam))
      (F4Unified.alpha r lam) (F4Unified.beta r lam) (F4Unified.gamma r lam)
      (F4Unified.delta r lam) s v rho t =
      F4Unified.q lam * F4Unified.parentN r lam 0 rho := by
  have hs := rootRecord_connected hG hK hr0 hrec
  have hv := rootRecord_mem hr0 hrec
  have hf := feasible_message_range_leaf hG hl hK hr0 hrec hchild
  have hr := actual_leaf_feasible hG hl hK hr0 hrec hchild
  have hsource := contract_source_eq hl (show (0 : ℝ) ≤ 0 from le_rfl) hr
  have hq : 0 < actQ lam := by unfold actQ; positivity
  rw [contract_p_zero] at hsource
  rw [leaf_payment_identity hG hl _ _ _ _ _ _ _ hs hv hchild, hf.1]
  unfold F4Unified.parentN F4Unified.parentP
  rw [contract_p_zero, hsource, messageRatio_of_ne_zero hq.ne', q_eq_actQ]
  ring

theorem actual_leaf_payment_pos {r : F4Unified.Row}
    (hleaf : F4Unified.LeafPositive r) (hG : G.IsAcyclic) {lam : ℝ}
    (hrow : F4Unified.InRow r lam)
    {K : Finset V} (hK : ConnectedIn G K) {r0 : V} (hr0 : r0 ∈ K)
    {s : Finset V} {v : V} {rho t : ℝ}
    (hrec : RootRecord G lam K r0 s v rho t) (hchild : nbrsIn G s v = ∅) :
    0 < responsePayment G lam ((F4Unified.rowData r).price/(1+lam))
      (F4Unified.alpha r lam) (F4Unified.beta r lam) (F4Unified.gamma r lam)
      (F4Unified.delta r lam) s v rho t := by
  have hl := row_activity_pos hrow
  rw [actual_leaf_payment_eq_contract hG hl r hK hr0 hrec hchild]
  exact hleaf lam rho hrow (actual_leaf_feasible hG hl hK hr0 hrec hchild)

end Erdos993Lean.Analytic.V213.Theorem51

#check Erdos993Lean.Analytic.V213.Theorem51.leaf_payment_identity
#print axioms Erdos993Lean.Analytic.V213.Theorem51.leaf_payment_identity
#check Erdos993Lean.Analytic.V213.Theorem51.actual_leaf_payment_eq_contract
#print axioms Erdos993Lean.Analytic.V213.Theorem51.actual_leaf_payment_eq_contract
#check Erdos993Lean.Analytic.V213.Theorem51.actual_leaf_payment_pos
#print axioms Erdos993Lean.Analytic.V213.Theorem51.actual_leaf_payment_pos
