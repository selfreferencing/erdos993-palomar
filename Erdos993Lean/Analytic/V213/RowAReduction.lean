module

public import Erdos993Lean.Analytic.V213.RowADefinitions
public import Erdos993Lean.Analytic.V213.ResponseOneVertex
public import Erdos993Lean.Analytic.V213.ResponseFeasibleMessages

/-! Row A Step 1: the actual rooted message and local payment, not an abstract
model assumed to satisfy the printed recurrence. Only the printed source lower
bound a_f*pi and the proved one-vertex inequality are used. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.RowA

open Finset Tail Reserve O2

noncomputable def fieldSlope (lam : ℝ) : ℝ := (1+2*lam)/(2*lam)

theorem fieldSlope_source_lower {lam : ℝ} (hl : 0 < lam) (p rho : ℝ) :
    fieldSlope lam*(rho*p) ≤ src lam p rho := by
  have hq := q_bounds hl
  have he : fieldSlope lam*(rho*p) = (1+actQ lam)*(p*rho)/(2*actQ lam) := by
    unfold fieldSlope actQ
    field_simp [hl.ne',show 1+lam ≠ 0 by positivity] <;> ring
  rw [he]
  exact (le_max_left _ _).trans (le_max_left _ _)

theorem hq_le_cavity_ratio {lam p : ℝ} (hl : 0 < lam) (hp : 0 < p) (hpq : p ≤ q lam) :
    messageRatio (q lam) ≤ messageRatio (cavH lam p) := by
  have hq := q_bounds hl
  have hp1 : p < 1 := hpq.trans_lt hq.2
  have hd : 0 < lam*(1-p) := mul_pos hl (by linarith)
  have hcross : p*(1+lam) ≤ lam := (le_div_iff₀ (by positivity)).mp hpq
  have hrat : p/(lam*(1-p)) ≤ 1 := (div_le_iff₀ hd).2 (by nlinarith)
  have hc0 : 0 ≤ cavH lam p := le_min hq.1.le (by linarith)
  have hcq : cavH lam p ≤ q lam := min_le_left _ _
  exact messageRatio_antitoneOn ⟨hc0,hcq.trans_lt hq.2⟩ ⟨hq.1.le,hq.2⟩ hcq

theorem oneVertexPsi_eq {lam x r z : ℝ} (hl : 0 < lam) (hx : 0 < x) (hx1 : x < 1) :
    oneVertexPsi (2/(1+lam)) 1 (7/6) (7*lam/20) (q lam*x) (1-r)
      (childMass lam x) z (fieldSlope lam*((1-r)*(q lam*x)))
      (messageRatio (q lam)) (messageRatio (q lam*x)) = psi lam x r z := by
  have hy := childMass_pos hl hx hx1
  have hd : 1+lam ≠ 0 := by positivity
  rw [← eta_eq_messageRatio hl]
  unfold oneVertexPsi psi fieldSlope sigma q
  field_simp [hl.ne',hx.ne',hy.ne',hd] <;> ring

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

theorem normalized_message_nonleaf (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    {s : Finset V} {v : V} (hv : v ∈ s) (hchild : (nbrsIn G s v).Nonempty) :
    0 < rootProb G lam s v/q lam ∧ rootProb G lam s v/q lam < 1 := by
  have hq := q_bounds hl
  exact ⟨div_pos (rootProb_pos hl s v) hq.1,
    (div_lt_iff₀ hq.1).2 (by simpa [q,actQ] using (rootProb_lt_actQ hl hv hchild))⟩

theorem childMass_normalized_message (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    {s : Finset V} (hs : ConnectedIn G s) {v : V} (hv : v ∈ s) :
    childMass lam (rootProb G lam s v/q lam) = Tmass G lam s v := by
  have hp := rootProb_pos (G := G) hl s v
  have hq := q_bounds hl
  rw [children_logmass_inverse hG hl hs hv]
  unfold childMass q
  congr 1
  field_simp [hl.ne',hp.ne',show 1+lam ≠ 0 by positivity] <;> ring

theorem record_complement_bounds (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    {K : Finset V} (hK : ConnectedIn G K) {r0 : V} (hr0 : r0 ∈ K)
    {s : Finset V} {v : V} {rho t : ℝ} (hrec : RootRecord G lam K r0 s v rho t) :
    0 ≤ 1-rho ∧ 1-rho ≤ q lam := by
  have h := feasible_message_range hG hl hK hr0 hrec
  have hp1 := message_lt_one (G := G) hl (rootRecord_mem hr0 hrec)
  have hpcomp : 0 < 1-rootProb G lam s v := sub_pos.mpr hp1
  have hd : 0 < 1+lam*(1-rootProb G lam s v) := by positivity
  have hD : 0 < 1+lam := by positivity
  have hrecip : 1/(1+lam) ≤ 1/(1+lam*(1-rootProb G lam s v)) := by
    apply (div_le_div_iff₀ hD hd).2
    nlinarith [mul_pos hl h.1]
  have he : 1-q lam = 1/(1+lam) := by
    unfold q
    field_simp [hD.ne'] <;> ring
  exact ⟨by linarith [h.2.2.2],by rw [← he] at hrecip; linarith [h.2.2.1]⟩

theorem payment_nonleaf_lower (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    {s : Finset V} (hs : ConnectedIn G s) {v : V} (hv : v ∈ s)
    (hchild : (nbrsIn G s v).Nonempty) (rho t : ℝ) (hrho : 0 ≤ rho) :
    rootProb G lam s v * psi lam (rootProb G lam s v/q lam) (1-rho) (zR G lam s v) ≤
      responsePayment G lam (2/(1+lam)) 1 (7/6) (7*lam/20) 0 s v rho t := by
  have hp := rootProb_pos (G := G) hl s v
  have hq := q_bounds hl
  have hpq : rootProb G lam s v ≤ q lam := rootProb_le_actQ hl.le hv
  have hH00 : 0 ≤ messageRatio (q lam) :=
    (show 0 ≤ 1-q lam by linarith).trans (messageRatio_weak_bounds hq.1.le hq.2).1
  have h := one_vertex_payment_lower hG hl (2/(1+lam)) 1 (7/6) (7*lam/20)
    rho t (fieldSlope lam*(rho*rootProb G lam s v))
    (messageRatio (q lam)) (messageRatio (rootProb G lam s v))
    (by positivity) (by norm_num) (by positivity) hrho hs hv hchild
    (fieldSlope_source_lower hl _ _) hH00 (hq_le_cavity_ratio hl hp hpq) le_rfl
  have hx := normalized_message_nonleaf hG hl hv hchild
  have hi := oneVertexPsi_eq (r := 1-rho) (z := zR G lam s v) hl hx.1 hx.2
  have hcancel : q lam*(rootProb G lam s v/q lam)=rootProb G lam s v := by
    field_simp [hq.1.ne']
  rw [hcancel,sub_sub_cancel,childMass_normalized_message hG hl hs hv] at hi
  rwa [hi] at h

theorem payment_leaf_difference (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    {s : Finset V} (hs : ConnectedIn G s) {v : V} (hv : v ∈ s)
    (hchild : nbrsIn G s v = ∅) (rho t : ℝ) :
    responsePayment G lam (2/(1+lam)) 1 (7/6) (7*lam/20) 0 s v rho t -
      q lam*leafPsi lam (1-rho) =
    (2/(1+lam))*(rho*q lam)*(src lam (q lam) rho-fieldSlope lam*(rho*q lam)) := by
  have hpq : rootProb G lam s v=q lam := (message_eq_q_iff_no_children hl hv).mpr hchild
  have hz := zR_of_nbrsIn_empty hG hl.le hs hv hchild
  have hphi := yLog_pos hG hl hs hv
  have hh := messageRatio_root_eq (G := G) hl s v
  rw [hpq] at hh
  simp only [responsePayment,responseSourceMass,responseReserve,hchild,Finset.sum_empty,
    hz,hpq,mul_one,sub_self,zero_mul,mul_zero,zero_div,add_zero,sub_zero]
  rw [leafPsi,hh]
  unfold sigma fieldSlope q
  field_simp [hl.ne',hphi.ne',show 1+lam ≠ 0 by positivity] <;> ring

theorem payment_leaf_lower (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    {s : Finset V} (hs : ConnectedIn G s) {v : V} (hv : v ∈ s)
    (hchild : nbrsIn G s v = ∅) (rho t : ℝ) (hrho : 0 ≤ rho) :
    q lam*leafPsi lam (1-rho) ≤
      responsePayment G lam (2/(1+lam)) 1 (7/6) (7*lam/20) 0 s v rho t := by
  apply sub_nonneg.mp
  rw [payment_leaf_difference hG hl hs hv hchild rho t]
  have hs0 := sub_nonneg.mpr (fieldSlope_source_lower hl (q lam) rho)
  have hq := (q_bounds hl).1
  positivity

end Erdos993Lean.Analytic.V213.VarianceResponse.RowA

#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.fieldSlope
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.fieldSlope
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.fieldSlope_source_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.fieldSlope_source_lower
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.hq_le_cavity_ratio
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.hq_le_cavity_ratio
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.oneVertexPsi_eq
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.oneVertexPsi_eq
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.normalized_message_nonleaf
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.normalized_message_nonleaf
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.childMass_normalized_message
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.childMass_normalized_message
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.record_complement_bounds
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.record_complement_bounds
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.payment_nonleaf_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.payment_nonleaf_lower
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.payment_leaf_difference
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.payment_leaf_difference
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.payment_leaf_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.payment_leaf_lower

-- Imported API audits.
#check Erdos993Lean.Analytic.Tail.rootProb_pos
#print axioms Erdos993Lean.Analytic.Tail.rootProb_pos
#check Erdos993Lean.Analytic.Tail.rootProb_le_actQ
#print axioms Erdos993Lean.Analytic.Tail.rootProb_le_actQ
#check Erdos993Lean.Analytic.Tail.rootProb_lt_actQ
#print axioms Erdos993Lean.Analytic.Tail.rootProb_lt_actQ
#check Erdos993Lean.Analytic.O2.zR_of_nbrsIn_empty
#print axioms Erdos993Lean.Analytic.O2.zR_of_nbrsIn_empty
#check Erdos993Lean.Analytic.Reserve.yLog_pos
#print axioms Erdos993Lean.Analytic.Reserve.yLog_pos
