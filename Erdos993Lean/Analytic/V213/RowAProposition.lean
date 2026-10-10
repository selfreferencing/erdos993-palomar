module

public import Erdos993Lean.Analytic.V213.RowAQuadratics
public import Erdos993Lean.Analytic.V213.RowAEndpointBounds
public import Erdos993Lean.Analytic.V213.RowAInterpolation
public import Erdos993Lean.Analytic.V213.RowAReduction

/-!
Current Proposition 5.12, T. Zhang's Row A: strict local-payment positivity on
the closed activity interval [1/3,3/5]. The finite input is a proved theorem
from RowAQuadratics, not a positivity assumption in the proposition. The leaf
case uses the separate assigned formula and never divides by its zero Y.



-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.RowA

open Finset Tail Reserve O2

theorem endpointMinus_pos {x r z : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 3/8) :
    0 < endpointPsi (1/3) (343/400) (15/16) x r z :=
  (quadMinus_pos hx.le hx1 hr0 hr1).trans_le (quadMinus_le_endpoint hx hx1 hr1)

theorem endpointPlus_pos {x r z : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 3/8) :
    0 < endpointPsi (3/5) (319/400) (55/64) x r z :=
  (quadPlus_pos hx.le hx1 hr0 hr1).trans_le (quadPlus_le_endpoint hx hx1 hr1)

/-- Every signed response is covered; only the normalized nonleaf message is restricted. -/
theorem psi_pos {lam x r z : ℝ} (hl : 1/3 ≤ lam) (hu : lam ≤ 3/5)
    (hx : 0 < x) (hx1 : x < 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 3/8) :
    0 < psi lam x r z :=
  psi_pos_of_endpoint_pos hl hu hx hx1 hr1
    (endpointMinus_pos hx hx1 hr0 hr1) (endpointPlus_pos hx hx1 hr0 hr1)

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Literal Proposition 5.12 on each actual generated descendant of a component. -/
theorem rowA_payment_pos (hG : G.IsAcyclic) {lam : ℝ}
    (hl : (1:ℝ)/3 ≤ lam) (hu : lam ≤ 3/5)
    {K : Finset V} (hK : ConnectedIn G K)
    (hKc : ∀ x ∈ K, ∀ y, G.Adj x y → y ∈ K) {r0 : V} (hr0 : r0 ∈ K)
    {s : Finset V} {v : V} {rho t : ℝ} (hrec : RootRecord G lam K r0 s v rho t) :
    0 < responsePayment G lam (2/(1+lam)) 1 (7/6) (7*lam/20) 0 s v rho t := by
  have hl0 : 0 < lam := by linarith
  have hs := rootRecord_connected hG hK hr0 hrec
  have hv := rootRecord_mem hr0 hrec
  have hr := record_complement_bounds hG hl0 hK hr0 hrec
  have hr1 : 1-rho ≤ 3/8 := hr.2.trans (row_q_bounds hl hu).2
  have hrho : 0 ≤ rho := (rootRecord_rho_bounds hG hl0 hKc hr0 hrec).1
  by_cases hchild : nbrsIn G s v = ∅
  · exact (mul_pos (q_bounds hl0).1 (leafPsi_pos hl hu hr1)).trans_le
      (payment_leaf_lower hG hl0 hs hv hchild rho t hrho)
  · have hne : (nbrsIn G s v).Nonempty := Finset.nonempty_iff_ne_empty.mpr hchild
    have hx := normalized_message_nonleaf hG hl0 hv hne
    have hpsi := psi_pos (z := zR G lam s v) hl hu hx.1 hx.2 hr.1 hr1
    exact (mul_pos (rootProb_pos hl0 s v) hpsi).trans_le
      (payment_nonleaf_lower hG hl0 hs hv hne rho t hrho)

/-- The component root, including a one-vertex component, is covered without a separate premise. -/
theorem rowA_root_payment_pos (hG : G.IsAcyclic) {lam : ℝ}
    (hl : (1:ℝ)/3 ≤ lam) (hu : lam ≤ 3/5)
    {K : Finset V} (hK : ConnectedIn G K)
    (hKc : ∀ x ∈ K, ∀ y, G.Adj x y → y ∈ K) {r0 : V} (hr0 : r0 ∈ K) :
    0 < responsePayment G lam (2/(1+lam)) 1 (7/6) (7*lam/20) 0 K r0 1 0 :=
  rowA_payment_pos hG hl hu hK hKc hr0 RootRecord.top

/-- Every vertex in the chosen component occurs in the proved strict-payment statement. -/
theorem rowA_each_vertex_payment_pos (hG : G.IsAcyclic) {lam : ℝ}
    (hl : (1:ℝ)/3 ≤ lam) (hu : lam ≤ 3/5)
    {K : Finset V} (hK : ConnectedIn G K)
    (hKc : ∀ x ∈ K, ∀ y, G.Adj x y → y ∈ K) {r0 : V} (hr0 : r0 ∈ K)
    {v : V} (hv : v ∈ K) :
    ∃ s rho t, RootRecord G lam K r0 s v rho t ∧
      0 < responsePayment G lam (2/(1+lam)) 1 (7/6) (7*lam/20) 0 s v rho t := by
  obtain ⟨s,rho,t,hrec⟩ := rootRecord_covers_component (lam := lam) hG hK hr0 hv
  exact ⟨s,rho,t,hrec,rowA_payment_pos hG hl hu hK hKc hr0 hrec⟩

end Erdos993Lean.Analytic.V213.VarianceResponse.RowA

#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.endpointMinus_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.endpointMinus_pos
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.endpointPlus_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.endpointPlus_pos
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.psi_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.psi_pos
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.rowA_payment_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.rowA_payment_pos
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.rowA_root_payment_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.rowA_root_payment_pos
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.rowA_each_vertex_payment_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.rowA_each_vertex_payment_pos
