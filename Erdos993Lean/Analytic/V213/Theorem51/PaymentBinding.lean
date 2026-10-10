module

public import Erdos993Lean.Analytic.V213.Theorem51.SourceBinding

/-! Bridge 9: exact identification of the contract payment with the actual
normalized child payment, including the totalized zero-J leaf case. -/
@[expose] public section
noncomputable section

namespace Erdos993Lean.Analytic.V213.Theorem51

open Finset Erdos993Lean.Analytic Tail Reserve O2 VarianceResponse

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

theorem contract_parentP_actual (hG : G.IsAcyclic) {r : F4Unified.Row}
    {lam : ℝ} (hl : 0 < lam) {s : Finset V} (hs : ConnectedIn G s)
    {v : V} (hv : v ∈ s) (rho : ℝ) :
    F4Unified.parentP r lam (Tmass G lam s v) rho =
      responseParentP G lam (F4Unified.gamma r lam) s v rho := by
  simp only [F4Unified.parentP, contract_p_actual hG hl hs hv,
    responseParentP, responseH, yLog]
  ring

/-- The contract's conditional reserve is exactly the actual totalized quotient.
For a zero-J child both expressions vanish; no division by a positive J is used. -/
theorem contract_reserve_actual (hG : G.IsAcyclic) {r : F4Unified.Row}
    {lam : ℝ} (hl : 0 < lam) {s : Finset V} (hs : ConnectedIn G s)
    {v : V} (hv : v ∈ s) :
    F4Unified.reserve r lam (rootProb G lam s v) (responseY G lam s v) =
      F4Unified.delta r lam * (responseH G lam s v - responseY G lam s v)^2 /
        responseJ G lam s v := by
  rcases actual_admissible hG hl hs hv with hJ | ⟨hJ, _⟩
  · rw [F4Unified.reserve, if_pos hJ]
    rw [contract_childH_actual hl, contract_childJ_actual hG hl hs hv]
  · have hzero : responseJ G lam s v = 0 :=
      (contract_childJ_actual hG hl hs hv).symm.trans hJ
    simp only [F4Unified.reserve, if_neg (not_lt_of_ge hJ.le), hzero, div_zero]

/-- The source is equal, rather than merely bounded, on an actual feasible
record. Every remaining term is a literal scalar coordinate identification. -/
theorem contract_payment_actual (hG : G.IsAcyclic) {r : F4Unified.Row}
    {lam : ℝ} (hl : 0 < lam) {K : Finset V} (hK : ConnectedIn G K)
    {r0 : V} (hr0 : r0 ∈ K) {s : Finset V} {v : V} {rho t : ℝ}
    (hrec : RootRecord G lam K r0 s v rho t) {w : V}
    (hw : w ∈ nbrsIn G s v) :
    F4Unified.payment r lam (Tmass G lam s v) rho
        (rootProb G lam (compIn G (s.erase v) w) w)
        (responseY G lam (compIn G (s.erase v) w) w) =
      responseChildPayment G lam ((F4Unified.rowData r).price / (1 + lam))
        (F4Unified.alpha r lam) (F4Unified.beta r lam) (F4Unified.gamma r lam)
        (F4Unified.delta r lam) s v rho w := by
  have hs := rootRecord_connected hG hK hr0 hrec
  have hv := rootRecord_mem hr0 hrec
  have hcs := (compIn_branch hG hs hv hw).1
  have hcv := self_mem_branch hw
  have hreserve := contract_reserve_actual (r := r) hG hl hcs hcv
  simp only [F4Unified.payment, F4Unified.parentN,
    contract_p_actual hG hl hs hv, actual_contract_source_eq hG hl hK hr0 hrec,
    contract_parentP_actual hG hl hs hv, contract_childH_actual hl,
    hreserve, responseChildPayment]
  ring

/-- The same payment identity with the established parent-row coefficient API. -/
theorem contract_payment_actual_parentRows (hG : G.IsAcyclic) {r : F4Unified.Row}
    {lam : ℝ} (hl : 0 < lam) {K : Finset V} (hK : ConnectedIn G K)
    {r0 : V} (hr0 : r0 ∈ K) {s : Finset V} {v : V} {rho t : ℝ}
    (hrec : RootRecord G lam K r0 s v rho t) {w : V}
    (hw : w ∈ nbrsIn G s v) :
    F4Unified.payment r lam (Tmass G lam s v) rho
        (rootProb G lam (compIn G (s.erase v) w) w)
        (responseY G lam (compIn G (s.erase v) w) w) =
      responseChildPayment G lam (ParentRows.price (parentRowIndex r) lam)
        (ParentRows.alpha (parentRowIndex r) lam)
        (ParentRows.beta (parentRowIndex r) lam)
        (ParentRows.gamma (parentRowIndex r) lam)
        (ParentRows.delta (parentRowIndex r) lam) s v rho w := by
  simpa only [price_eq r lam, ← alpha_eq r lam, ← beta_eq r lam,
    ← gamma_eq r lam, ← delta_eq r lam] using
      (contract_payment_actual (r := r) hG hl hK hr0 hrec hw)

/-- Pair positivity applies to every actual child, with all contract domain
conditions discharged from the actual rooted forest record. -/
theorem actual_child_payment_pos {r : F4Unified.Row} (hpair : F4Unified.PairPositive r)
    {lam : ℝ} (hrow : F4Unified.InRow r lam) (hG : G.IsAcyclic)
    {K : Finset V} (hK : ConnectedIn G K) {r0 : V} (hr0 : r0 ∈ K)
    {s : Finset V} {v : V} {rho t : ℝ}
    (hrec : RootRecord G lam K r0 s v rho t) {w : V}
    (hw : w ∈ nbrsIn G s v) :
    0 < responseChildPayment G lam (ParentRows.price (parentRowIndex r) lam)
      (ParentRows.alpha (parentRowIndex r) lam)
      (ParentRows.beta (parentRowIndex r) lam)
      (ParentRows.gamma (parentRowIndex r) lam)
      (ParentRows.delta (parentRowIndex r) lam) s v rho w := by
  have hd := actual_child_pairDomain hrow hG hK hr0 hrec hw
  have hp := hpair _ _ _ _ _ hd
  simpa only [contract_payment_actual_parentRows hG (row_activity_pos hrow)
    hK hr0 hrec hw] using hp

theorem actual_child_payment_nonneg {r : F4Unified.Row}
    (hpair : F4Unified.PairPositive r) {lam : ℝ} (hrow : F4Unified.InRow r lam)
    (hG : G.IsAcyclic) {K : Finset V} (hK : ConnectedIn G K)
    {r0 : V} (hr0 : r0 ∈ K) {s : Finset V} {v : V} {rho t : ℝ}
    (hrec : RootRecord G lam K r0 s v rho t) {w : V}
    (hw : w ∈ nbrsIn G s v) :
    0 ≤ responseChildPayment G lam (ParentRows.price (parentRowIndex r) lam)
      (ParentRows.alpha (parentRowIndex r) lam)
      (ParentRows.beta (parentRowIndex r) lam)
      (ParentRows.gamma (parentRowIndex r) lam)
      (ParentRows.delta (parentRowIndex r) lam) s v rho w :=
  (actual_child_payment_pos hpair hrow hG hK hr0 hrec hw).le

end Erdos993Lean.Analytic.V213.Theorem51

#check Erdos993Lean.Analytic.V213.Theorem51.contract_parentP_actual
#print axioms Erdos993Lean.Analytic.V213.Theorem51.contract_parentP_actual
#check Erdos993Lean.Analytic.V213.Theorem51.contract_reserve_actual
#print axioms Erdos993Lean.Analytic.V213.Theorem51.contract_reserve_actual
#check Erdos993Lean.Analytic.V213.Theorem51.contract_payment_actual
#print axioms Erdos993Lean.Analytic.V213.Theorem51.contract_payment_actual
#check Erdos993Lean.Analytic.V213.Theorem51.contract_payment_actual_parentRows
#print axioms Erdos993Lean.Analytic.V213.Theorem51.contract_payment_actual_parentRows
#check Erdos993Lean.Analytic.V213.Theorem51.actual_child_payment_pos
#print axioms Erdos993Lean.Analytic.V213.Theorem51.actual_child_payment_pos
#check Erdos993Lean.Analytic.V213.Theorem51.actual_child_payment_nonneg
#print axioms Erdos993Lean.Analytic.V213.Theorem51.actual_child_payment_nonneg
