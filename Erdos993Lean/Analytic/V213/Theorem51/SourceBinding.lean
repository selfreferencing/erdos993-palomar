module

public import Erdos993Lean.Analytic.V213.Theorem51.Coordinates

/-! Bridge 6: the contract's second source branch at the actual forest
coordinates. Physical record bounds give equality with the full source; the
nonnegative weighted transfer is also stated directly. -/
@[expose] public section
noncomputable section

namespace Erdos993Lean.Analytic.V213.Theorem51

open Finset Erdos993Lean.Analytic Tail Reserve O2 VarianceResponse

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

theorem actual_contract_mUp (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    {s : Finset V} (hs : ConnectedIn G s) {v : V} (hv : v ∈ s) (rho : ℝ) :
    mUp lam (rootProb G lam s v) rho =
      max (1-rho) ((1-rootProb G lam s v*rho)*
        F4Unified.childCap lam (Tmass G lam s v)) := by
  simpa only [contract_p_actual hG hl hs hv] using
    (contract_mUp (Y := Tmass G lam s v) (rho := rho) hl)

theorem actual_contract_source_le (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    {s : Finset V} (hs : ConnectedIn G s) {v : V} (hv : v ∈ s) (rho : ℝ) :
    F4Unified.source lam (Tmass G lam s v) rho ≤ src lam (rootProb G lam s v) rho := by
  simpa only [contract_p_actual hG hl hs hv] using
    (contract_source_le (Y := Tmass G lam s v) (rho := rho) hl)

theorem actual_contract_source_eq (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    {K : Finset V} (hK : ConnectedIn G K) {r0 : V} (hr0 : r0 ∈ K)
    {s : Finset V} {v : V} {rho t : ℝ}
    (hrec : RootRecord G lam K r0 s v rho t) :
    F4Unified.source lam (Tmass G lam s v) rho = src lam (rootProb G lam s v) rho := by
  have hs := rootRecord_connected hG hK hr0 hrec
  have hv := rootRecord_mem hr0 hrec
  simpa only [contract_p_actual hG hl hs hv] using
    (contract_source_eq hl (Tmass_nonneg hG hl hs hv)
      (actual_feasible_vacancy hG hl hK hr0 hrec))

/-- The source multiplier in the normalized child payment is nonnegative.
The totalized quotient at a leaf is harmless here; child payments themselves
are used only when the parent has positive total message mass. -/
theorem actual_source_coefficient_nonneg (hG : G.IsAcyclic) {lam price : ℝ}
    (hl : 0 < lam) (hprice : 0 ≤ price)
    {K : Finset V} (hK : ConnectedIn G K) {r0 : V} (hr0 : r0 ∈ K)
    {s : Finset V} {v : V} {rho t : ℝ}
    (hrec : RootRecord G lam K r0 s v rho t) :
    0 ≤ rootProb G lam s v*(price*rho)/Tmass G lam s v := by
  have hs := rootRecord_connected hG hK hr0 hrec
  have hv := rootRecord_mem hr0 hrec
  exact div_nonneg
    (mul_nonneg (rootProb_pos (G := G) hl s v).le
      (mul_nonneg hprice (actual_record_rho_nonneg hG hl hK hr0 hrec)))
    (Tmass_nonneg hG hl hs hv)

/-- Any lower bound using the contract source transfers to the actual source
term. The remainder R is arbitrary, so it may be the actual alpha/P expression. -/
theorem actual_source_payment_transfer (hG : G.IsAcyclic) {lam price : ℝ}
    (hl : 0 < lam) (hprice : 0 ≤ price)
    {K : Finset V} (hK : ConnectedIn G K) {r0 : V} (hr0 : r0 ∈ K)
    {s : Finset V} {v : V} {rho t : ℝ}
    (hrec : RootRecord G lam K r0 s v rho t) (R : ℝ) :
    rootProb G lam s v*(price*rho*F4Unified.source lam (Tmass G lam s v) rho+R)/
        Tmass G lam s v ≤
      rootProb G lam s v*(price*rho*src lam (rootProb G lam s v) rho+R)/
        Tmass G lam s v := by
  have hs := rootRecord_connected hG hK hr0 hrec
  have hv := rootRecord_mem hr0 hrec
  have hsource := actual_contract_source_le hG hl hs hv rho
  have hterm := mul_le_mul_of_nonneg_left hsource
    (mul_nonneg hprice (actual_record_rho_nonneg hG hl hK hr0 hrec))
  have hnum := mul_le_mul_of_nonneg_left (add_le_add hterm (le_refl R))
    (rootProb_pos (G := G) hl s v).le
  exact div_le_div_of_nonneg_right hnum (Tmass_nonneg hG hl hs hv)

end Erdos993Lean.Analytic.V213.Theorem51

#check Erdos993Lean.Analytic.V213.Theorem51.actual_contract_mUp
#print axioms Erdos993Lean.Analytic.V213.Theorem51.actual_contract_mUp
#check Erdos993Lean.Analytic.V213.Theorem51.actual_contract_source_le
#print axioms Erdos993Lean.Analytic.V213.Theorem51.actual_contract_source_le
#check Erdos993Lean.Analytic.V213.Theorem51.actual_contract_source_eq
#print axioms Erdos993Lean.Analytic.V213.Theorem51.actual_contract_source_eq
#check Erdos993Lean.Analytic.V213.Theorem51.actual_source_coefficient_nonneg
#print axioms Erdos993Lean.Analytic.V213.Theorem51.actual_source_coefficient_nonneg
#check Erdos993Lean.Analytic.V213.Theorem51.actual_source_payment_transfer
#print axioms Erdos993Lean.Analytic.V213.Theorem51.actual_source_payment_transfer
