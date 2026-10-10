module

public import Erdos993Lean.BCFG.ActualChartPayment
public import Erdos993Lean.BCFG.ActualTailPayment
public import Erdos993Lean.BCFG.ChartCoverage

/-! Complete-row consumers of the original closed charts and literal tails.
The imported chart consumers discharge the local payment obligations. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Erdos993Lean.BCFG.Analytic

open Finset Erdos993Lean.Analytic
open Erdos993Lean.Analytic.Tail Erdos993Lean.Analytic.Reserve
open Erdos993Lean.Analytic.V213.VarianceResponse

theorem tailCutoff_eq_power (r : AnalyticRow) :
    tailCutoff r = (1/2 : ℝ)^(heavyExponent r) := by
  cases r <;> norm_num [tailCutoff,heavyExponent]

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Printed Theorem 5.14, including actual roots and empty-child leaves. -/
theorem actual_bcfg_payment_margin (hG : G.IsAcyclic)
    {r : AnalyticRow} {lam : ℝ} (hrow : InRow r lam)
    {K : Finset V} (hK : ConnectedIn G K) {r0 : V} (hr0 : r0 ∈ K)
    {s : Finset V} {w : V} {rho t : ℝ}
    (hrec : RootRecord G lam K r0 s w rho t) :
    epsilon*rootProb G lam s w <
      responsePayment G lam (price r lam) (alpha r) (beta r) (gamma r lam) 0 s w rho t := by
  have hf := reduction_actual_feasible hrow hG hK hr0 hrec
  rcases chart_or_tail_coverage hrow hf.2.1 hf.2.2.1 with hlight | htail | hheavy
  · obtain ⟨x,hd,hx⟩ := hlight
    exact actual_light_payment hG hd hK hr0 hrec hx.symm
  · apply actual_tail_payment_margin hrow hG hK hr0 hrec
    rwa [tailCutoff_eq_power]
  · obtain ⟨v,hd,hv⟩ := hheavy
    exact actual_heavy_payment hG hd hK hr0 hrec hv.symm

/-- The same strict printed margin in the proposition's p/10000 notation. -/
theorem actual_bcfg_payment_strict (hG : G.IsAcyclic)
    {r : AnalyticRow} {lam : ℝ} (hrow : InRow r lam)
    {K : Finset V} (hK : ConnectedIn G K) {r0 : V} (hr0 : r0 ∈ K)
    {s : Finset V} {w : V} {rho t : ℝ}
    (hrec : RootRecord G lam K r0 s w rho t) :
    rootProb G lam s w/10000 <
      responsePayment G lam (price r lam) (alpha r) (beta r) (gamma r lam) 0 s w rho t := by
  simpa only [epsilon,div_eq_mul_inv,one_mul,mul_comm] using
    actual_bcfg_payment_margin hG hrow hK hr0 hrec

/-- Printed Proposition 5.13 on every actual descendant, with its printed margin. -/
theorem actual_bcfg_payment_proposition (hG : G.IsAcyclic)
    {r : AnalyticRow} {lam : ℝ} (hrow : InRow r lam)
    {K : Finset V} (hK : ConnectedIn G K) {r0 : V} (hr0 : r0 ∈ K)
    {s : Finset V} {w : V} {rho t : ℝ}
    (hrec : RootRecord G lam K r0 s w rho t) :
    rootProb G lam s w/10000 ≤
      responsePayment G lam (price r lam) (alpha r) (beta r) (gamma r lam) 0 s w rho t :=
  (actual_bcfg_payment_strict hG hrow hK hr0 hrec).le

theorem actual_bcfg_payment_nonneg (hG : G.IsAcyclic)
    {r : AnalyticRow} {lam : ℝ} (hrow : InRow r lam)
    {K : Finset V} (hK : ConnectedIn G K) {r0 : V} (hr0 : r0 ∈ K)
    {s : Finset V} {w : V} {rho t : ℝ}
    (hrec : RootRecord G lam K r0 s w rho t) :
    0 ≤ responsePayment G lam (price r lam) (alpha r) (beta r) (gamma r lam) 0 s w rho t := by
  have hp : 0 < rootProb G lam s w/10000 :=
    div_pos (rootProb_pos (G := G) (activity_pos hrow) s w) (by norm_num)
  exact (hp.trans (actual_bcfg_payment_strict hG hrow hK hr0 hrec)).le

end Erdos993Lean.BCFG.Analytic

#check Erdos993Lean.BCFG.Analytic.tailCutoff_eq_power
#print axioms Erdos993Lean.BCFG.Analytic.tailCutoff_eq_power
#check Erdos993Lean.BCFG.Analytic.actual_bcfg_payment_margin
#print axioms Erdos993Lean.BCFG.Analytic.actual_bcfg_payment_margin
#check Erdos993Lean.BCFG.Analytic.actual_bcfg_payment_strict
#print axioms Erdos993Lean.BCFG.Analytic.actual_bcfg_payment_strict
#check Erdos993Lean.BCFG.Analytic.actual_bcfg_payment_proposition
#print axioms Erdos993Lean.BCFG.Analytic.actual_bcfg_payment_proposition
#check Erdos993Lean.BCFG.Analytic.actual_bcfg_payment_nonneg
#print axioms Erdos993Lean.BCFG.Analytic.actual_bcfg_payment_nonneg
