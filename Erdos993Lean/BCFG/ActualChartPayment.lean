module

public import Erdos993Lean.BCFG.LeafPayment

/-! Actual generated-record consumers of the closed heavy/light scalar margins.
All source, mass, ratio and multiplier choices are discharged. The only chart
premise identifies the actual exp(-Tmass), and the light result includes leaves. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Erdos993Lean.BCFG.Analytic

open Finset Erdos993Lean.Analytic
open Erdos993Lean.Analytic.Tail Erdos993Lean.Analytic.Reserve
open Erdos993Lean.Analytic.V213.VarianceResponse

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Original heavy payment with no free positivity or comparison-choice hypotheses. -/
theorem actual_heavy_payment (hG : G.IsAcyclic) {r : AnalyticRow} {lam v : ℝ}
    (h : HeavyDomain r lam v) {K : Finset V} (hK : ConnectedIn G K)
    {r0 : V} (hr0 : r0 ∈ K) {s : Finset V} {w : V} {rho t : ℝ}
    (hrec : RootRecord G lam K r0 s w rho t)
    (hchart : Real.exp (-Tmass G lam s w) = heavyOmega r lam v) :
    epsilon*rootProb G lam s w <
      responsePayment G lam (price r lam) (alpha r) (beta r) (gamma r lam) 0 s w rho t := by
  have hl := activity_pos h.1
  have hs := rootRecord_connected hG hK hr0 hrec
  have hw := rootRecord_mem hr0 hrec
  have hf := reduction_actual_feasible h.1 hG hK hr0 hrec
  rw [hchart] at hf
  have hp : occupation lam (heavyOmega r lam v) = rootProb G lam s w := by
    rw [← hchart]
    exact reduction_actual_occupation hG hl hs hw
  have hY : logMass (heavyOmega r lam v) = Tmass G lam s w := by
    rw [← hchart]
    exact reduction_actual_logMass lam s w
  have hv : 0 < v := by linarith [h.2.1]
  have homega := heavyOmega_pos (r := r) hl hv
  have hT : 0 < Tmass G lam s w := by
    rw [← hY]
    exact neg_pos.mpr (Real.log_neg homega (heavyOmega_lt_one_onDomain h))
  have hchild : (nbrsIn G s w).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    have hzero : Tmass G lam s w = 0 := by simp [Tmass, he]
    linarith only [hT, hzero]
  have hrho := (rhoZero_bounds hl homega).1.le.trans hf.2.2.2.1
  have hsource := heavy_source_minorant (p := rootProb G lam s w) (rho := rho) hl
  have hpay := one_vertex_payment_lower hG hl (price r lam) (alpha r) (beta r)
    (gamma r lam) rho t (sourceA lam*rootProb G lam s w*rho) (massLine r lam)
    (cubicEnvelope (rootProb G lam s w)) (price_pos (r := r) hl).le
    (row_constants_pos r).2.2.1.le (gamma_pos (r := r) hl).le hrho hs hw hchild
    hsource (reduction_massLine_pos h.1).le (reduction_actual_massLine h.1 hG hs hw)
    (reduction_actual_T0 hG hl hs hw)
  have hpsi := heavy_chart_psi h hf.2.2.2.1 hf.2.2.2.2 (O2.zR G lam s w)
  rw [hp, hY] at hpsi
  have hstrict := mul_lt_mul_of_pos_left hpsi (rootProb_pos (G := G) hl s w)
  calc
    epsilon*rootProb G lam s w = rootProb G lam s w*epsilon := mul_comm _ _
    _ < _ := hstrict
    _ ≤ _ := hpay

/-- Full closed light payment; the leaf case is handled without mass division. -/
theorem actual_light_payment (hG : G.IsAcyclic) {r : AnalyticRow} {lam x : ℝ}
    (h : LightDomain r lam x) {K : Finset V} (hK : ConnectedIn G K)
    {r0 : V} (hr0 : r0 ∈ K) {s : Finset V} {w : V} {rho t : ℝ}
    (hrec : RootRecord G lam K r0 s w rho t)
    (hchart : Real.exp (-Tmass G lam s w) = lightOmega lam x) :
    epsilon*rootProb G lam s w <
      responsePayment G lam (price r lam) (alpha r) (beta r) (gamma r lam) 0 s w rho t := by
  by_cases he : nbrsIn G s w = ∅
  · exact actual_leaf_payment hG h.1 hK hr0 hrec he
  have hchild := Finset.nonempty_iff_ne_empty.mpr he
  have hl := activity_pos h.1
  have hs := rootRecord_connected hG hK hr0 hrec
  have hw := rootRecord_mem hr0 hrec
  have hf := reduction_actual_feasible h.1 hG hK hr0 hrec
  rw [hchart] at hf
  have hp : occupation lam (lightOmega lam x) = rootProb G lam s w := by
    rw [← hchart]
    exact reduction_actual_occupation hG hl hs hw
  have hY : logMass (lightOmega lam x) = Tmass G lam s w := by
    rw [← hchart]
    exact reduction_actual_logMass lam s w
  have homega := lightOmega_pos hl h.2.1 h.2.2
  have hb := lightOmega_bounds hl h.2.1 h.2.2
  have hrho := (rhoZero_bounds hl homega).1.le.trans hf.2.2.2.1
  have hsource := light_source_minorant hl hb.1 hb.2 hf.2.2.2.1 hf.2.2.2.2
  rw [hp] at hsource
  have hH00 := reduction_cavity_ratio_nonneg hl homega hb.2
  rw [hp] at hH00
  have hpay := one_vertex_payment_lower hG hl (price r lam) (alpha r) (beta r)
    (gamma r lam) rho t (lightSourceA lam (lightOmega lam x)*rho+
      lightSourceB lam (lightOmega lam x))
    (messageRatio (O2.cavH lam (rootProb G lam s w)))
    (cubicEnvelope (rootProb G lam s w)) (price_pos (r := r) hl).le
    (row_constants_pos r).2.2.1.le (gamma_pos (r := r) hl).le hrho hs hw hchild
    hsource hH00 le_rfl (reduction_actual_T0 hG hl hs hw)
  have hlog : 0 < logMass (lightOmega lam x) := by
    rw [hY]
    exact Tmass_pos hG hl hs hw hchild
  have hpsi := light_chart_psi h hf.2.2.2.1 hf.2.2.2.2 hlog (O2.zR G lam s w)
  rw [hp, hY] at hpsi
  have hstrict := mul_lt_mul_of_pos_left hpsi (rootProb_pos (G := G) hl s w)
  calc
    epsilon*rootProb G lam s w = rootProb G lam s w*epsilon := mul_comm _ _
    _ < _ := hstrict
    _ ≤ _ := hpay

end Erdos993Lean.BCFG.Analytic

#check Erdos993Lean.BCFG.Analytic.actual_heavy_payment
#print axioms Erdos993Lean.BCFG.Analytic.actual_heavy_payment
#check Erdos993Lean.BCFG.Analytic.actual_light_payment
#print axioms Erdos993Lean.BCFG.Analytic.actual_light_payment

-- Actual original one-vertex and record APIs; not new theorem counts.
#check Erdos993Lean.Analytic.V213.VarianceResponse.one_vertex_payment_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.one_vertex_payment_lower
#check Erdos993Lean.Analytic.V213.VarianceResponse.rootRecord_connected
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.rootRecord_connected
#check Erdos993Lean.Analytic.V213.VarianceResponse.rootRecord_mem
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.rootRecord_mem
#check Erdos993Lean.Analytic.Reserve.Tmass_pos
#print axioms Erdos993Lean.Analytic.Reserve.Tmass_pos
