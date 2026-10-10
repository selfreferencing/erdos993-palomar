module

public import Erdos993Lean.BCFG.ChartPaymentMargins

/-! The original response payment at a parent leaf, without division by Y.
Its source and cubic ratio comparisons are the same literal choices as on the
closed light chart; its determinant is evaluated at the regular x=0 endpoint. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Erdos993Lean.BCFG.Analytic

open Finset Erdos993Lean.Analytic
open Erdos993Lean.Analytic.Tail Erdos993Lean.Analytic.Reserve
open Erdos993Lean.Analytic.V213.VarianceResponse

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Literal original leaf payment, with all coefficients still arbitrary. -/
theorem leaf_payment_identity (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    (c a b g rho t : ℝ) {s : Finset V} (hs : ConnectedIn G s) {w : V} (hw : w ∈ s)
    (hchild : nbrsIn G s w = ∅) :
    responsePayment G lam c a b g 0 s w rho t =
      rootProb G lam s w*(c*rho*O2.src lam (rootProb G lam s w) rho+
        a*(1-rho)-rho*(1-rootProb G lam s w)-g*messageRatio (rootProb G lam s w)) := by
  have hz := O2.zR_of_nbrsIn_empty hG hl.le hs hw hchild
  have hratio := messageRatio_root_eq (G := G) hl s w
  have hreserve := responseReserve_leaf hG hl g 0 hs hw hchild
  unfold responsePayment responseSourceMass
  simp only [hchild, Finset.sum_empty, hreserve, hz, mul_one, sub_self,
    mul_zero, add_zero, zero_mul]
  rw [hratio]
  ring

/-- A leaf needs only source and ratio comparisons, not a mass denominator. -/
theorem leaf_payment_lower (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    (c a b g rho t f0 T0 : ℝ) (hc : 0 ≤ c) (hg : 0 ≤ g) (hrho : 0 ≤ rho)
    {s : Finset V} (hs : ConnectedIn G s) {w : V} (hw : w ∈ s)
    (hchild : nbrsIn G s w = ∅)
    (hf0 : f0 ≤ O2.src lam (rootProb G lam s w) rho)
    (hT0 : messageRatio (rootProb G lam s w) ≤ T0) :
    rootProb G lam s w*(c*rho*f0+a*(1-rho)-rho*(1-rootProb G lam s w)-g*T0) ≤
      responsePayment G lam c a b g 0 s w rho t := by
  rw [leaf_payment_identity hG hl c a b g rho t hs hw hchild]
  apply mul_le_mul_of_nonneg_left _ (rootProb_pos hl s w).le
  have hf := mul_le_mul_of_nonneg_left hf0 (mul_nonneg hc hrho)
  have ht := mul_le_mul_of_nonneg_left hT0 hg
  linarith only [hf, ht]

/-- Actual leaf margin for every original row and generated root record. -/
theorem actual_leaf_payment (hG : G.IsAcyclic) {r : AnalyticRow} {lam : ℝ}
    (hrow : InRow r lam) {K : Finset V} (hK : ConnectedIn G K)
    {r0 : V} (hr0 : r0 ∈ K) {s : Finset V} {w : V} {rho t : ℝ}
    (hrec : RootRecord G lam K r0 s w rho t) (hchild : nbrsIn G s w = ∅) :
    epsilon*rootProb G lam s w <
      responsePayment G lam (price r lam) (alpha r) (beta r) (gamma r lam) 0 s w rho t := by
  have hl := activity_pos hrow
  have hs := rootRecord_connected hG hK hr0 hrec
  have hw := rootRecord_mem hr0 hrec
  have he : Real.exp (-Tmass G lam s w) = 1 := by simp [Tmass, hchild]
  have hf := reduction_actual_feasible hrow hG hK hr0 hrec
  rw [he] at hf
  have hp : occupation lam 1 = rootProb G lam s w := by
    rw [← he]
    exact reduction_actual_occupation hG hl hs hw
  have hb := lightOmega_bounds hl (show (0 : ℝ) ≤ 0 from le_rfl) zero_le_one
  rw [(light_log_zero lam).1] at hb
  have hsource := light_source_minorant hl hb.1 hb.2 hf.2.2.2.1 hf.2.2.2.2
  rw [hp] at hsource
  have hrho := (rhoZero_bounds hl (show (0 : ℝ) < 1 from zero_lt_one)).1.le.trans
    hf.2.2.2.1
  have hlower := leaf_payment_lower hG hl (price r lam) (alpha r) (beta r)
    (gamma r lam) rho t (lightSourceA lam 1*rho+lightSourceB lam 1)
    (cubicEnvelope (rootProb G lam s w)) (price_pos (r := r) hl).le
    (gamma_pos (r := r) hl).le hrho hs hw hchild hsource
    (reduction_actual_T0 hG hl hs hw)
  have hm := light_leaf_scalar hrow hf.2.2.2.1 hf.2.2.2.2
  have hid : lightK r lam 0 rho-tailP r lam 1 rho =
      price r lam*rho*(lightSourceA lam 1*rho+lightSourceB lam 1)+
        alpha r*(1-rho)-rho*(1-rootProb G lam s w)-
          gamma r lam*cubicEnvelope (rootProb G lam s w) := by
    simp only [lightK, (light_log_zero lam).1, tailP, eCoeff, dCoeff, hp]
    ring
  rw [hid] at hm
  calc
    epsilon*rootProb G lam s w = rootProb G lam s w*epsilon := mul_comm _ _
    _ < rootProb G lam s w*
        (price r lam*rho*(lightSourceA lam 1*rho+lightSourceB lam 1)+
          alpha r*(1-rho)-rho*(1-rootProb G lam s w)-
            gamma r lam*cubicEnvelope (rootProb G lam s w)) :=
      mul_lt_mul_of_pos_left hm (rootProb_pos hl s w)
    _ ≤ _ := hlower

end Erdos993Lean.BCFG.Analytic

#check Erdos993Lean.BCFG.Analytic.leaf_payment_identity
#print axioms Erdos993Lean.BCFG.Analytic.leaf_payment_identity
#check Erdos993Lean.BCFG.Analytic.leaf_payment_lower
#print axioms Erdos993Lean.BCFG.Analytic.leaf_payment_lower
#check Erdos993Lean.BCFG.Analytic.actual_leaf_payment
#print axioms Erdos993Lean.BCFG.Analytic.actual_leaf_payment

-- Original leaf conventions and literal reserve, not the older row leaf certificate.
#check Erdos993Lean.Analytic.V213.VarianceResponse.responsePayment
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.responsePayment
#check Erdos993Lean.Analytic.V213.VarianceResponse.responseReserve_leaf
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.responseReserve_leaf
#check Erdos993Lean.Analytic.V213.VarianceResponse.messageRatio_root_eq
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.messageRatio_root_eq
#check Erdos993Lean.Analytic.O2.zR_of_nbrsIn_empty
#print axioms Erdos993Lean.Analytic.O2.zR_of_nbrsIn_empty
