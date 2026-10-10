module

public import Erdos993Lean.Analytic.V213.ResponsePayment
public import Erdos993Lean.Analytic.V213.ResponseRatioIntegral

/-!
Current Lemma 5.11 (f4:lem3.1): the exact four-term payment difference and its
nonnegativity.  This is a one-vertex identity, not a matrix certificate.  The
actual child sum uses signed responses and strictly positive log-masses.  The
printed comparison choices f0,H0,T0 and all multiplier signs are explicit.

-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse

open Finset Erdos993Lean.Analytic.Tail Erdos993Lean.Analytic.Reserve
open Erdos993Lean.Analytic.O2

/-- The literal P,eta,K,t0 quadratic from Lemma 5.11, with their printed definitions. -/
noncomputable def oneVertexPsi (price alpha beta gamma p rho Y z f0 H0 T0 : ℝ) : ℝ :=
  let P := rho*(1-p)+gamma*T0
  let eta := gamma/(p*Y)
  let K := price*rho*f0+alpha*(1-rho)+beta*rho*H0*Y
  let t0 := (alpha+beta)/2
  K-P+2*(P-t0)*(1-z)+(eta-P)*(1-z)^2

/-- The displayed difference is a rational identity before any sign estimate. -/
theorem one_vertex_difference_algebra (price alpha beta gamma p rho Y z phi g f0 H0 T0 S E : ℝ)
    (hp : p ≠ 0) (hY : Y ≠ 0) (hphi : phi ≠ 0) :
    (price*(rho*p)*g-(rho*p)*(1-p)*z^2+alpha*(p*z-rho*p)+
      beta*(p*(z-1)+(rho*p)*S)+gamma*E-gamma*(p*z)^2/phi) -
      p*oneVertexPsi price alpha beta gamma p rho Y z f0 H0 T0 =
    price*(rho*p)*(g-f0)+beta*(rho*p)*(S-H0*Y)+
      gamma*(E-(1-z)^2/Y)+gamma*p*z^2*(T0-p/phi) := by
  unfold oneVertexPsi
  field_simp [hp,hY,hphi]
  ring

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The assigned zero endpoint of h is irrelevant at an actual positive message. -/
theorem messageRatio_root_eq {lam : ℝ} (hl : 0 < lam) (s : Finset V) (v : V) :
    messageRatio (rootProb G lam s v) = rootProb G lam s v / yLog G lam s v := by
  rw [messageRatio_of_ne_zero (rootProb_pos hl s v).ne']
  rfl

/-- Every child's h is at least h(H_c(parent)). -/
theorem child_messageRatio_lower (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    {s : Finset V} (hs : ConnectedIn G s) {v : V} (hv : v ∈ s) {w : V}
    (hw : w ∈ nbrsIn G s v) :
    messageRatio (cavH lam (rootProb G lam s v)) ≤
      messageRatio (rootProb G lam (compIn G (s.erase v) w) w) := by
  have hp0 := rootProb_pos (G := G) hl (compIn G (s.erase v) w) w
  have hp1 := rootProb_lt_one (G := G) hl.le (self_mem_branch hw)
  have hb := child_le_cavH hG hl hs hv hw
  have hcap0 : 0 ≤ cavH lam (rootProb G lam s v) := hp0.le.trans hb
  have hcap1 : cavH lam (rootProb G lam s v) < 1 :=
    (min_le_left _ _).trans_lt (actQ_lt_one' hl)
  exact messageRatio_antitoneOn ⟨hp0.le,hp1⟩ ⟨hcap0,hcap1⟩ hb

/-- The printed H0 choice gives the actual child probability sum bound. -/
theorem children_message_sum_lower (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    {s : Finset V} (hs : ConnectedIn G s) {v : V} (hv : v ∈ s) {H0 : ℝ}
    (hH0 : H0 ≤ messageRatio (cavH lam (rootProb G lam s v))) :
    H0*Tmass G lam s v ≤ ∑ w ∈ nbrsIn G s v,
      rootProb G lam (compIn G (s.erase v) w) w := by
  unfold Tmass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro w hw
  have hphi := yLog_pos hG hl (compIn_branch hG hs hv hw).1 (self_mem_branch hw)
  have hm := mul_le_mul_of_nonneg_right
    (hH0.trans (child_messageRatio_lower hG hl hs hv hw)) hphi.le
  rw [messageRatio_root_eq hl, div_mul_cancel₀ _ hphi.ne'] at hm
  exact hm

/-- Weighted Cauchy--Schwarz permits signed child responses; no sign is lost. -/
theorem children_response_energy (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    {s : Finset V} (hs : ConnectedIn G s) {v : V} (hv : v ∈ s) :
    (1-zR G lam s v)^2/Tmass G lam s v ≤
      ∑ w ∈ nbrsIn G s v,
        (rootProb G lam (compIn G (s.erase v) w) w *
          zR G lam (compIn G (s.erase v) w) w)^2 /
            yLog G lam (compIn G (s.erase v) w) w := by
  have hz : 1-zR G lam s v = ∑ w ∈ nbrsIn G s v,
      rootProb G lam (compIn G (s.erase v) w) w *
        zR G lam (compIn G (s.erase v) w) w := by
    linarith [zR_rec hG hl.le hs hv]
  rw [hz,Tmass]
  exact Finset.sq_sum_div_le_sum_sq_div _ _
    (fun w hw => yLog_pos hG hl (compIn_branch hG hs hv hw).1 (self_mem_branch hw))

/-- The exact four displayed terms at an actual vertex with a child. -/
theorem one_vertex_difference (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    (price alpha beta gamma rho t f0 H0 T0 : ℝ)
    {s : Finset V} (hs : ConnectedIn G s) {v : V} (hv : v ∈ s)
    (hchild : (nbrsIn G s v).Nonempty) :
    responsePayment G lam price alpha beta gamma 0 s v rho t -
      rootProb G lam s v * oneVertexPsi price alpha beta gamma
        (rootProb G lam s v) rho (Tmass G lam s v) (zR G lam s v) f0 H0 T0 =
    price*(rho*rootProb G lam s v)*(src lam (rootProb G lam s v) rho-f0) +
    beta*(rho*rootProb G lam s v)*
      ((∑ w ∈ nbrsIn G s v, rootProb G lam (compIn G (s.erase v) w) w)-H0*Tmass G lam s v) +
    gamma*((∑ w ∈ nbrsIn G s v,
      (rootProb G lam (compIn G (s.erase v) w) w*zR G lam (compIn G (s.erase v) w) w)^2 /
        yLog G lam (compIn G (s.erase v) w) w) - (1-zR G lam s v)^2/Tmass G lam s v) +
    gamma*rootProb G lam s v*zR G lam s v^2*(T0-messageRatio (rootProb G lam s v)) := by
  have h := one_vertex_difference_algebra price alpha beta gamma (rootProb G lam s v)
    rho (Tmass G lam s v) (zR G lam s v) (yLog G lam s v)
    (src lam (rootProb G lam s v) rho) f0 H0 T0
    (∑ w ∈ nbrsIn G s v, rootProb G lam (compIn G (s.erase v) w) w)
    (∑ w ∈ nbrsIn G s v,
      (rootProb G lam (compIn G (s.erase v) w) w*zR G lam (compIn G (s.erase v) w) w)^2 /
        yLog G lam (compIn G (s.erase v) w) w)
    (rootProb_pos hl s v).ne' (Tmass_pos hG hl hs hv hchild).ne'
    (yLog_pos hG hl hs hv).ne'
  simpa only [responsePayment,responseSourceMass,responseReserve,zero_mul,zero_div,add_zero,
    mul_div_assoc,mul_assoc,Finset.mul_sum,messageRatio_root_eq hl] using h

/-- Nonnegativity of all four terms, retaining every printed bound on the choices. -/
theorem one_vertex_payment_lower (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    (price alpha beta gamma rho t f0 H0 T0 : ℝ)
    (hprice : 0 ≤ price) (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma) (hrho : 0 ≤ rho)
    {s : Finset V} (hs : ConnectedIn G s) {v : V} (hv : v ∈ s)
    (hchild : (nbrsIn G s v).Nonempty)
    (hf0 : f0 ≤ src lam (rootProb G lam s v) rho)
    (hH00 : 0 ≤ H0) (hH0 : H0 ≤ messageRatio (cavH lam (rootProb G lam s v)))
    (hT0 : messageRatio (rootProb G lam s v) ≤ T0) :
    rootProb G lam s v * oneVertexPsi price alpha beta gamma
      (rootProb G lam s v) rho (Tmass G lam s v) (zR G lam s v) f0 H0 T0 ≤
        responsePayment G lam price alpha beta gamma 0 s v rho t := by
  have hp := (rootProb_pos (G := G) hl s v).le
  have hpi := mul_nonneg hrho hp
  have h1 := mul_nonneg (mul_nonneg hprice hpi) (sub_nonneg.mpr hf0)
  have h2 := mul_nonneg (mul_nonneg hbeta hpi)
    (sub_nonneg.mpr (children_message_sum_lower hG hl hs hv hH0))
  have h3 := mul_nonneg hgamma (sub_nonneg.mpr (children_response_energy hG hl hs hv))
  have h4 := mul_nonneg (mul_nonneg (mul_nonneg hgamma hp) (sq_nonneg (zR G lam s v)))
    (sub_nonneg.mpr hT0)
  have hid := one_vertex_difference hG hl price alpha beta gamma rho t f0 H0 T0 hs hv hchild
  linarith

/-- Printed Lemma 5.11 on generated component descendants, with no added rho hypothesis. -/
theorem rootRecord_one_vertex_payment_lower (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    (price alpha beta gamma f0 H0 T0 : ℝ)
    (hprice : 0 ≤ price) (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma)
    {K : Finset V} (hK : ConnectedIn G K)
    (hKc : ∀ x ∈ K, ∀ y, G.Adj x y → y ∈ K) {r0 : V} (hr0 : r0 ∈ K)
    {s : Finset V} {v : V} {rho t : ℝ} (hrec : RootRecord G lam K r0 s v rho t)
    (hchild : (nbrsIn G s v).Nonempty)
    (hf0 : f0 ≤ src lam (rootProb G lam s v) rho)
    (hH00 : 0 ≤ H0) (hH0 : H0 ≤ messageRatio (cavH lam (rootProb G lam s v)))
    (hT0 : messageRatio (rootProb G lam s v) ≤ T0) :
    rootProb G lam s v * oneVertexPsi price alpha beta gamma
      (rootProb G lam s v) rho (Tmass G lam s v) (zR G lam s v) f0 H0 T0 ≤
        responsePayment G lam price alpha beta gamma 0 s v rho t :=
  one_vertex_payment_lower hG hl price alpha beta gamma rho t f0 H0 T0
    hprice hbeta hgamma (rootRecord_rho_bounds hG hl hKc hr0 hrec).1
    (rootRecord_connected hG hK hr0 hrec) (rootRecord_mem hr0 hrec) hchild hf0 hH00 hH0 hT0

end Erdos993Lean.Analytic.V213.VarianceResponse

#check Erdos993Lean.Analytic.V213.VarianceResponse.oneVertexPsi
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.oneVertexPsi
#check Erdos993Lean.Analytic.V213.VarianceResponse.one_vertex_difference_algebra
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.one_vertex_difference_algebra
#check Erdos993Lean.Analytic.V213.VarianceResponse.messageRatio_root_eq
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.messageRatio_root_eq
#check Erdos993Lean.Analytic.V213.VarianceResponse.child_messageRatio_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.child_messageRatio_lower
#check Erdos993Lean.Analytic.V213.VarianceResponse.children_message_sum_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.children_message_sum_lower
#check Erdos993Lean.Analytic.V213.VarianceResponse.children_response_energy
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.children_response_energy
#check Erdos993Lean.Analytic.V213.VarianceResponse.one_vertex_difference
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.one_vertex_difference
#check Erdos993Lean.Analytic.V213.VarianceResponse.one_vertex_payment_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.one_vertex_payment_lower
#check Erdos993Lean.Analytic.V213.VarianceResponse.rootRecord_one_vertex_payment_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.rootRecord_one_vertex_payment_lower

-- Inherited API audits.
#check Erdos993Lean.Analytic.O2.child_le_cavH
#print axioms Erdos993Lean.Analytic.O2.child_le_cavH
#check Erdos993Lean.Analytic.O2.actQ_lt_one'
#print axioms Erdos993Lean.Analytic.O2.actQ_lt_one'
#check Finset.sq_sum_div_le_sum_sq_div
#print axioms Finset.sq_sum_div_le_sum_sq_div
