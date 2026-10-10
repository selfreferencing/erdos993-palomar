module

public import Erdos993Lean.Analytic.V213.ResponseInnovation
public import Erdos993Lean.Analytic.V213.ResponseLocalData

/-!
Current paper Lemma 5.10 (f4:lem2.9), with the literal two-generation reserve.
This is not the inherited O2 BandData payment.  The price and the four multipliers
are fixed real numbers throughout each component.  The identity is algebraic;
its inequality uses exactly gamma,delta >= 0 and local payment nonnegativity on
actual generated descendants.  No band certificate or completed ratio theorem
is assumed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse

open Finset Erdos993Lean.Analytic.Tail Erdos993Lean.Analytic.Reserve
open Erdos993Lean.Analytic.O2

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

variable (G) in
/-- The literal two-generation reserve; real division makes its second term zero at a leaf. -/
noncomputable def responseReserve (lam gamma delta : ℝ) (s : Finset V) (v : V) : ℝ :=
  gamma * (rootProb G lam s v * zR G lam s v)^2 / yLog G lam s v +
    delta * (1-zR G lam s v)^2 / Tmass G lam s v

variable (G) in
/-- The printed source mass pi*g in the actual rooted record. -/
noncomputable def responseSourceMass (lam : ℝ) (s : Finset V) (v : V) (rho t : ℝ) : ℝ :=
  (rho * rootProb G lam s v) * src lam (rootProb G lam s v) rho

variable (G) in
/-- The exact printed payment, including both the alpha and beta cancellation terms. -/
noncomputable def responsePayment (lam price alpha beta gamma delta : ℝ)
    (s : Finset V) (v : V) (rho t : ℝ) : ℝ :=
  price * responseSourceMass G lam s v rho t -
    (rho * rootProb G lam s v) * (1-rootProb G lam s v) * zR G lam s v^2 +
    alpha * (rootProb G lam s v * zR G lam s v - rho * rootProb G lam s v) +
    beta * (rootProb G lam s v * (zR G lam s v-1) +
      (rho * rootProb G lam s v) * ∑ w ∈ nbrsIn G s v,
        rootProb G lam (compIn G (s.erase v) w) w) +
    (∑ w ∈ nbrsIn G s v, responseReserve G lam gamma delta (compIn G (s.erase v) w) w) -
    responseReserve G lam gamma delta s v

/-- The explicit convention at a vertex without children. -/
theorem responseReserve_leaf (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    (gamma delta : ℝ) {s : Finset V} (hs : ConnectedIn G s) {v : V} (hv : v ∈ s)
    (hchild : nbrsIn G s v = ∅) :
    responseReserve G lam gamma delta s v =
      gamma * (rootProb G lam s v)^2 / yLog G lam s v := by
  simp only [responseReserve, zR_of_nbrsIn_empty hG hl.le hs hv hchild,
    mul_one, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, zero_div, add_zero]

/-- These are the only multiplier signs needed for the printed forest inequality. -/
theorem responseReserve_nonneg (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    {gamma delta : ℝ} (hgamma : 0 ≤ gamma) (hdelta : 0 ≤ delta)
    {s : Finset V} (hs : ConnectedIn G s) {v : V} (hv : v ∈ s) :
    0 ≤ responseReserve G lam gamma delta s v := by
  exact add_nonneg
    (div_nonneg (mul_nonneg hgamma (sq_nonneg _)) (yLog_pos hG hl hs hv).le)
    (div_nonneg (mul_nonneg hdelta (sq_nonneg _)) (Tmass_nonneg hG hl hs hv))

/-- A finite rooted telescope, specialized to a charge added by each parent and removed locally. -/
theorem dfold_child_charge (lam : ℝ) (core charge : Finset V → V → ℝ → ℝ → ℝ)
    {s : Finset V} {v : V} (hv : v ∈ s) (rho t : ℝ) :
    dfold G lam (fun u w rho t => core u w rho t +
      (∑ x ∈ nbrsIn G u w, charge (compIn G (u.erase w) x) x
        (1-rho*rootProb G lam u w) (rootProb G lam u w)) - charge u w rho t) s v rho t =
    dfold G lam core s v rho t - charge s v rho t := by
  simpa only [add_sub_cancel_right] using
    (dfold_telescope (G := G) lam
      (fun u w rho t => core u w rho t + ∑ x ∈ nbrsIn G u w,
        charge (compIn G (u.erase w) x) x (1-rho*rootProb G lam u w)
          (rootProb G lam u w)) charge hv rho t)

private noncomputable def paymentCharge (lam beta gamma delta : ℝ)
    (s : Finset V) (v : V) (rho t : ℝ) : ℝ :=
  responseReserve G lam gamma delta s v + beta *
    (rootProb G lam s v - rho * rootProb G lam s v)

private noncomputable def paymentCore (lam price alpha beta : ℝ)
    (s : Finset V) (v : V) (rho t : ℝ) : ℝ :=
  price * responseSourceMass G lam s v rho t -
    rho * rootProb G lam s v * (1-rootProb G lam s v) * zR G lam s v^2 +
    (alpha+beta) * (rootProb G lam s v * zR G lam s v - rho * rootProb G lam s v)

private theorem child_vacancy_gap (lam rho : ℝ) (s : Finset V) (v : V) :
    (∑ w ∈ nbrsIn G s v, (rootProb G lam (compIn G (s.erase v) w) w -
      (1-rho*rootProb G lam s v) * rootProb G lam (compIn G (s.erase v) w) w)) =
    (rho*rootProb G lam s v) * ∑ w ∈ nbrsIn G s v,
      rootProb G lam (compIn G (s.erase v) w) w := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  ring

private theorem payment_decomposition (lam price alpha beta gamma delta : ℝ)
    (s : Finset V) (v : V) (rho t : ℝ) :
    responsePayment G lam price alpha beta gamma delta s v rho t =
    paymentCore (G := G) lam price alpha beta s v rho t +
      (∑ w ∈ nbrsIn G s v, paymentCharge (G := G) lam beta gamma delta
        (compIn G (s.erase v) w) w (1-rho*rootProb G lam s v) (rootProb G lam s v)) -
      paymentCharge (G := G) lam beta gamma delta s v rho t := by
  unfold responsePayment paymentCore paymentCharge
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, child_vacancy_gap]
  ring

private theorem paymentCore_fold (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    (price alpha beta : ℝ) {s : Finset V} (hs : ConnectedIn G s) {v : V} (hv : v ∈ s) :
    dfold G lam (paymentCore (G := G) lam price alpha beta) s v 1 0 =
      price * dfold G lam (responseSourceMass G lam) s v 1 0 - varB G univ lam s := by
  unfold paymentCore
  rw [dfold_add, dfold_sub, dfold_mul_left, dfold_mul_left, dfold_sub,
    response_mean_fold hG hl hs hv, boundary_marginal_mean_fold hG hl hs hv,
    ← innovation_identity hG hl hs hv]
  ring

/-- The exact forest identity in printed Lemma 5.10, on a rooted component. -/
theorem response_forest_identity (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    (price alpha beta gamma delta : ℝ) {s : Finset V} (hs : ConnectedIn G s)
    {v : V} (hv : v ∈ s) :
    price * dfold G lam (responseSourceMass G lam) s v 1 0 - varB G univ lam s =
      dfold G lam (responsePayment G lam price alpha beta gamma delta) s v 1 0 +
        responseReserve G lam gamma delta s v := by
  have heq : responsePayment G lam price alpha beta gamma delta =
      (fun u w rho t => paymentCore (G := G) lam price alpha beta u w rho t +
        (∑ x ∈ nbrsIn G u w, paymentCharge (G := G) lam beta gamma delta
          (compIn G (u.erase w) x) x (1-rho*rootProb G lam u w)
          (rootProb G lam u w)) - paymentCharge (G := G) lam beta gamma delta u w rho t) := by
    funext u w rho t
    exact payment_decomposition lam price alpha beta gamma delta u w rho t
  rw [heq, dfold_child_charge (G := G) lam _ _ hv, paymentCore_fold hG hl price alpha beta hs hv]
  simp only [paymentCharge, one_mul, sub_self, mul_zero, add_zero, sub_add_cancel]

/-- The source mass uses the actual full-forest marginal on each generated record. -/
theorem responseSourceMass_actual_marginal (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    {K : Finset V} {r0 : V} (hKc : ∀ x ∈ K, ∀ y, G.Adj x y → y ∈ K) (hr0 : r0 ∈ K)
    {s : Finset V} {v : V} {rho t : ℝ} (hrec : RootRecord G lam K r0 s v rho t) :
    responseSourceMass G lam s v rho t = gMarg G lam v * src lam (rootProb G lam s v) rho := by
  rw [responseSourceMass, rootRecord_marginal hG hl hKc hr0 hrec]

/-- Payment positivity is requested only for actual descendants, exactly as printed. -/
theorem response_variance_le_of_payments (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    (price alpha beta gamma delta : ℝ) (hgamma : 0 ≤ gamma) (hdelta : 0 ≤ delta)
    {s : Finset V} (hs : ConnectedIn G s) {v : V} (hv : v ∈ s)
    (hpay : ∀ u w rho t, RootRecord G lam s v u w rho t →
      0 ≤ responsePayment G lam price alpha beta gamma delta u w rho t) :
    varB G univ lam s ≤ price * dfold G lam (responseSourceMass G lam) s v 1 0 := by
  have hfold : 0 ≤ dfold G lam (responsePayment G lam price alpha beta gamma delta) s v 1 0 := by
    apply dfold_nonneg_of_inv hG lam (RootRecord G lam s v)
      (fun u w rho t hu hw hrec x hx => RootRecord.child hrec hx)
      (fun u w rho t hu hw hrec => hpay u w rho t hrec) hs hv RootRecord.top
  have hreserve := responseReserve_nonneg hG hl hgamma hdelta hs hv
  have hid := response_forest_identity hG hl price alpha beta gamma delta hs hv
  linarith

end Erdos993Lean.Analytic.V213.VarianceResponse

#check Erdos993Lean.Analytic.V213.VarianceResponse.responseReserve
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.responseReserve
#check Erdos993Lean.Analytic.V213.VarianceResponse.responseSourceMass
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.responseSourceMass
#check Erdos993Lean.Analytic.V213.VarianceResponse.responsePayment
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.responsePayment
#check Erdos993Lean.Analytic.V213.VarianceResponse.responseReserve_leaf
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.responseReserve_leaf
#check Erdos993Lean.Analytic.V213.VarianceResponse.responseReserve_nonneg
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.responseReserve_nonneg
#check Erdos993Lean.Analytic.V213.VarianceResponse.dfold_child_charge
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.dfold_child_charge
#check Erdos993Lean.Analytic.V213.VarianceResponse.response_forest_identity
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.response_forest_identity
#check Erdos993Lean.Analytic.V213.VarianceResponse.responseSourceMass_actual_marginal
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.responseSourceMass_actual_marginal
#check Erdos993Lean.Analytic.V213.VarianceResponse.response_variance_le_of_payments
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.response_variance_le_of_payments
