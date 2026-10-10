module

public import Erdos993Lean.Analytic.V213.ResponsePayment
public import Erdos993Lean.Analytic.V213.ResponsePairEnergy

/-!
Current Lemma 5.19 (f4:lem4.1): exact local split on actual parent-child records.
The J=0 convention is proved from a child without children. No sign of d is
assumed. The unordered-pair energy has its exact ordered-pair interpretation in
ResponsePairEnergy.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse

open Finset Erdos993Lean.Analytic.Tail Erdos993Lean.Analytic.Reserve
open Erdos993Lean.Analytic.O2

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

variable (G) in
noncomputable def responseH (lam : ℝ) (s : Finset V) (v : V) : ℝ :=
  rootProb G lam s v / yLog G lam s v

variable (G) in
noncomputable def responseJ (lam : ℝ) (s : Finset V) (v : V) : ℝ :=
  rootProb G lam s v * responseH G lam s v * Tmass G lam s v

variable (G) in
noncomputable def responseY (lam : ℝ) (s : Finset V) (v : V) : ℝ :=
  rootProb G lam s v * zR G lam s v / yLog G lam s v

variable (G) in
noncomputable def responseParentP (lam gamma : ℝ) (s : Finset V) (v : V) (rho : ℝ) : ℝ :=
  rho*(1-rootProb G lam s v)+gamma*responseH G lam s v

variable (G) in
/-- The literal child payment a+b*h+c*y+d*y^2+delta*(h-y)^2/J. -/
noncomputable def responseChildPayment (lam price alpha beta gamma delta : ℝ)
    (s : Finset V) (v : V) (rho : ℝ) (w : V) : ℝ :=
  let p := rootProb G lam s v
  let Y := Tmass G lam s v
  let P := responseParentP G lam gamma s v rho
  let N := price*rho*src lam p rho+alpha*(1-rho)-P
  let ss := 2*P-alpha-beta
  let d := gamma-delta-p*P*Y
  let C := compIn G (s.erase v) w
  let h := responseH G lam C w
  let J := responseJ G lam C w
  let y := responseY G lam C w
  p*N/Y+(beta*rho*p)*h+(p*ss)*y+d*y^2+delta*(h-y)^2/J

/-- Exact normalized child moment identities. -/
theorem response_moment_scaling (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    {s : Finset V} (hs : ConnectedIn G s) {v : V} (hv : v ∈ s) :
    yLog G lam s v * responseH G lam s v = rootProb G lam s v ∧
    yLog G lam s v * responseY G lam s v = rootProb G lam s v*zR G lam s v := by
  have hphi := (yLog_pos hG hl hs hv).ne'
  constructor
  · unfold responseH
    field_simp [hphi]
  · unfold responseY
    field_simp [hphi]

/-- The normalized energy equals the actual reserve, including a zero child log-mass. -/
theorem responseReserve_scaled (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    (gamma delta : ℝ) {s : Finset V} (hs : ConnectedIn G s) {v : V} (hv : v ∈ s) :
    responseReserve G lam gamma delta s v = yLog G lam s v *
      (gamma*responseY G lam s v^2+
        delta*(responseH G lam s v-responseY G lam s v)^2/responseJ G lam s v) := by
  have hp := (rootProb_pos (G := G) hl s v).ne'
  have hphi := (yLog_pos hG hl hs hv).ne'
  by_cases hT : Tmass G lam s v = 0
  · simp only [responseReserve,responseH,responseY,responseJ,hT,mul_zero,zero_div,add_zero]
    field_simp [hphi]
    ring
  · unfold responseReserve responseJ responseH responseY
    field_simp [hp,hphi,hT] <;> ring

/-- The printed response convention for a child without children. -/
theorem response_leaf_coordinates (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    {s : Finset V} (hs : ConnectedIn G s) {v : V} (hv : v ∈ s)
    (hchild : nbrsIn G s v = ∅) :
    responseJ G lam s v = 0 ∧ responseY G lam s v = responseH G lam s v := by
  constructor
  · simp only [responseJ,Tmass,hchild,Finset.sum_empty,mul_zero]
  · simp only [responseY,responseH,zR_of_nbrsIn_empty hG hl.le hs hv hchild,mul_one]

/-- Linear expansion of the weighted quadratic child sum. -/
theorem weighted_child_polynomial_sum {ι : Type*} (S : Finset ι)
    (phi h y J : ι → ℝ) (a b c d delta : ℝ) :
    (∑ i ∈ S, phi i*(a+b*h i+c*y i+d*y i^2+delta*(h i-y i)^2/J i)) =
    a*(∑ i ∈ S, phi i)+b*(∑ i ∈ S, phi i*h i)+c*(∑ i ∈ S, phi i*y i)+
      d*(∑ i ∈ S, phi i*y i^2)+delta*(∑ i ∈ S, phi i*(h i-y i)^2/J i) := by
  calc
    _ = ∑ i ∈ S, (a*phi i+b*(phi i*h i)+c*(phi i*y i)+
        d*(phi i*y i^2)+delta*(phi i*(h i-y i)^2/J i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by simp only [Finset.sum_add_distrib,← Finset.mul_sum]

/-- The parent algebra after the exact weighted sums have been taken. -/
theorem local_split_scalar (price alpha beta gamma delta p rho g P Y W U E : ℝ)
    (hY : Y ≠ 0) :
    (price*(rho*p)*g-p*P*(1-W)^2+alpha*(p*(1-W)-rho*p)+
      beta*(p*((1-W)-1)+(rho*p)*U)+gamma*E-delta*W^2/Y) -
    (p*(price*rho*g+alpha*(1-rho)-P)+(beta*rho*p)*U+
      (p*(2*P-alpha-beta))*W+(gamma-delta-p*P*Y)*E) =
    (p*P+delta/Y)*(Y*E-W^2) := by
  field_simp [hY]
  ring

/-- Exact Lemma 5.19 on a vertex with a child, with no sign assumption on d. -/
theorem response_local_split (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    (price alpha beta gamma delta rho t : ℝ)
    {s : Finset V} (hs : ConnectedIn G s) {v : V} (hv : v ∈ s)
    (hchild : (nbrsIn G s v).Nonempty) :
    responsePayment G lam price alpha beta gamma delta s v rho t -
      (∑ w ∈ nbrsIn G s v, yLog G lam (compIn G (s.erase v) w) w *
        responseChildPayment G lam price alpha beta gamma delta s v rho w) =
    (rootProb G lam s v*responseParentP G lam gamma s v rho+delta/Tmass G lam s v) *
      pairEnergy (nbrsIn G s v)
        (fun w => yLog G lam (compIn G (s.erase v) w) w)
        (fun w => responseY G lam (compIn G (s.erase v) w) w) := by
  let S := nbrsIn G s v
  let C : V → Finset V := fun w => compIn G (s.erase v) w
  let phi : V → ℝ := fun w => yLog G lam (C w) w
  let h : V → ℝ := fun w => responseH G lam (C w) w
  let y : V → ℝ := fun w => responseY G lam (C w) w
  let J : V → ℝ := fun w => responseJ G lam (C w) w
  let p := rootProb G lam s v
  let z := zR G lam s v
  let Y := Tmass G lam s v
  let P := responseParentP G lam gamma s v rho
  let g := src lam p rho
  let N := price*rho*g+alpha*(1-rho)-P
  let a := p*N/Y
  let b := beta*rho*p
  let c := p*(2*P-alpha-beta)
  let d := gamma-delta-p*P*Y
  let U := ∑ w ∈ S, phi w*h w
  let W := ∑ w ∈ S, phi w*y w
  let E := ∑ w ∈ S, phi w*y w^2
  let R := ∑ w ∈ S, phi w*(h w-y w)^2/J w
  have hYpos : 0 < Y := Tmass_pos hG hl hs hv hchild
  have hY : Y = ∑ w ∈ S, phi w := rfl
  have hU : U = ∑ w ∈ S, rootProb G lam (C w) w := by
    exact Finset.sum_congr rfl fun w hw =>
      (response_moment_scaling hG hl (compIn_branch hG hs hv hw).1 (self_mem_branch hw)).1
  have hW : W = 1-z := by
    have he : W = ∑ w ∈ S, rootProb G lam (C w) w*zR G lam (C w) w := by
      exact Finset.sum_congr rfl fun w hw =>
        (response_moment_scaling hG hl (compIn_branch hG hs hv hw).1 (self_mem_branch hw)).2
    have hz := zR_rec hG hl.le hs hv
    change z = 1-(∑ w ∈ S, rootProb G lam (C w) w*zR G lam (C w) w) at hz
    linarith
  have hreserve : (∑ w ∈ S, responseReserve G lam gamma delta (C w) w) = gamma*E+delta*R := by
    calc
      _ = ∑ w ∈ S, phi w*(gamma*y w^2+delta*(h w-y w)^2/J w) := by
        exact Finset.sum_congr rfl fun w hw =>
          responseReserve_scaled hG hl gamma delta (compIn_branch hG hs hv hw).1 (self_mem_branch hw)
      _ = ∑ w ∈ S, (gamma*(phi w*y w^2)+delta*(phi w*(h w-y w)^2/J w)) := by
        apply Finset.sum_congr rfl
        intro w hw
        ring
      _ = gamma*E+delta*R := by simp only [Finset.sum_add_distrib,← Finset.mul_sum,E,R]
  have hpoly : (∑ w ∈ S, phi w*responseChildPayment G lam price alpha beta gamma delta s v rho w) =
      a*Y+b*U+c*W+d*E+delta*R := by
    change (∑ w ∈ S, phi w*(a+b*h w+c*y w+d*y w^2+delta*(h w-y w)^2/J w)) = _
    rw [weighted_child_polynomial_sum,← hY]
  have ha : a*Y = p*N := div_mul_cancel₀ _ hYpos.ne'
  have hpP : (rho*p)*(1-p)*z^2+gamma*(p*z)^2/yLog G lam s v = p*P*z^2 := by
    change (rho*p)*(1-p)*z^2+gamma*(p*z)^2/yLog G lam s v =
      p*(rho*(1-p)+gamma*(p/yLog G lam s v))*z^2
    ring
  have hroot : responseReserve G lam gamma delta s v =
      gamma*(p*z)^2/yLog G lam s v+delta*(1-z)^2/Y := rfl
  have hPhi : responsePayment G lam price alpha beta gamma delta s v rho t =
      price*(rho*p)*g-p*P*z^2+alpha*(p*z-rho*p)+beta*(p*(z-1)+(rho*p)*U)+
        gamma*E+delta*R-delta*(1-z)^2/Y := by
    change price*((rho*p)*g)-(rho*p)*(1-p)*z^2+alpha*(p*z-rho*p)+
      beta*(p*(z-1)+(rho*p)*(∑ w ∈ S, rootProb G lam (C w) w))+
      (∑ w ∈ S, responseReserve G lam gamma delta (C w) w)-
      responseReserve G lam gamma delta s v = _
    rw [← hU,hreserve,hroot]
    linear_combination -hpP
  have hvariance : Y*E-W^2 = pairEnergy S phi y := by
    rw [hY]
    exact weighted_pair_identity S phi y
  change responsePayment G lam price alpha beta gamma delta s v rho t -
      (∑ w ∈ S, phi w*responseChildPayment G lam price alpha beta gamma delta s v rho w) =
    (p*P+delta/Y)*pairEnergy S phi y
  rw [hPhi,hpoly,ha,← hvariance]
  have hz : z = 1-W := by linarith [hW]
  rw [hz]
  dsimp only [N,b,c,d]
  have he := local_split_scalar price alpha beta gamma delta p rho g P Y W U E hYpos.ne'
  linear_combination he

/-- The coefficient multiplying the pair squares is nonnegative in the printed regime. -/
theorem response_split_coefficient_nonneg (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    {gamma delta rho : ℝ} (hgamma : 0 ≤ gamma) (hdelta : 0 < delta) (hrho : 0 ≤ rho)
    {s : Finset V} (hs : ConnectedIn G s) {v : V} (hv : v ∈ s) :
    0 ≤ rootProb G lam s v*responseParentP G lam gamma s v rho+delta/Tmass G lam s v := by
  have hp := (rootProb_pos (G := G) hl s v).le
  have hp1 : 0 ≤ 1-rootProb G lam s v := by linarith [rootProb_lt_one (G := G) hl.le hv]
  have hP : 0 ≤ responseParentP G lam gamma s v rho :=
    add_nonneg (mul_nonneg hrho hp1)
      (mul_nonneg hgamma (div_nonneg hp (yLog_pos hG hl hs hv).le))
  exact add_nonneg (mul_nonneg hp hP) (div_nonneg hdelta.le (Tmass_nonneg hG hl hs hv))

/-- The exact difference in the local split is nonnegative. -/
theorem response_local_split_nonneg (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    (price alpha beta gamma delta rho t : ℝ)
    (hgamma : 0 ≤ gamma) (hdelta : 0 < delta) (hrho : 0 ≤ rho)
    {s : Finset V} (hs : ConnectedIn G s) {v : V} (hv : v ∈ s)
    (hchild : (nbrsIn G s v).Nonempty) :
    0 ≤ responsePayment G lam price alpha beta gamma delta s v rho t -
      (∑ w ∈ nbrsIn G s v, yLog G lam (compIn G (s.erase v) w) w *
        responseChildPayment G lam price alpha beta gamma delta s v rho w) := by
  rw [response_local_split hG hl price alpha beta gamma delta rho t hs hv hchild]
  exact mul_nonneg (response_split_coefficient_nonneg hG hl hgamma hdelta hrho hs hv)
    (pairEnergy_nonneg _ _ _ fun w hw =>
      (yLog_pos hG hl (compIn_branch hG hs hv hw).1 (self_mem_branch hw)).le)

/-- The printed implication, on actual descendants and actual child payments. -/
theorem rootRecord_payment_nonneg_of_children (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    (price alpha beta gamma delta : ℝ) (hgamma : 0 ≤ gamma) (hdelta : 0 < delta)
    {K : Finset V} (hK : ConnectedIn G K)
    (hKc : ∀ x ∈ K, ∀ y, G.Adj x y → y ∈ K) {r0 : V} (hr0 : r0 ∈ K)
    {s : Finset V} {v : V} {rho t : ℝ} (hrec : RootRecord G lam K r0 s v rho t)
    (hchild : (nbrsIn G s v).Nonempty)
    (hZ : ∀ w ∈ nbrsIn G s v, 0 ≤ responseChildPayment G lam price alpha beta gamma delta s v rho w) :
    0 ≤ responsePayment G lam price alpha beta gamma delta s v rho t := by
  have hs := rootRecord_connected hG hK hr0 hrec
  have hv := rootRecord_mem hr0 hrec
  have hsplit := response_local_split_nonneg hG hl price alpha beta gamma delta rho t
    hgamma hdelta (rootRecord_rho_bounds hG hl hKc hr0 hrec).1 hs hv hchild
  have hsum : 0 ≤ ∑ w ∈ nbrsIn G s v, yLog G lam (compIn G (s.erase v) w) w *
      responseChildPayment G lam price alpha beta gamma delta s v rho w := by
    exact Finset.sum_nonneg fun w hw => mul_nonneg
      (yLog_pos hG hl (compIn_branch hG hs hv hw).1 (self_mem_branch hw)).le (hZ w hw)
  linarith

end Erdos993Lean.Analytic.V213.VarianceResponse

#check Erdos993Lean.Analytic.V213.VarianceResponse.responseH
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.responseH
#check Erdos993Lean.Analytic.V213.VarianceResponse.responseJ
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.responseJ
#check Erdos993Lean.Analytic.V213.VarianceResponse.responseY
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.responseY
#check Erdos993Lean.Analytic.V213.VarianceResponse.responseParentP
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.responseParentP
#check Erdos993Lean.Analytic.V213.VarianceResponse.responseChildPayment
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.responseChildPayment
#check Erdos993Lean.Analytic.V213.VarianceResponse.response_moment_scaling
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.response_moment_scaling
#check Erdos993Lean.Analytic.V213.VarianceResponse.responseReserve_scaled
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.responseReserve_scaled
#check Erdos993Lean.Analytic.V213.VarianceResponse.response_leaf_coordinates
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.response_leaf_coordinates
#check Erdos993Lean.Analytic.V213.VarianceResponse.weighted_child_polynomial_sum
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.weighted_child_polynomial_sum
#check Erdos993Lean.Analytic.V213.VarianceResponse.local_split_scalar
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.local_split_scalar
#check Erdos993Lean.Analytic.V213.VarianceResponse.response_local_split
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.response_local_split
#check Erdos993Lean.Analytic.V213.VarianceResponse.response_split_coefficient_nonneg
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.response_split_coefficient_nonneg
#check Erdos993Lean.Analytic.V213.VarianceResponse.response_local_split_nonneg
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.response_local_split_nonneg
#check Erdos993Lean.Analytic.V213.VarianceResponse.rootRecord_payment_nonneg_of_children
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.rootRecord_payment_nonneg_of_children
