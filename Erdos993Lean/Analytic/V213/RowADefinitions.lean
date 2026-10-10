module

public import Erdos993Lean.Analytic.V213.ResponseRatioBounds
public import Erdos993Lean.Analytic.Defs

/-!
Literal scalar definitions for T. Zhang's current Row A proof, Proposition 5.12.
These definitions are local to Row A. The endpoint eta values
are rational lower bounds, not asserted equal to eta at the endpoints.
No coefficient array or unprinted rational coefficient is introduced here.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.RowA

noncomputable def q (lam : ℝ) : ℝ := lam / (1 + lam)
noncomputable def eta (lam : ℝ) : ℝ := q lam / Real.log (1 + lam)
noncomputable def sigma (lam : ℝ) : ℝ := (1 + 2 * lam) / (1 + lam)^2
noncomputable def childMass (lam x : ℝ) : ℝ := Real.log ((1 + lam * (1 - x)) / x)
noncomputable def theta (lam : ℝ) : ℝ := (lam - 1/3) / (3/5 - 1/3)

noncomputable def psi (lam x r z : ℝ) : ℝ :=
  sigma lam * x * (1-r)^2 - (1-r) * (1-q lam*x) * z^2 -
    (7*lam/20) * messageRatio (q lam*x) * z^2 +
    (7*(1+lam)/(20*x*childMass lam x)) * (1-z)^2 + (z-(1-r)) +
    (7/6) * (z-1+eta lam*(1-r)*childMass lam x)

noncomputable def leafPsi (lam r : ℝ) : ℝ :=
  sigma lam * (1-r)^2 - (1-r)*(1-q lam) -
    (7*lam/20)*messageRatio (q lam) + r

noncomputable def endpointPsi (lam eta0 sigma0 x r z : ℝ) : ℝ :=
  (7*(1+lam)/(20*x*childMass lam x))*(1-z)^2 -
    ((1-r)*(1-q lam*x)+(7*lam/20)*(1-q lam*x/2))*z^2 +
    (z-(1-r))+(7/6)*(z-1+eta0*(1-r)*childMass lam x)+sigma0*x*(1-r)^2

noncomputable def kappaMinus (x : ℝ) : ℝ :=
  21*(4-x)*(x+2)/(20*(1-x)*(4+28*x-5*x^2))
noncomputable def kappaPlus (x : ℝ) : ℝ :=
  21*(8-3*x)*(x+4)/(20*(1-x)*(16+88*x-29*x^2))
noncomputable def tauMinus (x : ℝ) : ℝ :=
  (7*(343/400)/3)*(2*(1-x)/(2+x)+(2*(1-x)/(2+x))^3/3)
noncomputable def tauPlus (x : ℝ) : ℝ :=
  (7*(319/400)/3)*(4*(1-x)/(4+x)+(4*(1-x)/(4+x))^3/3)
noncomputable def nuMinus (x : ℝ) : ℝ := 67/60-127*x/480
noncomputable def nuPlus (x : ℝ) : ℝ := 121/100-663*x/1600

/-- The displayed quadratic, before taking its degree-two Bernstein form in r. -/
noncomputable def quad (kappa tau nu sigma0 q0 x r z : ℝ) : ℝ :=
  (kappa-nu+(1-q0*x)*r)*z^2+(13/6-2*kappa)*z+
    (kappa-13/6+tau+sigma0*x+(1-tau-2*sigma0*x)*r+sigma0*x*r^2)
noncomputable def quadMinus (x r z : ℝ) : ℝ :=
  quad (kappaMinus x) (tauMinus x) (nuMinus x) (15/16) (1/4) x r z
noncomputable def quadPlus (x r z : ℝ) : ℝ :=
  quad (kappaPlus x) (tauPlus x) (nuPlus x) (55/64) (3/8) x r z

theorem q_eq_actQ (lam : ℝ) : q lam = Erdos993Lean.Analytic.actQ lam := rfl

theorem q_bounds {lam : ℝ} (hl : 0 < lam) : 0 < q lam ∧ q lam < 1 := by
  have hd : 0 < 1+lam := by linarith
  constructor
  · exact div_pos hl hd
  · exact (div_lt_iff₀ hd).2 (by linarith)

theorem row_q_bounds {lam : ℝ} (hl : 1/3 ≤ lam) (hu : lam ≤ 3/5) :
    1/4 ≤ q lam ∧ q lam ≤ 3/8 := by
  have hd : 0 < 1+lam := by linarith
  unfold q
  constructor
  · apply (le_div_iff₀ hd).2
    linarith
  · apply (div_le_iff₀ hd).2
    linarith

theorem childMass_pos {lam x : ℝ} (hl : 0 < lam) (hx : 0 < x) (hx1 : x < 1) :
    0 < childMass lam x := by
  apply Real.log_pos
  apply (lt_div_iff₀ hx).2
  nlinarith [mul_pos hl (sub_pos.mpr hx1)]

theorem childMass_exp {lam x : ℝ} (hl : 0 < lam) (hx : 0 < x) (hx1 : x < 1) :
    Real.exp (childMass lam x) = (1+lam*(1-x))/x := by
  apply Real.exp_log
  exact div_pos (by nlinarith [mul_pos hl (sub_pos.mpr hx1)]) hx

theorem childMass_one (lam : ℝ) : childMass lam 1 = 0 := by
  simp [childMass]

theorem theta_bounds {lam : ℝ} (hl : 1/3 ≤ lam) (hu : lam ≤ 3/5) :
    0 ≤ theta lam ∧ theta lam ≤ 1 := by
  unfold theta
  constructor <;> norm_num <;> linarith

theorem theta_affine (lam : ℝ) : (1-theta lam)*(1/3)+theta lam*(3/5)=lam := by
  unfold theta
  ring

theorem eta_eq_messageRatio {lam : ℝ} (hl : 0 < lam) :
    eta lam = messageRatio (q lam) := by
  have hq := q_bounds hl
  have hd : 0 < 1+lam := by linarith
  have hsub : 1-q lam = (1+lam)⁻¹ := by
    unfold q
    field_simp [hd.ne'] <;> ring
  rw [messageRatio_of_ne_zero hq.1.ne',hsub,Real.log_inv]
  simp only [neg_neg,eta]

theorem nuMinus_eq (x : ℝ) :
    nuMinus x = 1-(1/4)*x+(7*(1/3)/20)*(1-(1/4)*x/2) := by
  unfold nuMinus
  ring

theorem nuPlus_eq (x : ℝ) :
    nuPlus x = 1-(3/8)*x+(7*(3/5)/20)*(1-(3/8)*x/2) := by
  unfold nuPlus
  ring

theorem leaf_endpoint_minus (r : ℝ) :
    (15/16)*(1-r)^2-(1-r)*(1-1/4)-(7*(1/3)/20)*(1-(1/4)/2)+r =
      (15/16)*(r-1/15)^2+13/160 := by ring

theorem leaf_endpoint_plus (r : ℝ) :
    (55/64)*(1-r)^2-(1-r)*(1-3/8)-(7*(3/5)/20)*(1-(3/8)/2)+r =
      (55/64)*(r-3/55)^2+1077/17600 := by ring

theorem leaf_endpoint_minus_pos (r : ℝ) : 0 < (15/16)*(r-1/15)^2+13/160 := by positivity
theorem leaf_endpoint_plus_pos (r : ℝ) : 0 < (55/64)*(r-3/55)^2+1077/17600 := by positivity

end Erdos993Lean.Analytic.V213.VarianceResponse.RowA

#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.q
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.q
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.eta
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.eta
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.sigma
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.sigma
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.childMass
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.childMass
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.theta
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.theta
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.psi
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.psi
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.leafPsi
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.leafPsi
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.endpointPsi
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.endpointPsi
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.kappaMinus
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.kappaMinus
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.kappaPlus
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.kappaPlus
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.tauMinus
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.tauMinus
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.tauPlus
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.tauPlus
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.nuMinus
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.nuMinus
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.nuPlus
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.nuPlus
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.quad
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.quad
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.quadMinus
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.quadMinus
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.quadPlus
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.quadPlus
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.q_eq_actQ
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.q_eq_actQ
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.q_bounds
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.q_bounds
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.row_q_bounds
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.row_q_bounds
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.childMass_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.childMass_pos
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.childMass_exp
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.childMass_exp
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.childMass_one
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.childMass_one
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.theta_bounds
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.theta_bounds
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.theta_affine
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.theta_affine
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.eta_eq_messageRatio
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.eta_eq_messageRatio
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.nuMinus_eq
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.nuMinus_eq
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.nuPlus_eq
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.nuPlus_eq
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.leaf_endpoint_minus
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.leaf_endpoint_minus
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.leaf_endpoint_plus
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.leaf_endpoint_plus
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.leaf_endpoint_minus_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.leaf_endpoint_minus_pos
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.leaf_endpoint_plus_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.leaf_endpoint_plus_pos
