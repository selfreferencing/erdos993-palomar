module

public import Erdos993Lean.Analytic.V213.FreeCountEllReduction
public import Erdos993Lean.Analytic.V213.FreeCountUniformJ
public import Erdos993Lean.Analytic.V213.FreeCountVarianceCapPrintedData

/-!
Analytic completion of the uniform ell/rate part of Lemma 3.2,
conditional only on its printed finite comparisons (18). Each cap is closed.
The global exponential maxima are proved, not assumed. The final conjunction
also uses the same explicit logarithm comparison as the uniform-J proof.
No finite endpoint is evaluated here, and no older cap result is substituted.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform

open Real Envelopes

theorem ellPolynomial_positive_nonnegative_brace {g lam u eta y : ℝ}
    (hg : 1/2 ≤ g) (hlam : 0 ≤ lam) (hlu : lam ≤ u) (hu : u ≤ 7/3)
    (heta : 1/2 ≤ eta) (hy : 0 ≤ y)
    (hbrace : 0 ≤ 1+eta-(1+81/200/g)*y) :
    0 < ellPolynomial g lam eta y := by
  have hg0 : 0 < g := by linarith
  have hc : 25/24/g ≤ (25/12 : ℝ) := by
    apply (div_le_iff₀ hg0).2
    linarith
  have hye : y*exp (-y) ≤ (3/8 : ℝ) :=
    (mul_exp_neg_le_exp_neg_one y).trans exp_neg_one_le_three_eighths
  have hfirst : (25/24/g)*y*exp (-y) ≤ (25/32 : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_right hc (mul_nonneg hy (exp_pos (-y)).le)
    have h2 := mul_le_mul_of_nonneg_left hye (by norm_num : (0 : ℝ) ≤ 25/12)
    nlinarith
  have hquad := quadratic_term_lower (eta := eta) (y := y) hlam hlu
  have hu0 : 0 ≤ u := hlam.trans hlu
  have husq : u^2 ≤ (7/3 : ℝ)^2 := by nlinarith
  have htail := exp_tail_le_coarse heta
  have hprod := mul_le_mul husq htail (exp_pos _).le
    (by norm_num : (0 : ℝ) ≤ (7/3)^2)
  have hquad' : -(147/2048 : ℝ) ≤ lam^2*exp (-2*y)*(eta-y/2) := by
    nlinarith
  have hmiddle : 0 ≤ lam*exp (-y)*(1+eta-(1+81/200/g)*y) := by positivity
  unfold ellPolynomial
  linarith

theorem ellPolynomial_lower_nonpositive_brace {g lam u eta y : ℝ}
    (hg : 0 < g) (hlam : 0 ≤ lam) (hu : 0 < u) (hlu : lam ≤ u)
    (hbrace : 1+eta-(1+81/200/g)*y ≤ 0) :
    1-capM g u*exp (-capR g u eta)-u^2/4*exp (-(4*eta+1)) ≤
      ellPolynomial g lam eta y := by
  have hm := capM_pos hg hu
  have hlin := mul_le_mul_of_nonpos_right hlu
    (mul_nonpos_of_nonneg_of_nonpos (exp_pos (-y)).le hbrace)
  have hquad := quadratic_term_lower (eta := eta) (y := y) hlam hlu
  have hmax := shifted_exp_bound y ((1+eta)*u/capM g u)
  have her : -((1+eta)*u/capM g u)-1 = -capR g u eta := by
    unfold capR
    ring
  rw [her] at hmax
  have hmaxM := mul_le_mul_of_nonneg_left hmax hm.le
  have hid : -(25/24/g)*y*exp (-y)+u*exp (-y)*(1+eta-(1+81/200/g)*y) =
      -(capM g u*((y-(1+eta)*u/capM g u)*exp (-y))) := by
    field_simp [hm.ne', hg.ne']
    unfold capM
    field_simp [hg.ne'] <;> ring
  unfold ellPolynomial
  nlinarith

/-- Generic analytic consequence of the two exact displayed ell comparisons.
The exponent n is the printed integer 4*eta+1 (3 or 4 on the actual caps). -/
theorem ell_gt_neg_eta_of_printed_endpoints {D lam u eta H y : ℝ} {n : ℕ}
    (hD : 0 < D) (hg : 1/2 ≤ 5*D/12)
    (hlam : 0 < lam) (hlu : lam ≤ u) (hu : u ≤ 7/3)
    (heta : 1/2 ≤ eta) (hn : (n : ℝ) = 4*eta+1) (hH : 0 < H)
    (hTaylor : H < expPartial 5 (capR (5*D/12) u eta))
    (hmargin : 0 < 1-capM (5*D/12) u/H-u^2/4*(3/8 : ℝ)^n)
    (hy : 0 < y) : -eta < ell D lam y := by
  have hg0 : 0 < 5*D/12 := by positivity
  have hu0 : 0 < u := hlam.trans_le hlu
  have hm := capM_pos hg0 hu0
  have hr := capR_pos hg0 hu0 (by linarith : 0 ≤ eta)
  have hexp : H < exp (capR (5*D/12) u eta) :=
    hTaylor.trans_le (expPartial_le_exp 5 hr.le)
  have hR : exp (-capR (5*D/12) u eta) ≤ 1/H := by
    rw [exp_neg]
    simpa using one_div_le_one_div_of_le hH hexp.le
  have htail : exp (-(4*eta+1)) ≤ (3/8 : ℝ)^n := by
    rw [← hn]
    exact exp_neg_nat_le_three_eighths n
  have hpoly : 0 < ellPolynomial (5*D/12) lam eta y := by
    by_cases hbr : 0 ≤ 1+eta-(1+81/200/(5*D/12))*y
    · exact ellPolynomial_positive_nonnegative_brace hg hlam.le hlu hu heta hy.le hbr
    · have hlo := ellPolynomial_lower_nonpositive_brace hg0 hlam.le hu0 hlu
        (eta := eta) (y := y) (le_of_lt (lt_of_not_ge hbr))
      have h1 := mul_le_mul_of_nonneg_left hR hm.le
      have h2 := mul_le_mul_of_nonneg_left htail (show 0 ≤ u^2/4 by positivity)
      have hrational : capM (5*D/12) u*(1/H)=capM (5*D/12) u/H := by ring
      rw [hrational] at h1
      linarith
  have hscaled := hpoly.trans_le (ellPolynomial_le_scaled_ell hD hlam hy.le)
  have hpos : 0 < (lam*exp (-y))*(1+lam*exp (-y)) := by positivity
  have hell : 0 < ell D lam y+eta := by
    apply (mul_pos_iff_of_pos_right hpos).mp
    simpa only [mul_assoc] using hscaled
  linarith

namespace CapEndpoint

noncomputable def H : Cap → ℝ := PrintedCapData.H

def exponent : Cap → ℕ
  | .first | .second => 4
  | .third | .fourth | .fifth => 3

/-- Exactly the four rational comparisons displayed in (18), as Real
expressions to be supplied by the separate finite-certificate transfer. -/
def Printed (c : Cap) : Prop :=
  H c < expPartial 5 (capR (5*c.value/12) c.upper c.eta) ∧
  0 < 1-capM (5*c.value/12) c.upper/H c-c.upper^2/4*(3/8 : ℝ)^(exponent c) ∧
  (25/24+(81/200)*c.upper)/(5*c.value/12) < 10/3 ∧
  c.upper+(25/24+(81/200)*c.upper)/(5*c.value/12) < 14/3

theorem exponent_eq (c : Cap) : (exponent c : ℝ) = 4*c.eta+1 := by
  cases c <;> norm_num [exponent, Cap.eta]

theorem parameter_bounds (c : Cap) :
    1/2 ≤ 5*c.value/12 ∧ c.upper ≤ 7/3 ∧ 1/2 ≤ c.eta ∧ 0 < H c := by
  cases c <;> norm_num [Cap.value, Cap.upper, Cap.eta, H, PrintedCapData.H]

end CapEndpoint

theorem ell_gt_neg_eta_on_cap {c : Cap} {lam y : ℝ}
    (hc : c.Contains lam) (hf : CapEndpoint.Printed c) (hy : 0 < y) :
    -c.eta < ell c.value lam y := by
  have hp := CapEndpoint.parameter_bounds c
  exact ell_gt_neg_eta_of_printed_endpoints c.value_pos hp.1
    (Cap.activity_pos hc) hc.2 hp.2.1 hp.2.2.1 (CapEndpoint.exponent_eq c)
    hp.2.2.2 hf.1 hf.2.1 hy

/-- The entire printed Lemma 3.2, with only its separately listed finite
logarithm comparison and four-per-cap endpoint comparisons remaining. -/
theorem scalarBounds_of_printed_finite {c : Cap} {lam t y : ℝ}
    (hc : c.Contains lam) (ht : 0 ≤ t) (hy : 0 < y)
    (hlog : log (369/80 : ℝ) < 153/100) (hf : CapEndpoint.Printed c) :
    c.ScalarBounds lam t y := by
  have hJ := cap_J_bound hc ht hlog
  have hell := ell_gt_neg_eta_on_cap hc hf hy
  have hZ := Cap.denominator_of_two_bounds hc ht hJ hell
  have hr := rate_bounds_of_printed_endpoints c.value_pos (Cap.activity_pos hc)
    hc.2 hf.2.2.1 hf.2.2.2
  exact ⟨hJ, hell, hZ, hr.1, hr.2⟩

end Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform

-- Type and axiom audit commands.
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.ellPolynomial_positive_nonnegative_brace
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.ellPolynomial_positive_nonnegative_brace
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.ellPolynomial_lower_nonpositive_brace
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.ellPolynomial_lower_nonpositive_brace
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.ell_gt_neg_eta_of_printed_endpoints
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.ell_gt_neg_eta_of_printed_endpoints
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.CapEndpoint.exponent_eq
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.CapEndpoint.exponent_eq
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.CapEndpoint.parameter_bounds
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.CapEndpoint.parameter_bounds
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.ell_gt_neg_eta_on_cap
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.ell_gt_neg_eta_on_cap
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.scalarBounds_of_printed_finite
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.scalarBounds_of_printed_finite
