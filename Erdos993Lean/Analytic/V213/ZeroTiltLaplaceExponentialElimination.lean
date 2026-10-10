module

public import Erdos993Lean.Analytic.V213.ZeroTiltLaplaceScalarBounds

/-!
Analytic alternative for the F0 lower bound in current T2a 4.3.
It uses x <= 2 sinh(x/2), followed by one exact nonnegative polynomial
factorization, instead of differentiating log F0 and taking its limit.
No printed finite comparison or old curve is used.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace

open Real

noncomputable def halfExp (x : ℝ) : ℝ := exp (-x/2)
noncomputable def fZero (lam x : ℝ) : ℝ :=
  (exp x-1)/x*(1+q lam*exp (-x))^2/(1+lam*exp (-x))
noncomputable def eliminationQuotient (q A B z : ℝ) : ℝ :=
  (1+q*z)^2/((1+A*z)*(1+B*z))

theorem halfExp_pos (x : ℝ) : 0<halfExp x := exp_pos _

theorem halfExp_le_one {x : ℝ} (hx : 0≤x) : halfExp x≤1 := by
  unfold halfExp
  exact exp_le_one_iff.mpr (by linarith)

theorem halfExp_sq (x : ℝ) : (halfExp x)^2=exp (-x) := by
  unfold halfExp
  rw [pow_two, ← exp_add]
  congr 1
  ring

theorem exp_mul_halfExp (x : ℝ) : exp x*halfExp x=(halfExp x)⁻¹ := by
  unfold halfExp
  rw [← exp_add, ← exp_neg]
  congr 1
  ring

theorem x_le_halfExp_inv_sub {x : ℝ} (hx : 0≤x) :
    x≤(halfExp x)⁻¹-halfExp x := by
  have hh := Real.self_le_sinh_iff.mpr (show 0≤x/2 by linarith)
  have hi : exp (x/2)=(halfExp x)⁻¹ := by
    unfold halfExp
    rw [← exp_neg]
    congr 1
    ring
  have hneg : exp (-(x/2))=halfExp x := by
    unfold halfExp
    congr 1
    ring
  rw [Real.sinh_eq, hi, hneg] at hh
  change x/2≤((halfExp x)⁻¹-halfExp x)/2 at hh
  linarith

theorem exp_secant_lower {x : ℝ} (hx : 0<x) :
    (halfExp x)⁻¹≤(exp x-1)/x := by
  have hu := halfExp_pos x
  have hmul : x≤(exp x-1)*halfExp x := by
    calc
      x≤(halfExp x)⁻¹-halfExp x := x_le_halfExp_inv_sub hx.le
      _=(exp x-1)*halfExp x := by rw [sub_mul, exp_mul_halfExp, one_mul]
  have hh : x/halfExp x≤exp x-1 := (div_le_iff₀ hu).2 hmul
  apply (le_div_iff₀ hx).2
  simpa only [div_eq_mul_inv, mul_comm] using hh

/-- Exact factorization used only with 0<q<1 and 0<u<=1. -/
theorem fZero_gap_factor {q : ℝ} (hq1 : q<1) (u : ℝ) :
    (1+q*u^2)^2-(1-q)*(1+q)^2*u*(1+(q/(1-q))*u^2)=
      (1-u)*(1-q*u+q*u^2+q^2*u+q^2*u^2*(1-u)+q^3*u*(1+u)) := by
  have h1 : 1-q≠0 := by linarith
  field_simp [h1] <;> ring

theorem fZero_rational_lower {q u : ℝ} (hq : 0<q) (hq1 : q<1)
    (hu : 0<u) (hu1 : u≤1) :
    (1-q)*(1+q)^2≤(1+q*u^2)^2/(u*(1+(q/(1-q))*u^2)) := by
  have h1 : 0<1-q := by linarith
  have hden : 0<u*(1+(q/(1-q))*u^2) := by positivity
  have hqu : q*u<1 := (mul_le_mul_of_nonneg_left hu1 hq.le).trans_lt (by simpa using hq1)
  have hbr : 0≤1-q*u+q*u^2+q^2*u+q^2*u^2*(1-u)+q^3*u*(1+u) := by
    have hqu0 : 0≤1-q*u := by linarith
    have hu0 : 0≤1-u := by linarith
    positivity
  have hprod := mul_nonneg (show 0≤1-u by linarith) hbr
  rw [← fZero_gap_factor hq1 u] at hprod
  apply (le_div_iff₀ hden).2
  nlinarith only [hprod]

/-- The current F0 lower bound, with no derivative or limiting premise. -/
theorem fZero_lower {lam x : ℝ} (hlam : 0<lam) (hx : 0<x) :
    (1-q lam)*(1+q lam)^2≤fZero lam x := by
  have hu := halfExp_pos x
  have hq := q_pos hlam
  have hd : 0<1+lam*(halfExp x)^2 := by positivity
  have hb := fZero_rational_lower hq (q_lt_one hlam) hu (halfExp_le_one hx.le)
  rw [← activity_from_q hlam] at hb
  have hs := mul_le_mul_of_nonneg_right (exp_secant_lower hx)
    (show 0≤(1+q lam*(halfExp x)^2)^2/(1+lam*(halfExp x)^2) by positivity)
  have he : (halfExp x)⁻¹*((1+q lam*(halfExp x)^2)^2/(1+lam*(halfExp x)^2))=
      (1+q lam*(halfExp x)^2)^2/(halfExp x*(1+lam*(halfExp x)^2)) := by
    field_simp [hu.ne',hd.ne'] <;> ring
  rw [he] at hs
  refine hb.trans ?_
  convert hs using 1 <;> simp only [fZero, halfExp_sq] <;> ring

/-- Each linear fractional factor decreases with its nonnegative input. -/
theorem ratio_antitone {q A z r : ℝ} (hq : 0≤q) (hA : q≤A)
    (hz : 0≤z) (hzr : z≤r) :
    (1+q*r)/(1+A*r)≤(1+q*z)/(1+A*z) := by
  have hr : 0≤r := hz.trans hzr
  have hA0 : 0≤A := hq.trans hA
  have hd1 : 0<1+A*r := by positivity
  have hd2 : 0<1+A*z := by positivity
  apply (div_le_div_iff₀ hd1 hd2).2
  nlinarith [mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hzr)]

theorem eliminationQuotient_antitone {q A B z r : ℝ}
    (hq : 0≤q) (hA : q≤A) (hB : q≤B) (hz : 0≤z) (hzr : z≤r) :
    eliminationQuotient q A B r≤eliminationQuotient q A B z := by
  have hr : 0≤r := hz.trans hzr
  have hA0 : 0≤A := hq.trans hA
  have hB0 : 0≤B := hq.trans hB
  have h := mul_le_mul (ratio_antitone hq hA hz hzr) (ratio_antitone hq hB hz hzr)
    (show 0≤(1+q*r)/(1+B*r) by positivity)
    (show 0≤(1+q*z)/(1+A*z) by positivity)
  simpa only [eliminationQuotient, pow_two, div_mul_div_comm] using h

end Erdos993Lean.Analytic.V213.ZeroTiltLaplace

-- Audit commands.
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.halfExp_pos
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.halfExp_pos
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.halfExp_le_one
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.halfExp_le_one
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.halfExp_sq
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.halfExp_sq
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.exp_mul_halfExp
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.exp_mul_halfExp
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.x_le_halfExp_inv_sub
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.x_le_halfExp_inv_sub
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.exp_secant_lower
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.exp_secant_lower
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.fZero_gap_factor
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.fZero_gap_factor
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.fZero_rational_lower
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.fZero_rational_lower
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.fZero_lower
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.fZero_lower
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.ratio_antitone
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.ratio_antitone
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.eliminationQuotient_antitone
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.eliminationQuotient_antitone
