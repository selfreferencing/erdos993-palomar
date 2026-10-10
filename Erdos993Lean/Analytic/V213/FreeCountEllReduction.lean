module

public import Erdos993Lean.Analytic.V213.FreeCountActivityTangent
public import Erdos993Lean.Analytic.V213.FreeCountRealExpEnvelopes

/-!
Analytic reduction for the actual ell in current T1 Lemma 3.2.
The polynomial is the displayed expression after zeta=lambda*exp (-y).
Its lower bound uses the proved scalarH upper bound and activity tangent.
No numerical row is evaluated and no old cap estimate is consumed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform

open Real Envelopes

noncomputable def ellPolynomial (g lam eta y : ℝ) : ℝ :=
  1-(25/24/g)*y*exp (-y)+
    lam*exp (-y)*(1+eta-(1+81/200/g)*y)+
    lam^2*exp (-2*y)*(eta-y/2)

noncomputable def capM (g u : ℝ) : ℝ := 25/24/g+(1+81/200/g)*u
noncomputable def capR (g u eta : ℝ) : ℝ := 1+(1+eta)*u/capM g u

theorem capM_pos {g u : ℝ} (hg : 0 < g) (hu : 0 < u) : 0 < capM g u := by
  unfold capM
  positivity

theorem capR_pos {g u eta : ℝ} (hg : 0 < g) (hu : 0 < u) (heta : 0 ≤ eta) :
    0 < capR g u eta := by
  have hm := capM_pos hg hu
  unfold capR
  positivity

/-- The printed polynomial is a genuine lower bound for a positive multiple
of ell+eta, on all y>=0, not merely on the feasible subset. -/
theorem ellPolynomial_le_scaled_ell {D lam eta y : ℝ}
    (hD : 0 < D) (hlam : 0 < lam) (hy : 0 ≤ y) :
    ellPolynomial (5*D/12) lam eta y ≤
      (ell D lam y+eta)*(lam*exp (-y))*(1+lam*exp (-y)) := by
  let z := lam*exp (-y)
  have hz : 0 < z := mul_pos hlam (exp_pos _)
  have hz1 : 0 < 1+z := by linarith
  have hg := gamma_pos hD hlam
  have hf := logMass_pos hlam y
  have hp : message lam y = z/(1+z) := rfl
  have ha : ap lam y = 1/z := by
    dsimp [ap, z]
    rw [exp_neg]
    field_simp [hlam.ne', (exp_pos y).ne'] <;> ring
  have hid : (ell D lam y+eta)*z*(1+z) =
      1+z+eta*z*(1+z)-y*z/gamma D lam-
        y*z*(1+z)*(message lam y/logMass lam y) := by
    rw [ell_normalized hD hlam, h_normalized hlam, ha]
    unfold B
    rw [hp]
    field_simp [hz.ne', hz1.ne', hg.ne', hf.ne'] <;> ring
  have hh := (message_scalarH_bounds hlam y).2
  have hhm := mul_le_mul_of_nonneg_left hh
    (show 0 ≤ y*z*(1+z) by positivity)
  have hp2 : y*z*(1+z)*(1-message lam y/2)=y*z*(2+z)/2 := by
    rw [hp]
    field_simp [hz1.ne'] <;> ring
  rw [hp2] at hhm
  have ht := activityRatio_le_printed_line hlam
  have hb := logActivity_pos hlam
  have hg0 : 0 < 5*D/12 := by positivity
  have hrate : z/gamma D lam ≤ (25/24+(81/200)*lam)*exp (-y)/(5*D/12) := by
    have hm := mul_le_mul_of_nonneg_right ht
      (show 0 ≤ exp (-y)/(5*D/12) by positivity)
    convert hm using 1 <;> (try dsimp [z, gamma, logActivity]) <;>
      field_simp [hD.ne', show log (1+lam) ≠ 0 from hb.ne'] <;> ring
  have hyrate := mul_le_mul_of_nonneg_left hrate hy
  have hz2 : z^2 = lam^2*exp (-2*y) := by
    dsimp [z]
    rw [mul_pow, ← exp_nat_mul]
    congr 1
    congr 1
    norm_num <;> ring
  have hpoly : ellPolynomial (5*D/12) lam eta y =
      1+z+eta*z*(1+z)-
        y*((25/24+(81/200)*lam)*exp (-y)/(5*D/12))-y*z*(2+z)/2 := by
    unfold ellPolynomial
    rw [← hz2]
    dsimp [z]
    ring
  rw [hpoly]
  change _ ≤ (ell D lam y+eta)*z*(1+z)
  rw [hid]
  simp only [mul_div_assoc] at hhm hyrate ⊢
  linarith only [hhm, hyrate]

/-- The standard global maximum of a shifted linear exponential. -/
theorem shifted_exp_bound (x a : ℝ) :
    (x-a)*exp (-x) ≤ exp (-a-1) := by
  calc
    (x-a)*exp (-x) = ((x-a)*exp (-(x-a)))*exp (-a) := by
      rw [mul_assoc, ← exp_add]
      congr 1
      congr 1
      ring
    _ ≤ exp (-1)*exp (-a) :=
      mul_le_mul_of_nonneg_right (mul_exp_neg_le_exp_neg_one (x-a)) (exp_pos _).le
    _ = exp (-a-1) := by rw [← exp_add]; congr 1; ring

theorem quadratic_exp_lower (eta y : ℝ) :
    -exp (-(4*eta+1))/4 ≤ exp (-2*y)*(eta-y/2) := by
  have hh := shifted_exp_bound (2*y) (4*eta)
  have he : exp (-(4*eta)-1)=exp (-(4*eta+1)) := by congr 1; ring
  rw [he] at hh
  have he0 : exp (-2*y)=exp (-(2*y)) := by congr 1; ring
  rw [he0]
  nlinarith only [hh]

theorem quadratic_term_lower {lam u eta y : ℝ}
    (hlam : 0 ≤ lam) (hlu : lam ≤ u) :
    -u^2/4*exp (-(4*eta+1)) ≤ lam^2*exp (-2*y)*(eta-y/2) := by
  have hs : lam^2 ≤ u^2 := by nlinarith
  have h1 := mul_le_mul_of_nonneg_left (quadratic_exp_lower eta y) (sq_nonneg lam)
  have h2 := mul_le_mul_of_nonneg_right hs (show 0 ≤ exp (-(4*eta+1))/4 by positivity)
  nlinarith

theorem exp_neg_one_le_three_eighths : exp (-1) ≤ (3/8 : ℝ) := by
  rw [exp_neg]
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 8/3)
    exp_one_gt_eight_thirds.le
  simpa using h

theorem exp_neg_nat_le_three_eighths (n : ℕ) :
    exp (-(n : ℝ)) ≤ (3/8 : ℝ)^n := by
  have h := pow_le_pow_left₀ (exp_pos (-1)).le exp_neg_one_le_three_eighths n
  rw [← exp_nat_mul] at h
  simpa using h

theorem exp_tail_le_coarse {eta : ℝ} (heta : 1/2 ≤ eta) :
    exp (-(4*eta+1)) ≤ (27/512 : ℝ) := by
  calc
    exp (-(4*eta+1)) ≤ exp (-3) := exp_le_exp.mpr (by linarith)
    _ ≤ (27/512 : ℝ) := by
      have h := exp_neg_nat_le_three_eighths 3
      norm_num at h ⊢
      exact h

end Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform

-- Type and axiom audit commands.
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.capM_pos
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.capM_pos
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.capR_pos
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.capR_pos
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.ellPolynomial_le_scaled_ell
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.ellPolynomial_le_scaled_ell
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.shifted_exp_bound
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.shifted_exp_bound
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.quadratic_exp_lower
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.quadratic_exp_lower
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.quadratic_term_lower
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.quadratic_term_lower
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.exp_neg_one_le_three_eighths
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.exp_neg_one_le_three_eighths
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.exp_neg_nat_le_three_eighths
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.exp_neg_nat_le_three_eighths
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.exp_tail_le_coarse
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Uniform.exp_tail_le_coarse
