module

public import Erdos993Lean.BCFG.LogRemainderLower

/-!
The upper side of current Lemma 5.15.
The denominator (2*n+1) in the remainder is retained exactly.
This generic analytic proof does not evaluate the twelve later finite gates.
-/

@[expose] public section

set_option autoImplicit false

namespace Erdos993Lean.BCFG.Analytic

open Set Finset

/-- The printed upper sum and exact geometric remainder. -/
noncomputable def logUpper (n : ℕ) (z : ℝ) : ℝ :=
  logLower n z + 2*z^(2*n+1)/((2*(n : ℝ)+1)*(1-z^2))

/-- The exact upper gap has a positive derivative away from zero. -/
theorem logUpper_gap_hasDerivAt (n : ℕ) {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) :
    HasDerivAt (fun x => logUpper n x - Real.log ((1+x)/(1-x)))
      (4*z^(2*n+2)/((2*(n : ℝ)+1)*(1-z^2)^2)) z := by
  have hn : 0 < 2*(n : ℝ)+1 := by positivity
  have hd : 0 < 1-z^2 := by
    have hm : 0 < (1-z)*(1+z) :=
      mul_pos (sub_pos.mpr hz1) (by linarith)
    nlinarith
  have hrem := ((hasDerivAt_pow (2*n+1) z).const_mul 2).div
    (((hasDerivAt_pow 2 z).const_sub 1).const_mul (2*(n : ℝ)+1))
    (mul_ne_zero hn.ne' hd.ne')
  have h := hrem.sub (logLower_gap_hasDerivAt n hz hz1)
  have he :
      (2*((2*n+1 : ℕ) : ℝ)*z^(2*n+1-1)*((2*(n : ℝ)+1)*(1-z^2)) -
        2*z^(2*n+1)*((2*(n : ℝ)+1)*(-(2*z^(2-1))))) /
          ((2*(n : ℝ)+1)*(1-z^2))^2 - 2*z^(2*n)/(1-z^2) =
        4*z^(2*n+2)/((2*(n : ℝ)+1)*(1-z^2)^2) := by
    norm_num only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_mul, Nat.cast_one,
      Nat.cast_ofNat, pow_add, pow_one]
    field_simp [hn.ne', hd.ne'] <;> ring
  have h' : HasDerivAt
      (fun x => 2*x^(2*n+1)/((2*(n : ℝ)+1)*(1-x^2)) -
        (Real.log ((1+x)/(1-x)) - logLower n x))
      (4*z^(2*n+2)/((2*(n : ℝ)+1)*(1-z^2)^2)) z := by
    apply h.congr_deriv
    convert he using 1 <;> ring
  apply h'.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun x => by dsimp [logUpper]; ring)

/-- Strictness includes every positive z below one and every natural truncation order. -/
theorem log_lt_logUpper (n : ℕ) {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    Real.log ((1+z)/(1-z)) < logUpper n z := by
  have h := gap_pos_of_hasDerivAt_pos
    (f := fun x => logUpper n x - Real.log ((1+x)/(1-x)))
    (f' := fun x => 4*x^(2*n+2)/((2*(n : ℝ)+1)*(1-x^2)^2)) hz
    (by simp [logUpper, logLower])
    (fun x hx => logUpper_gap_hasDerivAt n hx.1 (hx.2.trans_lt hz1))
    (by
      intro x hx
      have hx1 : x < 1 := hx.2.trans hz1
      have hd : 0 < 1-x^2 := by
        have hm : 0 < (1-x)*(1+x) :=
          mul_pos (sub_pos.mpr hx1) (by linarith [hx.1])
        nlinarith
      have hn : 0 < 2*(n : ℝ)+1 := by positivity
      exact div_pos (mul_pos (by norm_num) (pow_pos hx.1 _))
        (mul_pos hn (pow_pos hd _)))
  exact sub_pos.mp h

/-- The upper half of Lemma 5.15 includes the assigned zero endpoint. -/
theorem log_le_logUpper (n : ℕ) {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) :
    Real.log ((1+z)/(1-z)) ≤ logUpper n z := by
  rcases eq_or_lt_of_le hz with hzero | hpos
  · subst z
    simp [logUpper, logLower]
  · exact (log_lt_logUpper n hpos hz1).le

/-- Current printed Lemma 5.15, both weak inequalities for n>=1. -/
theorem log_formulas (n : ℕ) (_hn : 1 ≤ n) {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) :
    logLower n z ≤ Real.log ((1+z)/(1-z)) ∧
      Real.log ((1+z)/(1-z)) ≤ logUpper n z :=
  ⟨logLower_le n hz hz1, log_le_logUpper n hz hz1⟩

/-- The two inequalities printed in Lemma 5.15 are strict for z>0. -/
theorem log_formulas_strict (n : ℕ) (_hn : 1 ≤ n) {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    logLower n z < Real.log ((1+z)/(1-z)) ∧
      Real.log ((1+z)/(1-z)) < logUpper n z :=
  ⟨logLower_lt n hz hz1, log_lt_logUpper n hz hz1⟩

end Erdos993Lean.BCFG.Analytic

#check Erdos993Lean.BCFG.Analytic.logUpper
#print axioms Erdos993Lean.BCFG.Analytic.logUpper
#check Erdos993Lean.BCFG.Analytic.logUpper_gap_hasDerivAt
#print axioms Erdos993Lean.BCFG.Analytic.logUpper_gap_hasDerivAt
#check Erdos993Lean.BCFG.Analytic.log_lt_logUpper
#print axioms Erdos993Lean.BCFG.Analytic.log_lt_logUpper
#check Erdos993Lean.BCFG.Analytic.log_le_logUpper
#print axioms Erdos993Lean.BCFG.Analytic.log_le_logUpper
#check Erdos993Lean.BCFG.Analytic.log_formulas
#print axioms Erdos993Lean.BCFG.Analytic.log_formulas
#check Erdos993Lean.BCFG.Analytic.log_formulas_strict
#print axioms Erdos993Lean.BCFG.Analytic.log_formulas_strict
