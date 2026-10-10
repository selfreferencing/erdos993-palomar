module

public import Erdos993Lean.Analytic.V213.LowMeanHeat

/-!
Differentiation of the signed beta monomials in Lemma 6.6 of version 2.13 of the manuscript
(`r12:lem13`). Both exponents are
integers; neither exponent is assumed nonnegative. All identities are on
the open probability interval (0,1).
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanMonomial (c : ℝ) (a b : ℤ) (q : ℝ) : ℝ := c * q ^ a * (1 - q) ^ b
noncomputable def lowMeanMonomialD (c : ℝ) (a b : ℤ) (q : ℝ) : ℝ :=
  lowMeanMonomial c a b q * ((a : ℝ) / q - (b : ℝ) / (1 - q))
def lowMeanPi (a b : ℤ) (q : ℝ) : ℝ :=
  ((a + b : ℤ) : ℝ) * (((a + b : ℤ) : ℝ) - 1) * q ^ 2 -
    2 * (a : ℝ) * (((a + b : ℤ) : ℝ) - 1) * q + (a : ℝ) * ((a : ℝ) - 1)
noncomputable def lowMeanMonomialDD (c : ℝ) (a b : ℤ) (q : ℝ) : ℝ :=
  lowMeanMonomial c a b q * lowMeanPi a b q / (q ^ 2 * (1 - q) ^ 2)

theorem lowMeanMonomial_hasDerivAt (c : ℝ) (a b : ℤ) {q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) :
    HasDerivAt (lowMeanMonomial c a b) (lowMeanMonomialD c a b q) q := by
  have hq : q ≠ 0 := hq0.ne'
  have h1 : 1 - q ≠ 0 := (sub_pos.mpr hq1).ne'
  have hd := ((hasDerivAt_zpow a q (Or.inl hq)).const_mul c).mul
    ((hasDerivAt_zpow b (1 - q) (Or.inl h1)).comp q ((hasDerivAt_id q).const_sub 1))
  convert hd using 1
  · rfl
  · unfold lowMeanMonomialD lowMeanMonomial
    simp only [Function.comp_apply]
    rw [zpow_sub₀ hq, zpow_sub₀ h1, zpow_one, zpow_one]
    field_simp
    ring

theorem lowMeanMonomialD_hasDerivAt (c : ℝ) (a b : ℤ) {q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) :
    HasDerivAt (lowMeanMonomialD c a b) (lowMeanMonomialDD c a b q) q := by
  have hq : q ≠ 0 := hq0.ne'
  have h1 : 1 - q ≠ 0 := (sub_pos.mpr hq1).ne'
  have hd := ((hasDerivAt_const q (a : ℝ)).div (hasDerivAt_id q) hq).sub
    ((hasDerivAt_const q (b : ℝ)).div ((hasDerivAt_id q).const_sub 1) h1)
  have hp := (lowMeanMonomial_hasDerivAt c a b hq0 hq1).mul hd
  convert hp using 1
  · rfl
  · unfold lowMeanMonomialD lowMeanMonomialDD lowMeanPi
    simp only [Pi.sub_apply, Pi.div_apply, id_eq]
    push_cast
    field_simp
    ring

theorem lowMeanMonomial_abs (c : ℝ) (a b : ℤ) {q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) :
    |lowMeanMonomial c a b q| = |c| * q ^ a * (1 - q) ^ b := by
  simp only [lowMeanMonomial, abs_mul, abs_of_pos (zpow_pos hq0 a),
    abs_of_pos (zpow_pos (sub_pos.mpr hq1) b)]

/-- c/|c| is the printed sign sigma for c≠0. -/
theorem lowMeanMonomialDD_signed {c : ℝ} (hc : c ≠ 0) (a b : ℤ) {q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) :
    lowMeanMonomialDD c a b q =
      |lowMeanMonomial c a b q| * (c / |c| * lowMeanPi a b q) / (q ^ 2 * (1 - q) ^ 2) := by
  have habs : |c| ≠ 0 := abs_ne_zero.mpr hc
  rw [lowMeanMonomial_abs c a b hq0 hq1]
  unfold lowMeanMonomialDD lowMeanMonomial
  field_simp

/-- The affine numerator controls the sign of the logarithmic derivative;
this identity is valid also for a+b=0 and negative exponents. -/
theorem lowMeanMonomialD_affine (c : ℝ) (a b : ℤ) {q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) :
    lowMeanMonomialD c a b q = lowMeanMonomial c a b q *
      ((a : ℝ) - ((a + b : ℤ) : ℝ) * q) / (q * (1 - q)) := by
  have hq : q ≠ 0 := hq0.ne'
  have h1 : 1 - q ≠ 0 := (sub_pos.mpr hq1).ne'
  unfold lowMeanMonomialD
  push_cast
  field_simp
  ring

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMeanMonomial_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.lowMeanMonomialD_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.lowMeanMonomialDD_signed
#print axioms Erdos993Lean.Analytic.V213.lowMeanMonomialD_affine
