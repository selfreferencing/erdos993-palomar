module

public import Erdos993Lean.Analytic.V213.LowMeanTaylor

/-!
The exponential truncation and mean-concavity argument in version 2.13 of the manuscript.
Concavity is proved for the actual mean
margin; no concavity claim is made for its rational approximant.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanE60 (x : ℝ) : ℝ :=
  ∑ r ∈ Finset.range 61, x ^ r / (r.factorial : ℝ)

theorem lowMeanE60_ge_one {x : ℝ} (hx : 0 ≤ x) : 1 ≤ lowMeanE60 x := by
  have hh := Finset.single_le_sum (s := Finset.range 61)
    (f := fun r : ℕ => x ^ r / (r.factorial : ℝ))
    (fun r _ => div_nonneg (pow_nonneg hx _) (Nat.cast_nonneg _))
    (show 0 ∈ Finset.range 61 by simp)
  simpa [lowMeanE60] using hh

theorem lowMeanE60_le_exp {x : ℝ} (hx : 0 ≤ x) : lowMeanE60 x ≤ Real.exp x :=
  Real.sum_le_exp_of_nonneg hx 61

/-- Any nonnegative lower bound x on the exponent gives the paper's
rational upper bound on the priced exponential tail. -/
theorem lowMean_expTail_le {z x y : ℝ} (hz : 0 ≤ z) (hx : 0 ≤ x) (hxy : x ≤ y) :
    z * Real.exp (-y) ≤ z / lowMeanE60 x := by
  have hE : 0 < lowMeanE60 x := lt_of_lt_of_le (by norm_num) (lowMeanE60_ge_one hx)
  calc
    z * Real.exp (-y) ≤ z * Real.exp (-x) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hxy)) hz
    _ = z / Real.exp x := by rw [Real.exp_neg]; ring
    _ ≤ z / lowMeanE60 x := div_le_div_of_nonneg_left hz hE (lowMeanE60_le_exp hx)

theorem lowMean_quadratic_exp_concave (A B gamma z ell : ℝ)
    (hgamma : 0 ≤ gamma) (hz : 0 ≤ z) :
    ConcaveOn ℝ Set.univ (fun x : ℝ => A + B * x - gamma * x ^ 2 - z * Real.exp (-ell * x)) := by
  let f := fun x : ℝ => A + B * x - gamma * x ^ 2 - z * Real.exp (-ell * x)
  let f' := fun x : ℝ => B - 2 * gamma * x + z * ell * Real.exp (-ell * x)
  let f'' := fun x : ℝ => -2 * gamma - z * ell ^ 2 * Real.exp (-ell * x)
  have hd (x : ℝ) : HasDerivAt f (f' x) x := by
    have he := (((hasDerivAt_id x).const_mul (-ell)).exp).const_mul z
    have hp := (((hasDerivAt_id x).const_mul B).const_add A).sub
      (((hasDerivAt_id x).pow 2).const_mul gamma)
    convert hp.sub he using 1
    · rfl
    · dsimp [f']
      ring
  have hdd (x : ℝ) : HasDerivAt f' (f'' x) x := by
    have hp := ((hasDerivAt_id x).const_mul (2 * gamma)).const_sub B
    have he := (((hasDerivAt_id x).const_mul (-ell)).exp).const_mul (z * ell)
    convert hp.add he using 1
    · rfl
    · dsimp [f'']
      ring
  apply concaveOn_of_hasDerivWithinAt2_nonpos convex_univ
    (fun x _ => (hd x).continuousAt.continuousWithinAt)
    (fun x _ => (hd x).hasDerivWithinAt)
    (fun x _ => (hdd x).hasDerivWithinAt)
  intro x _
  have he := mul_nonneg (mul_nonneg hz (sq_nonneg ell)) (Real.exp_pos (-ell * x)).le
  dsimp [f'']
  linarith

/-- The actual mean margin in equation r12:eq49. -/
noncomputable def lowMeanMargin (alpha beta gamma m0 eta theta D z ell q mu : ℝ) : ℝ :=
  lowMeanPsi alpha beta gamma m0 mu - gamma * D * mu -
    eta * theta * q * (1 - q) * mu - z * Real.exp (-ell * mu)

theorem lowMeanMargin_concave (alpha beta gamma m0 eta theta D z ell q : ℝ)
    (hgamma : 0 ≤ gamma) (hz : 0 ≤ z) :
    ConcaveOn ℝ Set.univ (lowMeanMargin alpha beta gamma m0 eta theta D z ell q) := by
  have he : lowMeanMargin alpha beta gamma m0 eta theta D z ell q =
      fun mu : ℝ => (alpha - beta * m0 - gamma * m0 ^ 2) +
        (beta + 2 * gamma * m0 - gamma * D - eta * theta * q * (1 - q)) * mu -
        gamma * mu ^ 2 - z * Real.exp (-ell * mu) := by
    funext mu
    unfold lowMeanMargin lowMeanPsi
    ring
  rw [he]
  exact lowMean_quadratic_exp_concave _ _ _ _ _ hgamma hz

/-- Positive endpoint margins imply positivity throughout the closed mean
interval; the two endpoints may coincide. -/
theorem lowMean_concave_positive {f : ℝ → ℝ} {L H x : ℝ}
    (hf : ConcaveOn ℝ (Set.Icc L H) f) (hL : 0 < f L) (hH : 0 < f H)
    (hx : x ∈ Set.Icc L H) : 0 < f x := by
  by_cases hLH : L < H
  · have hd : 0 < H - L := sub_pos.mpr hLH
    have hchord := lowMean_concave_chord hLH hf hx
    have hmin : 0 < min (f L) (f H) := lt_min hL hH
    have ha : 0 ≤ (H - x) / (H - L) := div_nonneg (sub_nonneg.mpr hx.2) hd.le
    have hb : 0 ≤ (x - L) / (H - L) := div_nonneg (sub_nonneg.mpr hx.1) hd.le
    have hab : (H - x) / (H - L) + (x - L) / (H - L) = 1 := by field_simp; ring
    have h1 := mul_le_mul_of_nonneg_left (min_le_left (f L) (f H)) ha
    have h2 := mul_le_mul_of_nonneg_left (min_le_right (f L) (f H)) hb
    nlinarith
  · have he : x = L := by linarith [hx.1, hx.2]
    simpa [he] using hL

/-- The paper's rational approximant is a lower bound for the actual margin.
The only inputs are the variance and rate bounds, not any claim about
concavity of the approximant. -/
theorem lowMean_rationalMargin_le
    {alpha beta gamma m0 eta theta D z ell ellK q mu v : ℝ}
    (heta : 0 ≤ eta) (htheta : 0 ≤ theta) (hz : 0 ≤ z) (hmu : 0 ≤ mu)
    (hellK : 0 ≤ ellK) (hell : ellK ≤ ell) (hv : q * (1 - q) ≤ v) :
    lowMeanPsi alpha beta gamma m0 mu - gamma * D * mu - eta * theta * v * mu -
        z / lowMeanE60 (ellK * mu) ≤
      lowMeanMargin alpha beta gamma m0 eta theta D z ell q mu := by
  have htail := lowMean_expTail_le hz (mul_nonneg hellK hmu)
    (mul_le_mul_of_nonneg_right hell hmu)
  have hvar := mul_le_mul_of_nonneg_left hv (mul_nonneg (mul_nonneg heta htheta) hmu)
  unfold lowMeanMargin
  simp only [neg_mul] at htail ⊢
  nlinarith

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMeanE60_le_exp
#print axioms Erdos993Lean.Analytic.V213.lowMean_expTail_le
#print axioms Erdos993Lean.Analytic.V213.lowMeanMargin_concave
#print axioms Erdos993Lean.Analytic.V213.lowMean_concave_positive
#print axioms Erdos993Lean.Analytic.V213.lowMean_rationalMargin_le
