module

public import Erdos993Lean.Analytic.V213.FiberDefinitions

/-!
The exact shifted-penalty averaging Lemma 6.7 (`r12:lem14`).
The printed probability and five moment inputs
remain conditional hypotheses. All scale and shifted-offset costs are proved
from the source definition of F and the accepted zero-tilt criterion.
No unreviewed DF10 record is consumed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

theorem fiber_scale_mul_F {q mu : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hmu : 0 < mu)
    (M : ℕ) (j : ℤ) :
    fiberScale q mu * fiberF q mu M j =
      kernel2 q (fiberWeightL q) (fiberWeightR q) M j +
        (fiberScale q mu / (fiberVariance q * mu)) * fiberOffset q M j ^ 2 := by
  have hn : fiberNormalization q mu ≠ 0 := (fiber_normalization_pos hq0 hq1 hmu).ne'
  unfold fiberF fiberScale
  rw [mul_add, inv_mul_cancel_left₀ hn]
  ring

/-- Lemma 6.7 on the full printed probability and positive-mean domain.
The affine coefficients are unrestricted; only the two printed prices are nonnegative. -/
theorem fiber_shifted_penalty_average
    {ι : Type} (X : Mixture ι) (k : ℤ)
    {q mu theta D ell alpha beta Gamma Z : ℝ}
    (hq : q ∈ Set.Icc (1 / 4) (3 / 4)) (hmu : 0 < mu)
    (hGamma : 0 ≤ Gamma) (hZ : 0 ≤ Z)
    (hpoint : ∀ (M : ℕ) (j : ℤ),
      alpha + beta * ((M : ℝ) / mu - 1) - Gamma * ((M : ℝ) / mu - 1) ^ 2 -
        Z * (1 - q) ^ M ≤ fiberF q mu M j)
    (hmargin : 0 < alpha - theta - Gamma * D / mu -
      fiberSkew q ^ 2 / ((1 - fiberSkew q ^ 2) * mu) - Z * Real.exp (-ell * mu))
    (hX : X.IsProb) (hmean : X.meanM = mu)
    (hdelta : X.expect (fun M Y => delta q k M Y) = 0)
    (hvar : X.varM ≤ D * mu)
    (hdelta2 : X.expect (fun M Y => delta q k M Y ^ 2) ≤
      theta * (q * (1 - q)) * mu)
    (htail : X.expect (fun M _ => (1 - q) ^ M) ≤ Real.exp (-ell * mu)) :
    ¬ X.WeakValley q k := by
  have hq0 : 0 < q := by linarith [hq.1]
  have hq1 : q < 1 := by linarith [hq.2]
  have hv : 0 < fiberVariance q := fiber_variance_pos hq0 hq1
  have hK : 0 < fiberScale q mu := fiber_scale_pos hq0 hq1 hmu
  have hvm : 0 < fiberVariance q * mu := mul_pos hv hmu
  let K := fiberScale q mu
  let eta := K / (fiberVariance q * mu)
  let r := fiberSkew q
  have heta : 0 < eta := div_pos hK hvm
  have hcost : 0 ≤ K * Gamma / mu ^ 2 := div_nonneg (mul_nonneg hK.le hGamma) (sq_nonneg _)
  apply zeroTilt_noValley X k hq0 hq1 heta hcost
    (fiber_weights_nonneg hq).1 (fiber_weights_nonneg hq).2 (mul_nonneg hK.le hZ)
    (alpha := K * alpha - eta * r ^ 2 / 4)
    (beta := K * beta / mu) (gamma := K * Gamma / mu ^ 2)
    (xi := -r * eta) (z0 := K * Z) (ell := ell) (D := D) (theta := theta)
    ?_ ?_ hX hmean hdelta hvar hdelta2 htail
  · intro M j
    have hh := mul_le_mul_of_nonneg_left (hpoint M j) hK.le
    have hF := fiber_scale_mul_F hq0 hq1 hmu M j
    change K * fiberF q mu M j = _ at hF
    rw [hF] at hh
    have heq : K * (alpha + beta * ((M : ℝ) / mu - 1) -
          Gamma * ((M : ℝ) / mu - 1) ^ 2 - Z * (1 - q) ^ M) - eta * r ^ 2 / 4 =
        K * alpha - eta * r ^ 2 / 4 + K * beta / mu * ((M : ℝ) - mu) -
          K * Gamma / mu ^ 2 * ((M : ℝ) - mu) ^ 2 - K * Z * (1 - q) ^ M := by
      field_simp [hmu.ne']
      <;> ring
    have hoffset : eta * fiberOffset q M j ^ 2 - eta * r ^ 2 / 4 =
        -r * eta * ((j : ℝ) - q * M) + eta * ((j : ℝ) - q * M) ^ 2 := by
      dsimp [fiberOffset, r]
      ring
    change _ ≤ kernel2 q (fiberWeightL q) (fiberWeightR q) M j +
      -r * eta * ((j : ℝ) - q * M) + eta * ((j : ℝ) - q * M) ^ 2
    change K * _ ≤ kernel2 q (fiberWeightL q) (fiberWeightR q) M j + eta * _ at hh
    rw [← heq]
    linarith [hoffset]
  · have hskew : 1 - r ^ 2 = 4 * fiberVariance q := fiber_variance_skew q
    have heq : K * alpha - eta * r ^ 2 / 4 - K * Gamma / mu ^ 2 * D * mu -
        K * Z * Real.exp (-ell * mu) - eta * theta * q * (1 - q) * mu =
      K * (alpha - theta - Gamma * D / mu -
        r ^ 2 / ((1 - r ^ 2) * mu) - Z * Real.exp (-ell * mu)) := by
      rw [hskew]
      dsimp [eta, K]
      unfold fiberVariance
      field_simp [hmu.ne', hq0.ne', (sub_pos.mpr hq1).ne']
      <;> ring
    rw [heq]
    exact mul_pos hK hmargin

end Erdos993Lean.Analytic.V213

#check Erdos993Lean.Analytic.V213.fiber_shifted_penalty_average
#print axioms Erdos993Lean.Analytic.V213.fiber_shifted_penalty_average
