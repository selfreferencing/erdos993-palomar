module

public import Erdos993Lean.Analytic.V213.FiberLowerCurvature

/-!
Exact printed polynomial/discriminant algebra. The rational
constants are the literal source coefficients. This is symbolic polynomial
proof on all a in[0,1], with no generated-family or numerical premise.
The actual Q point and derivative are bound separately by the F02 consumer.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def fiberLowerAb (a : ℝ) : ℝ := 303 / 1000 - 1353 / 2000 * a + 51 / 125 * a ^ 2

noncomputable def fiberLowerVb (a : ℝ) : ℝ := 189 / 100 - 211 / 125 * a - 533 / 1000 * a ^ 2

noncomputable def fiberLowerDiscriminantPolynomial (a : ℝ) : ℝ :=
  15 / 8 - 29 / 5 * a + 13 / 2 * a ^ 2 - 21 / 10 * a ^ 3

theorem fiber_lower_discriminant_identity (a : ℝ) :
    18 * fiberLowerAb a - fiberLowerVb a ^ 2 - 1 / 250 - fiberLowerDiscriminantPolynomial a =
      29 / 10000 + 91 * a / 25000 + 2349 * a ^ 2 / 250000 +
        (16503 * a ^ 3 + 284089 * a ^ 3 * (1 - a)) / 1000000 := by
  unfold fiberLowerAb fiberLowerVb fiberLowerDiscriminantPolynomial
  ring

theorem fiber_lower_discriminant_decomposition {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    fiberLowerDiscriminantPolynomial a ≤ 18 * fiberLowerAb a - fiberLowerVb a ^ 2 - 1 / 250 := by
  have hp : 0 ≤ 29 / 10000 + 91 * a / 25000 + 2349 * a ^ 2 / 250000 +
      (16503 * a ^ 3 + 284089 * a ^ 3 * (1 - a)) / 1000000 := by
    have h1 : 0 ≤ 1 - a := by linarith
    positivity
  linarith [fiber_lower_discriminant_identity a]

theorem fiber_lower_discriminant_polynomial_gt {a : ℝ} (ha1 : a ≤ 1) :
    (1 / 4 : ℝ) < fiberLowerDiscriminantPolynomial a := by
  let u : ℝ := a - 2 / 3
  have hu : u ≤ (1 / 3 : ℝ) := by dsimp [u]; linarith
  have hp : 0 ≤ (7 / 10 - 21 / 10 * u) * u ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have he : fiberLowerDiscriminantPolynomial a -
      (8 / 5 * (u + 1 / 48) ^ 2 + 79 / 288) = (7 / 10 - 21 / 10 * u) * u ^ 2 := by
    dsimp [fiberLowerDiscriminantPolynomial, u]
    ring
  nlinarith [sq_nonneg (u + 1 / 48)]

theorem fiber_lower_Vb_abs {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    |fiberLowerVb a| ≤ (19 / 10 : ℝ) := by
  have ha2 : a ^ 2 ≤ (1 : ℝ) := by nlinarith
  rw [abs_le]
  unfold fiberLowerVb
  constructor <;> nlinarith [sq_nonneg a]

theorem fiber_lower_derivative_square {V a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (he : |V - fiberLowerVb a| ≤ (1 / 1000 : ℝ)) :
    V ^ 2 ≤ fiberLowerVb a ^ 2 + 1 / 250 := by
  have hb := fiber_lower_Vb_abs ha0 ha1
  have hmul := mul_le_mul hb he (abs_nonneg (V - fiberLowerVb a)) (by norm_num : (0 : ℝ) ≤ 19 / 10)
  rw [← abs_mul] at hmul
  have hc := (abs_le.mp hmul).2
  have hd : (V - fiberLowerVb a) ^ 2 ≤ (1 / 1000 : ℝ) ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 1000)).2 he
    simpa only [sq_abs] using h
  nlinarith

theorem fiber_lower_discriminant {A V a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hA : fiberLowerAb a ≤ A) (hV : |V - fiberLowerVb a| ≤ (1 / 1000 : ℝ)) :
    (1 / 4 : ℝ) < 18 * A - V ^ 2 := by
  have hd := fiber_lower_discriminant_decomposition ha0 ha1
  have hp := fiber_lower_discriminant_polynomial_gt ha1
  have hs := fiber_lower_derivative_square ha0 ha1 hV
  linarith

theorem fiber_lower_Q_positive_of_point {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hA : fiberLowerAb a ≤ fiberLowerQ (1 / 19) a ((11 / 10 : ℝ) ^ 2))
    (hV : |fiberLowerQPrime (1 / 19) a ((11 / 10 : ℝ) ^ 2) - fiberLowerVb a| ≤ (1 / 1000 : ℝ))
    {t : ℝ} (ht : 3 / 5 ≤ t) : (1 / 72 : ℝ) < fiberLowerQ (1 / 19) a t := by
  have hd := fiber_lower_discriminant ha0 ha1 hA hV
  have hq := fiber_lower_Q_tangent ha0 ht
  nlinarith [sq_nonneg (9 * (t - (11 / 10 : ℝ) ^ 2) +
    fiberLowerQPrime (1 / 19) a ((11 / 10 : ℝ) ^ 2))]

end Erdos993Lean.Analytic.V213
