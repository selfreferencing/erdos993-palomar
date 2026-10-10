module

public import Erdos993Lean.Analytic.V213.FiberMassLinearization

/-!
Literal affine-minorant definitions for Theorem6.15.
N is the actual shifted fiber width; Y concerns the analytic
minorant as a function of xi. No monotonicity of an integer-index mass is
asserted. Rational polynomial definitions are the printed formulas.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def fiberAffineH (N : ℝ) : ℝ := N - 1 + 1 / N

noncomputable def fiberAffineK (w : ℝ) : ℝ := (w + 3 / 2) / Real.sqrt (3 / 2)

noncomputable def fiberAffineY (N w xi : ℝ) : ℝ :=
  (1 - w + fiberAffineH N * xi ^ 2) *
    Real.exp (-(2 * xi ^ 2 + fiberAffineK w * Real.sqrt N * xi) / (N + 1))

noncomputable def fiberAffineG (t : ℝ) : ℝ := 641 / 625 + (128 / 125) * t

noncomputable def fiberAffineC (w : ℝ) : ℝ := 13 / 10 - 21 * w / 40

noncomputable def fiberAffineA (w : ℝ) : ℝ :=
  21 / 40 * w ^ 2 - (34401 / 25000) * w + 7903 / 6250

noncomputable def fiberAffineV (w : ℝ) : ℝ :=
  -(63 / 80) * w ^ 2 + (201323 / 50000) * w - 45819 / 12500

noncomputable def fiberAffineCurvature (w : ℝ) : ℝ := 9 - 9 * w ^ 2 / 8

noncomputable def fiberAffineP (w : ℝ) : ℝ := 21 / 40 * w ^ 2 - 69 / 50 * w + 63 / 50

noncomputable def fiberAffineQ (w : ℝ) : ℝ := 14 / 3 - 4 * w + 4 * w ^ 2 / 5

noncomputable def fiberAffineSupport (beta t w : ℝ) : ℝ :=
  9 / 2 * (t - 1) ^ 2 + t * (w - 1) - 2 / 5 - beta * (t - 1) +
    fiberAffineC w * ((641 / 625 - w) * t ^ (-(3 / 2 : ℝ)) +
      (128 / 125) * t ^ (-(1 / 2 : ℝ)))

end Erdos993Lean.Analytic.V213
