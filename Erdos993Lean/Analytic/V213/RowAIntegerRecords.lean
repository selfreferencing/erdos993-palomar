module

public import Mathlib

/-! Exact transcription of the printed Row A integer parts.

These are the integer parts, not the exact unprinted rational coefficients.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.RowA

def floorCoefficients : Fin 6 → Fin 9 → ℤ :=
  ![![84, 33, -332, -245, 514, 831, 479, 162, 37],
    ![1456, 3331, 2381, 2000, 4866, 5484, 3053, 1360, 437],
    ![583, 1984, 2413, 175, -2605, -2246, 345, 1300, 480],
    ![26, 1, -62, 55, 242, 225, 95, 25, 4],
    ![478, 974, 1211, 2300, 3008, 1874, 554, 157, 55],
    ![199, 623, 913, 765, 268, 23, 185, 226, 72]]

noncomputable def floorPolynomial (r : Fin 6) (x : ℝ) : ℝ :=
  ∑ k : Fin 9, (floorCoefficients r k : ℝ) * x ^ (k : ℕ)

end Erdos993Lean.Analytic.V213.VarianceResponse.RowA

#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.floorCoefficients
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.floorCoefficients
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.floorPolynomial
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.floorPolynomial
