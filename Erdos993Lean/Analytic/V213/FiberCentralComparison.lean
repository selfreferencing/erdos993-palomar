module

public import Erdos993Lean.Analytic.V213.FiberUniversalUpper
public import Erdos993Lean.Analytic.V213.FiberLowerComparison
public import Erdos993Lean.Analytic.V213.FiberPointwiseReflection

/-!
Literal central fiber comparison Theorem6.14.
Every natural width and integer rank is retained. The printed mean/ratio
guards imply the upper-comparison width cutoff; both offset ranges and
the closed full q interval are proved. Pointwise reflection leaves the
original q in later Laplace expectations unchanged.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

theorem fiber_central_comparison_nonnegative_skew {q mu : ℝ}
    (hq0 : 1 / 2 ≤ q) (hqh : q ≤ 3 / 4) (hmu : 19 ≤ mu) (M : ℕ)
    (ht : 3 / 5 ≤ (M : ℝ) / mu) (j : ℤ) :
    fiberPsi ((M : ℝ) / mu) ≤ fiberF q mu M j := by
  have hmu0 : 0 < mu := by linarith
  by_cases hw : fiberSquareOffset q M j ≤ fiberBonus q M
  · have hl := fiber_lower_offset_comparison hmu hq0 hqh M j hw
    have hp : 0 ≤ 1 / (4 * mu) := by positivity
    linarith only [hl, hp]
  · have hM := fiber_lower_integer_width hmu ht
    exact fiber_universal_upper_comparison (by omega : 8 ≤ M) hq0 hqh hmu0 j
      (le_of_lt (lt_of_not_ge hw)) ht

theorem fiber_central_comparison {q mu : ℝ}
    (hql : 1 / 4 ≤ q) (hqh : q ≤ 3 / 4) (hmu : 19 ≤ mu) (M : ℕ)
    (ht : 3 / 5 ≤ (M : ℝ) / mu) (j : ℤ) :
    fiberPsi ((M : ℝ) / mu) ≤ fiberF q mu M j := by
  by_cases hq0 : 1 / 2 ≤ q
  · exact fiber_central_comparison_nonnegative_skew hq0 hqh hmu M ht j
  · have hqr0 : 1 / 2 ≤ 1 - q := by linarith
    have hqrh : 1 - q ≤ 3 / 4 := by linarith
    have hr := fiber_central_comparison_nonnegative_skew hqr0 hqrh hmu M ht ((M : ℤ) - j)
    rw [fiber_F_reflect] at hr
    exact hr

end Erdos993Lean.Analytic.V213
