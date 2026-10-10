module

public import Erdos993Lean.Analytic.V213.FiberReflection
public import Erdos993Lean.Analytic.V213.FiberKernel

/-!
Full-integer-axis reflection of the actual squared offset and bonus.
These identities
are stated before any reflected lower/upper-offset comparison is consumed.
The original q in every Laplace factor is untouched.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

theorem fiber_square_offset_reflect (q : ℝ) (M : ℕ) (j : ℤ) :
    fiberSquareOffset (1 - q) M ((M : ℤ) - j) = fiberSquareOffset q M j := by
  unfold fiberSquareOffset
  rw [fiber_offset_reflect, fiber_variance_reflect, neg_sq]

theorem fiber_bonus_reflect (q : ℝ) (M : ℕ) :
    fiberBonus (1 - q) M = fiberBonus q M := by
  unfold fiberBonus
  rw [fiber_skew_reflect, neg_sq]

theorem fiber_lower_offset_reflect (q : ℝ) (M : ℕ) (j : ℤ) :
    fiberSquareOffset (1 - q) M ((M : ℤ) - j) ≤ fiberBonus (1 - q) M ↔
      fiberSquareOffset q M j ≤ fiberBonus q M := by
  rw [fiber_square_offset_reflect, fiber_bonus_reflect]

theorem fiber_upper_offset_reflect (q : ℝ) (M : ℕ) (j : ℤ) :
    fiberBonus (1 - q) M ≤ fiberSquareOffset (1 - q) M ((M : ℤ) - j) ↔
      fiberBonus q M ≤ fiberSquareOffset q M j := by
  rw [fiber_square_offset_reflect, fiber_bonus_reflect]

end Erdos993Lean.Analytic.V213
