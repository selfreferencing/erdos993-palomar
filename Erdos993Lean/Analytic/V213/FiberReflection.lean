module

public import Erdos993Lean.Analytic.V213.FiberDefinitions
public import Erdos993Lean.Analytic.V213.LowMeanKernelIdentities

/-!
Source reflection, on the entire integer rank
axis. The pointwise weighted kernel and F reflect; no Laplace factor is altered.
The exact all-integer binomial identity is reused from the low-mean modules.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

theorem fiber_variance_reflect (q : ℝ) : fiberVariance (1 - q) = fiberVariance q := by
  unfold fiberVariance
  ring

theorem fiber_skew_reflect (q : ℝ) : fiberSkew (1 - q) = -fiberSkew q := by
  unfold fiberSkew
  ring

theorem fiber_weights_reflect (q : ℝ) :
    fiberWeightL (1 - q) = fiberWeightR q ∧ fiberWeightR (1 - q) = fiberWeightL q := by
  unfold fiberWeightL fiberWeightR
  constructor <;> ring

theorem fiber_offset_reflect (q : ℝ) (M : ℕ) (j : ℤ) :
    fiberOffset (1 - q) M ((M : ℤ) - j) = -fiberOffset q M j := by
  unfold fiberOffset fiberSkew
  push_cast
  ring

theorem fiber_normalization_reflect (q mu : ℝ) :
    fiberNormalization (1 - q) mu = fiberNormalization q mu := by
  unfold fiberNormalization
  rw [fiber_variance_reflect]

theorem fiber_kernel_reflect (q : ℝ) (M : ℕ) (j : ℤ) :
    kernel2 (1 - q) (fiberWeightL (1 - q)) (fiberWeightR (1 - q)) M ((M : ℤ) - j) =
      kernel2 q (fiberWeightL q) (fiberWeightR q) M j := by
  rw [(fiber_weights_reflect q).1, (fiber_weights_reflect q).2]
  exact lowMean_kernel_reflect M q (fiberWeightL q) (fiberWeightR q) j

theorem fiber_F_reflect (q mu : ℝ) (M : ℕ) (j : ℤ) :
    fiberF (1 - q) mu M ((M : ℤ) - j) = fiberF q mu M j := by
  unfold fiberF
  rw [fiber_normalization_reflect, fiber_kernel_reflect, fiber_offset_reflect,
      fiber_variance_reflect, neg_sq]

end Erdos993Lean.Analytic.V213
