module

public import Erdos993Lean.Analytic.V213.Foundation
public import Erdos993Lean.Analytic.TopCore

/-!
Window component: Lemma 2.2 of version 2.13 of the manuscript (r12:lem2).
The inherited prefix/normalized-matching/window theorem is used.
The new wrapper preserves the paper's
integer window and equality-inclusive valley definition. No occupation
theorem or old first-mode estimate is used in this proof.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

/-- The paper's integer-window hypothesis gives the globally unimodal
zero-extended natural coefficient sequence. -/
theorem window_reduction_unimodal (F : FiniteForest)
    (hno : ∀ k : ℤ, WindowRank F k → ¬ CoefficientValley F k) :
    Unimodal (independenceCount F) := by
  apply Erdos993Lean.Analytic.unimodal_of_noWeakValley_window F
  intro k hlow hhigh hvalley
  have hk : 1 ≤ k := by omega
  have hwindow : WindowRank F (k : ℤ) := by
    constructor
    · exact_mod_cast hlow
    · exact_mod_cast hhigh
  apply hno (k : ℤ) hwindow
  refine ⟨by exact_mod_cast hk, ?_, ?_⟩
  · have hpred : (k : ℤ) - 1 = ((k - 1 : ℕ) : ℤ) := by omega
    simpa only [hpred, coefficient_nat] using hvalley.1
  · have hsucc : (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) := by omega
    simpa only [hsucc, coefficient_nat] using hvalley.2

/-- Lemma 2.2 of version 2.13 of the manuscript: the independence sequence is unimodal if its open
integer window contains no valley. -/
theorem window_reduction (F : FiniteForest)
    (hno : ∀ k : ℤ, WindowRank F k → ¬ CoefficientValley F k) :
    independenceSequenceUnimodal F := by
  exact unimodalUpTo_of_unimodal (window_reduction_unimodal F hno)

end Erdos993Lean.Analytic.V213

#check Erdos993Lean.Analytic.V213.window_reduction_unimodal
#print axioms Erdos993Lean.Analytic.V213.window_reduction_unimodal
#check Erdos993Lean.Analytic.V213.window_reduction
#print axioms Erdos993Lean.Analytic.V213.window_reduction

