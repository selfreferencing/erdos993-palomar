module

public import Erdos993Lean.Analytic.V213.LowMeanAnchorBudget

/-!
Equation 60 uses both closed halves of Q. Their shared midpoint and both
outer endpoints are included, so successful half budgets cover all of Q.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

theorem lowMean_closed_halves {l h q : ℝ} (hq : q ∈ Set.Icc l h) :
    q ∈ Set.Icc l ((l + h) / 2) ∨ q ∈ Set.Icc ((l + h) / 2) h := by
  by_cases hm : q ≤ (l + h) / 2
  · exact Or.inl ⟨hq.1, hm⟩
  · exact Or.inr ⟨(lt_of_not_ge hm).le, hq.2⟩

theorem lowMean_closed_halves_union {l h : ℝ} (hlh : l ≤ h) :
    Set.Icc l ((l + h) / 2) ∪ Set.Icc ((l + h) / 2) h = Set.Icc l h := by
  ext q
  constructor
  · intro hq
    rcases hq with hq | hq
    · exact ⟨hq.1, by linarith [hq.2]⟩
    · exact ⟨by linarith [hq.1], hq.2⟩
  · exact lowMean_closed_halves

theorem lowMean_halves_lower_bound {l h bound : ℝ} {f : ℝ → ℝ}
    (hleft : ∀ q ∈ Set.Icc l ((l + h) / 2), bound ≤ f q)
    (hright : ∀ q ∈ Set.Icc ((l + h) / 2) h, bound ≤ f q)
    {q : ℝ} (hq : q ∈ Set.Icc l h) : bound ≤ f q := by
  rcases lowMean_closed_halves hq with hq | hq
  · exact hleft q hq
  · exact hright q hq

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMean_closed_halves_union
