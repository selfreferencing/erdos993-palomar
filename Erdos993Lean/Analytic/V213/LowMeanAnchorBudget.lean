module

public import Erdos993Lean.Analytic.V213.LowMeanBudgetFormula

/-!
The printed finite anchor set and calligraphic R(I).
Repeated anchors are removed by Finset, the fourth anchor is
omitted for M=0, and a positive exact maximum yields interval slack.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanAnchors (M : ℕ) (j : ℤ) (xi eta L H : ℝ) : Finset ℝ :=
  by
    classical
    exact ({L, H, (L + H) / 2} : Finset ℝ) ∪
      (if M = 0 then ∅ else {max L (min H (((j : ℝ) + xi / (2 * eta)) / M))})

theorem lowMeanAnchors_nonempty (M : ℕ) (j : ℤ) (xi eta L H : ℝ) :
    (lowMeanAnchors M j xi eta L H).Nonempty := by
  classical
  exact ⟨L, by simp [lowMeanAnchors]⟩

theorem lowMeanAnchors_in_interval (M : ℕ) (j : ℤ) (xi eta : ℝ)
    {L H tau : ℝ} (hLH : L ≤ H) (ht : tau ∈ lowMeanAnchors M j xi eta L H) :
    tau ∈ Set.Icc L H := by
  classical
  simp only [lowMeanAnchors, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with (rfl | rfl | rfl) | ht
  · exact ⟨le_rfl, hLH⟩
  · exact ⟨hLH, le_rfl⟩
  · constructor <;> linarith
  · split_ifs at ht with hM
    · simpa using ht
    · simp only [Finset.mem_singleton] at ht
      subst tau
      exact ⟨le_max_left _ _, max_le hLH (min_le_left _ _)⟩

noncomputable def lowMeanAnchorMaximum (M : ℕ) (j : ℤ) (xi eta L H : ℝ) (f : ℝ → ℝ) : ℝ :=
  by
    classical
    exact ((lowMeanAnchors M j xi eta L H).image f).max'
      ((lowMeanAnchors_nonempty M j xi eta L H).image f)

theorem lowMean_anchorMaximum_le (M : ℕ) (j : ℤ) (xi eta L H : ℝ) (f : ℝ → ℝ)
    {tau : ℝ} (ht : tau ∈ lowMeanAnchors M j xi eta L H) :
    f tau ≤ lowMeanAnchorMaximum M j xi eta L H f := by
  classical
  exact Finset.le_max' _ _ (Finset.mem_image_of_mem f ht)

theorem lowMean_anchorMaximum_positive_iff (M : ℕ) (j : ℤ) (xi eta L H : ℝ) (f : ℝ → ℝ) :
    0 < lowMeanAnchorMaximum M j xi eta L H f ↔
      ∃ tau ∈ lowMeanAnchors M j xi eta L H, 0 < f tau := by
  classical
  constructor
  · intro h
    have hm : lowMeanAnchorMaximum M j xi eta L H f ∈ (lowMeanAnchors M j xi eta L H).image f :=
      Finset.max'_mem _ _
    obtain ⟨tau, ht, he⟩ := Finset.mem_image.mp hm
    exact ⟨tau, ht, by simpa [he] using h⟩
  · rintro ⟨tau, ht, hp⟩
    exact lt_of_lt_of_le hp (lowMean_anchorMaximum_le M j xi eta L H f ht)

noncomputable def lowMeanBudgetMinimumAt (terms : List (ℝ × ℤ × ℤ)) (M : ℕ) (j : ℤ)
    (eta xi alpha beta gamma m0 zeta L H tau : ℝ) : ℝ :=
  lowMeanQuadMinimum (lowMeanBudgetA terms M eta L H) (lowMeanBudgetB terms M j eta xi L H tau)
    (lowMeanBudgetC terms M j eta xi alpha beta gamma m0 zeta L H tau) L H
noncomputable def lowMeanBestBudget (terms : List (ℝ × ℤ × ℤ)) (M : ℕ) (j : ℤ)
    (eta xi alpha beta gamma m0 zeta L H : ℝ) : ℝ :=
  lowMeanAnchorMaximum M j xi eta L H (lowMeanBudgetMinimumAt terms M j eta xi alpha beta gamma m0 zeta L H)

/-- The exact calligraphic R(I)>0 implication. No optimization assumption
or premise that asserts the desired slack is introduced. -/
theorem lowMean_bestBudget_positive_slack (terms : List (ℝ × ℤ × ℤ))
    {M : ℕ} {j : ℤ} {wL wR eta xi alpha beta gamma m0 z zeta L H : ℝ}
    (hL : 0 < L) (hH : H < 1) (hLH : L < H)
    (hterms : ∀ t ∈ terms, t.1 ≠ 0 ∧ 0 ≤ t.2.1 + t.2.2)
    (hidentity : ∀ q ∈ Set.Icc L H, kernel2 q wL wR M j + z * (1 - q) ^ M =
      (terms.map fun t => lowMeanMonomial t.1 t.2.1 t.2.2 q).sum)
    (hbest : 0 < lowMeanBestBudget terms M j eta xi alpha beta gamma m0 zeta L H)
    {q : ℝ} (hq : q ∈ Set.Icc L H) :
    zeta < lowMeanH q wL wR xi eta M j - lowMeanPsi alpha beta gamma m0 M + z * (1 - q) ^ M := by
  obtain ⟨tau, ht, hp⟩ := (lowMean_anchorMaximum_positive_iff M j xi eta L H
    (lowMeanBudgetMinimumAt terms M j eta xi alpha beta gamma m0 zeta L H)).mp hbest
  have htau := lowMeanAnchors_in_interval M j xi eta hLH.le ht
  apply lowMean_slack_positive_of_quadratic hLH hp ?_ hq
  intro p hpp
  rw [← lowMean_budget_coefficients]
  exact lowMean_slack_support terms hL hH hLH htau hpp hterms (hidentity p hpp)

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMean_bestBudget_positive_slack
