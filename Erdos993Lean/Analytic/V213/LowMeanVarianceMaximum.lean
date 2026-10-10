module

public import Erdos993Lean.Analytic.V213.LowMeanRate

/-!
Exact variance maximum v_Q on the printed closed interval. The value
is attained and dominates every q(1-q) on Q, including intervals meeting or
crossing one half. This supplies the exact v used by all finite formulas.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanVarianceMaximum (l h : ℝ) : ℝ :=
  if l ≤ 1 / 2 ∧ 1 / 2 ≤ h then 1 / 4 else max (l * (1 - l)) (h * (1 - h))

theorem lowMean_varianceMaximum_bound {l h q : ℝ} (hq : q ∈ Set.Icc l h) :
    q * (1 - q) ≤ lowMeanVarianceMaximum l h := by
  unfold lowMeanVarianceMaximum
  split_ifs with hc
  · nlinarith [sq_nonneg (q - 1 / 2)]
  · by_cases hl : l ≤ 1 / 2
    · have hh : h < 1 / 2 := lt_of_not_ge (fun hh => hc ⟨hl, hh⟩)
      apply le_trans (show q * (1 - q) ≤ h * (1 - h) by nlinarith [hq.1, hq.2])
        (le_max_right _ _)
    · have hh : 1 / 2 < l := lt_of_not_ge hl
      apply le_trans (show q * (1 - q) ≤ l * (1 - l) by nlinarith [hq.1, hq.2])
        (le_max_left _ _)

theorem lowMean_varianceMaximum_attained {l h : ℝ} (hlh : l ≤ h) :
    ∃ q ∈ Set.Icc l h, q * (1 - q) = lowMeanVarianceMaximum l h := by
  unfold lowMeanVarianceMaximum
  split_ifs with hc
  · exact ⟨1 / 2, hc, by norm_num⟩
  · by_cases he : l * (1 - l) ≤ h * (1 - h)
    · exact ⟨h, ⟨hlh, le_rfl⟩, (max_eq_right he).symm⟩
    · exact ⟨l, ⟨le_rfl, hlh⟩, (max_eq_left (le_of_not_ge he)).symm⟩

/-- The printed maximum, expressed as a greatest element of the image. -/
theorem lowMean_varianceMaximum_exact {l h : ℝ} (hlh : l ≤ h) :
    IsGreatest ((fun q : ℝ => q * (1 - q)) '' Set.Icc l h) (lowMeanVarianceMaximum l h) := by
  obtain ⟨q, hq, he⟩ := lowMean_varianceMaximum_attained hlh
  refine ⟨⟨q, hq, he⟩, ?_⟩
  intro y hy
  obtain ⟨q, hq, rfl⟩ := hy
  exact lowMean_varianceMaximum_bound hq

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMean_varianceMaximum_exact
