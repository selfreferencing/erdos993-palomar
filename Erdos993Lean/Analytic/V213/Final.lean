module

public import Erdos993Lean.Analytic.V213.FinalInputs
public import Erdos993Lean.Analytic.V213.FinalParameterDomain
public import Erdos993Lean.Analytic.V213.FinalForestFacts
public import Erdos993Lean.Analytic.V213.FreeCountVarianceClosedAssembly
public import Erdos993Lean.Analytic.V213.ZeroTiltLaplaceClosedForest
public import Erdos993Lean.Analytic.V213.SmallForestTheorem
public import Erdos993Lean.Analytic.Window

/-! Printed Theorem 2.9 and the final consumer, assembled from the merged
Theorems 2.7 and 5.1, with all numeric and forest interfaces discharged. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

/-- Theorem 2.9 from Theorems 2.7 and 5.1; all mixture and window inputs
are actual proved forest statements; both numerical inputs are discharged. -/
theorem theorem29
    (F : FiniteForest) : independenceSequenceUnimodal F := by
  by_cases hn : F.n ≤ 24
  · exact SmallForest.small_forest_independenceSequenceUnimodal F hn
  · have hn25 : 25 ≤ F.n := by omega
    apply window_reduction F
    intro z hz hv
    have hz0 : 0 ≤ z := by have := hz.1; omega
    let k := z.toNat
    have hkz : (k : ℤ) = z := Int.toNat_of_nonneg hz0
    have hklo : (F.n + 3) / 4 < k := by have := hz.1; omega
    have hkhi : k < hB F := by have := hz.2; omega
    obtain ⟨lam, hlamlo, hlamhi, hmean⟩ := exists_activity_eq F k hklo hkhi
    have hlam : 0 < lam := by linarith
    obtain ⟨A, hA⟩ := HardCore.exists_isMaxWeight F lam
    obtain ⟨i, hi, hsel⟩ := lowMean_selected_activity_cover ⟨hlamlo.le, hlamhi.le⟩
    have hinterval : lam ∈ Set.Icc (N44.Data.pieceLo.getD i 0 : ℝ)
        (N44.Data.pieceHi.getD i 0 : ℝ) := by
      refine ⟨?_, hsel.2⟩
      rcases hsel.1 with hfirst | hstrict
      · exact hfirst.2
      · exact hstrict.le
    have heq := forest_equation23 F A hlam hA k hmean
    have hlow := (lemma25_lower_edge F hn25 k hklo hkhi hlamlo hlamhi hmean A hA).2
    have hvM := (FreeCountVariance.Closed.maxWeight_variances_Dhat F hlamlo.le hlamhi.le hA).2
    have hvK := theorem51_input F i hi hinterval A hA
    have hd2 : (forestMixture F A lam).expect
        (fun M Y => delta (FreeCountVariance.q lam) k M Y ^ 2) ≤
        lowMeanFractionReal (lowMeanInputRowAt i).theta *
          (FreeCountVariance.q lam * (1 - FreeCountVariance.q lam)) *
            (forestMixture F A lam).meanM := by
      rw [heq.2.1]
      rw [← heq.2.2] at hvK
      nlinarith [hvK]
    have htail := ZeroTiltLaplace.current_forest_laplace_maxWeight F A
      ⟨hlamlo.le, hlamhi.le⟩ hA
    have hno := theorem28_Dhat i hi (forestMixture F A lam) (k : ℤ)
      hinterval hlow (HardCore.forestMixture_isProb F hA.1 hlam) rfl heq.1 hvM hd2 htail
    have hvk : CoefficientValley F (k : ℤ) := by simpa only [hkz] using hv
    exact hno (forest_valley_transfer F A hlam hA k hvk)

/-- Every finite forest has a unimodal independence sequence, with no extra hypothesis. -/
theorem erdos993_v213_final : Erdos993Statement := theorem29

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.theorem29
#print axioms Erdos993Lean.Analytic.V213.erdos993_v213_final
