module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceAssembly
public import Erdos993Lean.Analytic.V213.FreeCountCAClosedCaps

/-! Closed assembly of the Section 3 variance bound.
This is separate from the frozen conditional graph assembly. It supplies
all five analytic hypotheses using the actual closed-cap comparisons.
Neither a completed old curve nor an unproved current-paper assertion is
an input. The graph conclusions are for every finite forest, with no size
or interior-rank restriction; the Profile wrapper only weakens this domain.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance.Closed

open Finset

theorem cap_stepCert {c : Cap} {lam : ℝ} (hc : c.Contains lam) :
    Reserve.StepCert (gamma c.value lam) lam (alpha c.value lam) 0 (capA c.value lam) :=
  cap_stepCert_of_feasible_comparisons hc
    (fun _ _ ht hy => (Finite.comparisons_on_cap hc ht hy).1)
    (fun _ _ ht hy => (Finite.comparisons_on_cap hc ht hy).2.1)
    (fun _ _ ht hy => (Finite.comparisons_on_cap hc ht hy).2.2.1)
    (fun _ _ ht hy => (Finite.comparisons_on_cap hc ht hy).2.2.2.1.le)
    (fun _ _ ht hy => (Finite.comparisons_on_cap hc ht hy).2.2.2.2.le)

/-- Both variance conclusions for any independent set with the leaf property. -/
theorem forest_variances {c : Cap} {lam : ℝ} (hc : c.Contains lam)
    (F : FiniteForest) {B : Finset (Fin F.n)}
    (hB : F.graph.IsIndepSet (B : Set (Fin F.n))) (hleaf : Reserve.LeafProp F.graph B) :
    HardCore.varKB F lam B ≤ capA c.value lam*weightW F lam B ∧
      (forestMixture F B lam).varM ≤ c.value*(forestMixture F B lam).meanM :=
  forest_variances_le_closed_cap hc
    (fun _ _ ht hy => (Finite.comparisons_on_cap hc ht hy).1)
    (fun _ _ ht hy => (Finite.comparisons_on_cap hc ht hy).2.1)
    (fun _ _ ht hy => (Finite.comparisons_on_cap hc ht hy).2.2.1)
    (fun _ _ ht hy => (Finite.comparisons_on_cap hc ht hy).2.2.2.1.le)
    (fun _ _ ht hy => (Finite.comparisons_on_cap hc ht hy).2.2.2.2.le)
    F hB hleaf

/-- Maximum marginal weight supplies the leaf property, including components
with no selected vertex and the isolated-vertex case through the graph proof. -/
theorem maxWeight_variances {c : Cap} {lam : ℝ} (hc : c.Contains lam)
    (F : FiniteForest) {B : Finset (Fin F.n)} (hB : IsMaxWeight F lam B) :
    HardCore.varKB F lam B ≤ capA c.value lam*weightW F lam B ∧
      (forestMixture F B lam).varM ≤ c.value*(forestMixture F B lam).meanM :=
  forest_variances hc F hB.1 (Reserve.leafProp_of_isMaxWeight F (Cap.activity_pos hc) hB)

/-- The literal current left-selected curve, including every seam and both
endpoints. No continuity or agreement of neighboring cap values is assumed. -/
theorem forest_variances_Dhat (F : FiniteForest) {lam : ℝ}
    (hlam : (1/3 : ℝ) ≤ lam) (hlam7 : lam ≤ 7/3) {B : Finset (Fin F.n)}
    (hB : F.graph.IsIndepSet (B : Set (Fin F.n))) (hleaf : Reserve.LeafProp F.graph B) :
    HardCore.varKB F lam B ≤ (1+(Dhat lam-1)*q lam)*weightW F lam B ∧
      (forestMixture F B lam).varM ≤ Dhat lam*(forestMixture F B lam).meanM := by
  have hh := forest_variances (selectedCap_contains hlam hlam7) F hB hleaf
  simpa only [Dhat,capA] using hh

theorem maxWeight_variances_Dhat (F : FiniteForest) {lam : ℝ}
    (hlam : (1/3 : ℝ) ≤ lam) (hlam7 : lam ≤ 7/3) {B : Finset (Fin F.n)}
    (hB : IsMaxWeight F lam B) :
    HardCore.varKB F lam B ≤ (1+(Dhat lam-1)*q lam)*weightW F lam B ∧
      (forestMixture F B lam).varM ≤ Dhat lam*(forestMixture F B lam).meanM :=
  forest_variances_Dhat F hlam hlam7 hB.1
    (Reserve.leafProp_of_isMaxWeight F (by linarith) hB)

/-- Only the Db field is supplied here. No assertion about any other open
profile field, or any inherited numerical profile, is made. -/
noncomputable def withCurrentDhat (P : Profile) : Profile := { P with Db := Dhat }

/-- An assumption-free variance-field adapter: the selected current Db is
installed explicitly, so no last profile-equality hypothesis is hidden. -/
theorem varianceBound_currentProfile (P : Profile) : VarianceBound (withCurrentDhat P) := by
  intro F _ lam hlam _ B hB
  simpa only [withCurrentDhat] using
    (maxWeight_variances_Dhat F hlam.1 hlam.2 hB).2

end Erdos993Lean.Analytic.V213.FreeCountVariance.Closed

#check Erdos993Lean.Analytic.V213.FreeCountVariance.Closed.cap_stepCert
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Closed.cap_stepCert
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Closed.forest_variances
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Closed.forest_variances
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Closed.maxWeight_variances
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Closed.maxWeight_variances
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Closed.forest_variances_Dhat
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Closed.forest_variances_Dhat
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Closed.maxWeight_variances_Dhat
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Closed.maxWeight_variances_Dhat
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Closed.varianceBound_currentProfile
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Closed.varianceBound_currentProfile
