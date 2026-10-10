module

public import Erdos993Lean.Analytic.V213.ZeroTiltLaplaceUnitClosure
public import Erdos993Lean.Analytic.V213.ZeroTiltLaplaceFiniteSigns
public import Erdos993Lean.Analytic.V213.ZeroTiltLaplaceJoiningFinite
public import Erdos993Lean.Analytic.V213.ZeroTiltLaplaceRateFinite
public import Erdos993Lean.Analytic.V213.ZeroTiltLaplaceSingleSumForest
public import Erdos993Lean.Analytic.HardCore.Moments
public import Erdos993Lean.Analytic.HardCore.Mixture

/-! Unconditional current unit and forest conclusions after the complete
literal finite layer. No variance estimate, activity-fixed choice of A,
or inherited completed Laplace theorem is used. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace

/-- All analytic and finite premises of the new unit proof are discharged. -/
theorem current_unit_nonnegative {lam : ℝ} (hlam : ActivityDomain lam) :
    UnitNonnegative lam :=
  unit_nonnegative_of_signs FinitePolynomial.current_polynomial_signs
    FinitePolynomial.current_center_joins hlam

/-- The stronger leaf-compatible independent-set scope of the actual
single-sum proof; the printed theorem's maximum-weight scope follows below. -/
theorem current_forest_laplace_leaf (F : FiniteForest) (A : Finset (Fin F.n))
    (hA : F.graph.IsIndepSet (A : Set (Fin F.n)))
    (hleaf : Tail.LeafCondition F.graph A) {lam : ℝ} (hlam : ActivityDomain lam) :
    (forestMixture F A lam).expect (fun M _ => (1-q lam)^M)≤
      Real.exp (-ellH lam*(forestMixture F A lam).meanM) :=
  single_sum_forest_conditional F A hA hleaf hlam (current_unit_nonnegative hlam)

theorem current_forest_laplace_maxWeight (F : FiniteForest) (A : Finset (Fin F.n))
    {lam : ℝ} (hlam : ActivityDomain lam) (hA : IsMaxWeight F lam A) :
    (forestMixture F A lam).expect (fun M _ => (1-q lam)^M)≤
      Real.exp (-ellH lam*(forestMixture F A lam).meanM) :=
  single_sum_maxWeight_conditional F A hlam hA (current_unit_nonnegative hlam)

theorem forest_meanM_nonneg (F : FiniteForest) (A : Finset (Fin F.n))
    (hA : F.graph.IsIndepSet (A : Set (Fin F.n))) {lam : ℝ} (hlam : 0<lam) :
    0≤(forestMixture F A lam).meanM := by
  have hp := HardCore.forestMixture_isProb (F:=F) hA hlam
  exact Mixture.expect_nonneg _ hp.1 (fun _ _ => Nat.cast_nonneg _)

theorem retained_exponential_comparison (F : FiniteForest) (A : Finset (Fin F.n))
    (hA : F.graph.IsIndepSet (A : Set (Fin F.n))) {i : Nat} (hi : i<55) {lam : ℝ}
    (hlo : (N44.Data.pieceLo.getD i 0:ℝ)≤lam)
    (hhi : lam≤(N44.Data.pieceHi.getD i 0:ℝ)) :
    Real.exp (-ellH lam*(forestMixture F A lam).meanM)≤
      Real.exp (-((N44.Data.rates44.getD i []).getD 0 0:ℝ)*(forestMixture F A lam).meanM) := by
  have hd := PrintedRates.input_interval_domain hi hlo hhi
  have hm := forest_meanM_nonneg F A hA (lam:=lam) (by linarith only [hd.1])
  have hr := PrintedRates.retained_input_rate_le hi hlo hhi
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right (neg_le_neg hr) hm

/-- Literal current Theorem4.1, both inequalities, on each of the55 exact
retained input intervals. All endpoints are closed, and the maximum-weight
set is chosen at the given activity; no choice is held fixed across activities. -/
theorem current_forest_two_laplace_bounds (F : FiniteForest) (A : Finset (Fin F.n))
    {i : Nat} (hi : i<55) {lam : ℝ}
    (hlo : (N44.Data.pieceLo.getD i 0:ℝ)≤lam)
    (hhi : lam≤(N44.Data.pieceHi.getD i 0:ℝ)) (hA : IsMaxWeight F lam A) :
    (forestMixture F A lam).expect (fun M _ => (1-q lam)^M)≤
        Real.exp (-ellH lam*(forestMixture F A lam).meanM) ∧
      Real.exp (-ellH lam*(forestMixture F A lam).meanM)≤
        Real.exp (-((N44.Data.rates44.getD i []).getD 0 0:ℝ)*(forestMixture F A lam).meanM) :=
  ⟨current_forest_laplace_maxWeight F A (PrintedRates.input_interval_domain hi hlo hhi) hA,
    retained_exponential_comparison F A hA.1 hi hlo hhi⟩

end Erdos993Lean.Analytic.V213.ZeroTiltLaplace

#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.current_unit_nonnegative
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.current_unit_nonnegative
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.current_forest_laplace_leaf
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.current_forest_laplace_leaf
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.current_forest_laplace_maxWeight
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.current_forest_laplace_maxWeight
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.forest_meanM_nonneg
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.forest_meanM_nonneg
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.retained_exponential_comparison
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.retained_exponential_comparison
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.current_forest_two_laplace_bounds
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.current_forest_two_laplace_bounds
