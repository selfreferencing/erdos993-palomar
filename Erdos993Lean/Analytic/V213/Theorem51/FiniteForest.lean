module

public import Erdos993Lean.Analytic.V213.Theorem51.Statements
public import Erdos993Lean.Analytic.HardCore.Basic
public import Erdos993Lean.Analytic.Reserve.Moments
public import Erdos993Lean.Analytic.Tail.Fallback

/-! Theorem 5.1 in the earlier finite-forest vocabulary. The identities below hold for
all real activities; only the final row bound consumes `AllRowsVarianceRatio`. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.Theorem51

open Finset Tail Reserve O2

theorem isIndepSet_iff_isIndepFinset (F : FiniteForest) (B : Finset (Fin F.n)) :
    F.graph.IsIndepSet (B : Set (Fin F.n)) ↔ IsIndepFinset F.graph B :=
  HardCore.isIndepSet_coe_iff F

section Identities

variable (F : FiniteForest) [DecidableRel F.graph.Adj]

/-- On the full vertex set the selected count is the cardinality of the independent set. -/
theorem momB_univ_card (t : ℝ) (k : ℕ) :
    momB F.graph univ t k univ =
      ∑ S ∈ indepSets F, (S.card : ℝ) ^ k * t ^ S.card := by
  unfold momB
  rw [← Tail.indepSets_eq F]
  simp only [Finset.inter_univ]

theorem meanB_univ_eq_hardCoreMean (t : ℝ) :
    meanB F.graph univ t univ = hardCoreMean F t := by
  rw [meanB, momB_univ_card, momB_univ_card, HardCore.hardCoreMean_eq_sum,
    HardCore.partitionFn_eq_sum]
  simp only [pow_one, pow_zero, one_mul]

/-- Centered and raw second moments agree, including the total-division case `Z = 0`. -/
theorem hardCoreVar_eq_varB (t : ℝ) :
    hardCoreVar F t = varB F.graph univ t univ := by
  have hexp :
      (∑ S ∈ indepSets F, ((S.card : ℝ) - hardCoreMean F t) ^ 2 * t ^ S.card) =
        (∑ S ∈ indepSets F, (S.card : ℝ) ^ 2 * t ^ S.card) -
          2 * hardCoreMean F t * (∑ S ∈ indepSets F, (S.card : ℝ) * t ^ S.card) +
          hardCoreMean F t ^ 2 * (∑ S ∈ indepSets F, t ^ S.card) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun S _ => ?_
    ring
  rw [HardCore.hardCoreVar_eq_sum, hexp, varB, meanB_univ_eq_hardCoreMean,
    momB_univ_card, momB_univ_card]
  simp only [pow_zero, one_mul]
  simp only [← HardCore.partitionFn_eq_sum F t, HardCore.hardCoreMean_eq_sum F t]
  by_cases hZ : partitionFn F t = 0
  · simp [hZ]
  · field_simp [hZ] <;> ring

theorem marginal_eq_gMarg (t : ℝ) (v : Fin F.n) :
    marginal F t v = gMarg F.graph t v := by
  rw [Tail.marginal_eq_marg, Tail.marg_of_mem (Finset.mem_univ v)]
  rfl

theorem weightW_eq_sum_gMarg (t : ℝ) (B : Finset (Fin F.n)) :
    weightW F t B = ∑ v ∈ B, gMarg F.graph t v := by
  unfold weightW
  exact Finset.sum_congr rfl fun v _ => marginal_eq_gMarg F t v

/-- Both maximum-weight predicates range over the same independent subsets and weights. -/
theorem isMaxWeight_iff (t : ℝ) (B : Finset (Fin F.n)) :
    IsMaxWeight F t B ↔
      IsIndepFinset F.graph B ∧
        ∀ C : Finset (Fin F.n), IsIndepFinset F.graph C →
          (∑ v ∈ C, gMarg F.graph t v) ≤ ∑ v ∈ B, gMarg F.graph t v := by
  constructor
  · intro h
    refine ⟨(isIndepSet_iff_isIndepFinset F B).1 h.1, ?_⟩
    intro C hC
    simpa only [weightW_eq_sum_gMarg] using
      h.2 C ((isIndepSet_iff_isIndepFinset F C).2 hC)
  · rintro ⟨hB, hmax⟩
    refine ⟨(isIndepSet_iff_isIndepFinset F B).2 hB, ?_⟩
    intro C hC
    simpa only [weightW_eq_sum_gMarg] using
      hmax C ((isIndepSet_iff_isIndepFinset F C).1 hC)

end Identities

/-- The actual all-row statement transfers to the original `FiniteForest` vocabulary. -/
theorem finiteForest_variance_ratio_of_allRows (hAll : AllRowsVarianceRatio.{0})
    (F : FiniteForest) {r : TableRow} {t : ℝ} (hrow : InTableRow r t)
    (B : Finset (Fin F.n)) (hB : IsMaxWeight F t B) :
    hardCoreVar F t ≤ (gammaTheta r / (1 + t)) * weightW F t B := by
  classical
  obtain ⟨hBi, hmax⟩ := (isMaxWeight_iff F t B).1 hB
  rw [hardCoreVar_eq_varB F t, weightW_eq_sum_gMarg F t B]
  exact hAll (Fin F.n) F.graph F.isForest r t hrow B hBi hmax

/-- Maximum-weight witnesses exist; the adapter has no extra existence premise. -/
theorem finiteForest_exists_variance_ratio_of_allRows (hAll : AllRowsVarianceRatio.{0})
    (F : FiniteForest) {r : TableRow} {t : ℝ} (hrow : InTableRow r t) :
    ∃ B : Finset (Fin F.n), IsMaxWeight F t B ∧
      hardCoreVar F t ≤ (gammaTheta r / (1 + t)) * weightW F t B := by
  obtain ⟨B, hB⟩ := HardCore.exists_isMaxWeight F t
  exact ⟨B, hB, finiteForest_variance_ratio_of_allRows hAll F hrow B hB⟩

end Erdos993Lean.Analytic.V213.Theorem51

#check Erdos993Lean.Analytic.V213.Theorem51.hardCoreVar_eq_varB
#print axioms Erdos993Lean.Analytic.V213.Theorem51.hardCoreVar_eq_varB
#check Erdos993Lean.Analytic.V213.Theorem51.isIndepSet_iff_isIndepFinset
#print axioms Erdos993Lean.Analytic.V213.Theorem51.isIndepSet_iff_isIndepFinset
#check Erdos993Lean.Analytic.V213.Theorem51.weightW_eq_sum_gMarg
#print axioms Erdos993Lean.Analytic.V213.Theorem51.weightW_eq_sum_gMarg
#check Erdos993Lean.Analytic.V213.Theorem51.isMaxWeight_iff
#print axioms Erdos993Lean.Analytic.V213.Theorem51.isMaxWeight_iff
#check Erdos993Lean.Analytic.V213.Theorem51.finiteForest_variance_ratio_of_allRows
#print axioms Erdos993Lean.Analytic.V213.Theorem51.finiteForest_variance_ratio_of_allRows
#check Erdos993Lean.Analytic.V213.Theorem51.finiteForest_exists_variance_ratio_of_allRows
#print axioms Erdos993Lean.Analytic.V213.Theorem51.finiteForest_exists_variance_ratio_of_allRows
