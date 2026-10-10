module

public import Erdos993Lean.Analytic.V213.Theorem51.FiveRows
public import Erdos993Lean.Analytic.V213.Theorem51.HalfLight
public import Erdos993Lean.Analytic.V213.Theorem51.HeavyForest
public import Erdos993Lean.Analytic.V213.Theorem51.NonVacuity
public import Erdos993Lean.Analytic.V213.Theorem51.FiniteForest
public import Erdos993Lean.F4U.AssemblyA.Local
public import F4Heavy.Targets
public import F4Heavy.TargetsRegional

/-! Theorem 5.1 on every original Table 1 row. The only unresolved mathematical
input is exactly the frozen contract's light core for its four heavy rows. -/

@[expose] public section

universe u

namespace Erdos993Lean.Analytic.V213.Theorem51

open Finset Erdos993Lean.Analytic Tail Reserve O2 VarianceResponse

theorem heavy_localEvidence
    (hLight : ∀ r : F4Unified.Row, F4Unified.LightCore r) (r : F4Unified.Row) :
    F4Unified.LocalEvidence r :=
  ⟨halfLight r, F4Heavy.fixedParentCap_all r, hLight r,
    F4Heavy.compactHeavy_all r, F4Heavy.tailPositive_all r⟩

theorem heavy_pairPositive
    (hLight : ∀ r : F4Unified.Row, F4Unified.LightCore r) (r : F4Unified.Row) :
    F4Unified.PairPositive r :=
  F4Unified.Assembly.pairPositive_of_localEvidence r (heavy_localEvidence hLight r)

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

theorem heavy_forest_variance_bound
    (hLight : ∀ r : F4Unified.Row, F4Unified.LightCore r)
    (hG : G.IsAcyclic) {r : F4Unified.Row} {lam : ℝ} (hrow : F4Unified.InRow r lam)
    (A : Finset V) (hA : IsIndepFinset G A)
    (hmax : ∀ B : Finset V, IsIndepFinset G B →
      (∑ v ∈ B, gMarg G lam v) ≤ ∑ v ∈ A, gMarg G lam v) :
    varB G univ lam univ ≤ ((F4Unified.rowData r).price/(1+lam))*
      ∑ v ∈ A, gMarg G lam v :=
  heavy_forest_variance_bound_of_pairPositive (heavy_pairPositive hLight r)
    (F4Heavy.leafPositive_all r) hG hrow A hA hmax

theorem variance_ratio_bound_heavy_rows
    (hLight : ∀ r : F4Unified.Row, F4Unified.LightCore r)
    (hG : G.IsAcyclic) (r : F4Unified.Row) {lam : ℝ}
    (hrow : InTableRow (tableRowOfHeavy r) lam)
    (A : Finset V) (hA : IsIndepFinset G A)
    (hmax : ∀ B : Finset V, IsIndepFinset G B →
      (∑ v ∈ B, gMarg G lam v) ≤ ∑ v ∈ A, gMarg G lam v) :
    varB G univ lam univ ≤ (gammaTheta (tableRowOfHeavy r)/(1+lam))*
      ∑ v ∈ A, gMarg G lam v := by
  rw [heavy_gammaTheta_eq]
  exact heavy_forest_variance_bound hLight hG ((heavy_inTableRow_iff r lam).1 hrow)
    A hA hmax

/-- The variance-ratio bound for all nine original rows and actual finite forests. -/
theorem variance_ratio_bound_all_rows
    (hLight : ∀ r : F4Unified.Row, F4Unified.LightCore r)
    (hG : G.IsAcyclic) {r : TableRow} {lam : ℝ} (hrow : InTableRow r lam)
    (A : Finset V) (hA : IsIndepFinset G A)
    (hmax : ∀ B : Finset V, IsIndepFinset G B →
      (∑ v ∈ B, gMarg G lam v) ≤ ∑ v ∈ A, gMarg G lam v) :
    varB G univ lam univ ≤ (gammaTheta r/(1+lam))*∑ v ∈ A, gMarg G lam v := by
  cases r with
  | A => exact variance_ratio_bound_five_rows hG (Or.inl rfl) hrow A hA hmax
  | B => exact variance_ratio_bound_five_rows hG (Or.inr (Or.inl rfl)) hrow A hA hmax
  | C => exact variance_ratio_bound_five_rows hG (Or.inr (Or.inr (Or.inl rfl))) hrow A hA hmax
  | D => exact variance_ratio_bound_heavy_rows hLight hG .D hrow A hA hmax
  | E1 => exact variance_ratio_bound_heavy_rows hLight hG .E1 hrow A hA hmax
  | E2 => exact variance_ratio_bound_heavy_rows hLight hG .E2 hrow A hA hmax
  | F => exact variance_ratio_bound_five_rows hG (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hrow A hA hmax
  | G => exact variance_ratio_bound_five_rows hG (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hrow A hA hmax
  | H => exact variance_ratio_bound_heavy_rows hLight hG .H hrow A hA hmax

theorem allRowsVarianceRatio
    (hLight : ∀ r : F4Unified.Row, F4Unified.LightCore r) : AllRowsVarianceRatio.{u} := by
  intro V _ _ G _ hG r lam hrow A hA hmax
  exact variance_ratio_bound_all_rows hLight hG hrow A hA hmax

theorem exists_independent_variance_ratio_bound
    (hLight : ∀ r : F4Unified.Row, F4Unified.LightCore r)
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsAcyclic)
    {r : TableRow} {lam : ℝ} (hrow : InTableRow r lam) :
    ∃ A : Finset V, IsIndepFinset G A ∧
      varB G univ lam univ ≤ (gammaTheta r/(1+lam))*∑ v ∈ A, gMarg G lam v :=
  exists_independent_variance_bound (allRowsVarianceRatio hLight) G hG hrow

theorem finiteForest_variance_ratio_bound
    (hLight : ∀ r : F4Unified.Row, F4Unified.LightCore r)
    (F : FiniteForest) {r : TableRow} {t : ℝ} (hrow : InTableRow r t)
    (B : Finset (Fin F.n)) (hB : IsMaxWeight F t B) :
    hardCoreVar F t ≤ (gammaTheta r/(1+t))*weightW F t B :=
  finiteForest_variance_ratio_of_allRows (allRowsVarianceRatio hLight) F hrow B hB

theorem finiteForest_exists_variance_ratio
    (hLight : ∀ r : F4Unified.Row, F4Unified.LightCore r)
    (F : FiniteForest) {r : TableRow} {t : ℝ} (hrow : InTableRow r t) :
    ∃ B : Finset (Fin F.n), IsMaxWeight F t B ∧
      hardCoreVar F t ≤ (gammaTheta r/(1+t))*weightW F t B :=
  finiteForest_exists_variance_ratio_of_allRows (allRowsVarianceRatio hLight) F hrow

theorem empty_A_of_light
    (hLight : ∀ r : F4Unified.Row, F4Unified.LightCore r) :
    ∃ A : Finset (Fin 0), IsIndepFinset emptyGraph A ∧
      varB emptyGraph univ (1 / 2) univ ≤
        (gammaTheta .A / (1 + (1 / 2 : ℝ))) * ∑ v ∈ A, gMarg emptyGraph (1 / 2) v :=
  empty_A (allRowsVarianceRatio hLight)

theorem empty_B_of_light
    (hLight : ∀ r : F4Unified.Row, F4Unified.LightCore r) :
    ∃ A : Finset (Fin 0), IsIndepFinset emptyGraph A ∧
      varB emptyGraph univ (2 / 3) univ ≤
        (gammaTheta .B / (1 + (2 / 3 : ℝ))) * ∑ v ∈ A, gMarg emptyGraph (2 / 3) v :=
  empty_B (allRowsVarianceRatio hLight)

theorem empty_D_of_light
    (hLight : ∀ r : F4Unified.Row, F4Unified.LightCore r) :
    ∃ A : Finset (Fin 0), IsIndepFinset emptyGraph A ∧
      varB emptyGraph univ 1 univ ≤
        (gammaTheta .D / (1 + (1 : ℝ))) * ∑ v ∈ A, gMarg emptyGraph 1 v :=
  empty_D (allRowsVarianceRatio hLight)

theorem singleton_A_of_light
    (hLight : ∀ r : F4Unified.Row, F4Unified.LightCore r) :
    ∃ A : Finset (Fin 1), IsIndepFinset singletonGraph A ∧
      varB singletonGraph univ (1 / 2) univ ≤
        (gammaTheta .A / (1 + (1 / 2 : ℝ))) * ∑ v ∈ A, gMarg singletonGraph (1 / 2) v :=
  singleton_A (allRowsVarianceRatio hLight)

theorem singleton_B_of_light
    (hLight : ∀ r : F4Unified.Row, F4Unified.LightCore r) :
    ∃ A : Finset (Fin 1), IsIndepFinset singletonGraph A ∧
      varB singletonGraph univ (2 / 3) univ ≤
        (gammaTheta .B / (1 + (2 / 3 : ℝ))) * ∑ v ∈ A, gMarg singletonGraph (2 / 3) v :=
  singleton_B (allRowsVarianceRatio hLight)

theorem singleton_D_of_light
    (hLight : ∀ r : F4Unified.Row, F4Unified.LightCore r) :
    ∃ A : Finset (Fin 1), IsIndepFinset singletonGraph A ∧
      varB singletonGraph univ 1 univ ≤
        (gammaTheta .D / (1 + (1 : ℝ))) * ∑ v ∈ A, gMarg singletonGraph 1 v :=
  singleton_D (allRowsVarianceRatio hLight)

theorem edge_A_of_light
    (hLight : ∀ r : F4Unified.Row, F4Unified.LightCore r) :
    ∃ A : Finset (Fin 2), IsIndepFinset edgeGraph A ∧
      varB edgeGraph univ (1 / 2) univ ≤
        (gammaTheta .A / (1 + (1 / 2 : ℝ))) * ∑ v ∈ A, gMarg edgeGraph (1 / 2) v :=
  edge_A (allRowsVarianceRatio hLight)

theorem edge_B_of_light
    (hLight : ∀ r : F4Unified.Row, F4Unified.LightCore r) :
    ∃ A : Finset (Fin 2), IsIndepFinset edgeGraph A ∧
      varB edgeGraph univ (2 / 3) univ ≤
        (gammaTheta .B / (1 + (2 / 3 : ℝ))) * ∑ v ∈ A, gMarg edgeGraph (2 / 3) v :=
  edge_B (allRowsVarianceRatio hLight)

theorem edge_D_of_light
    (hLight : ∀ r : F4Unified.Row, F4Unified.LightCore r) :
    ∃ A : Finset (Fin 2), IsIndepFinset edgeGraph A ∧
      varB edgeGraph univ 1 univ ≤
        (gammaTheta .D / (1 + (1 : ℝ))) * ∑ v ∈ A, gMarg edgeGraph 1 v :=
  edge_D (allRowsVarianceRatio hLight)

theorem pathThree_A_of_light
    (hLight : ∀ r : F4Unified.Row, F4Unified.LightCore r) :
    ∃ A : Finset (Fin 3), IsIndepFinset pathThreeGraph A ∧
      varB pathThreeGraph univ (1 / 2) univ ≤
        (gammaTheta .A / (1 + (1 / 2 : ℝ))) * ∑ v ∈ A, gMarg pathThreeGraph (1 / 2) v :=
  pathThree_A (allRowsVarianceRatio hLight)

theorem pathThree_B_of_light
    (hLight : ∀ r : F4Unified.Row, F4Unified.LightCore r) :
    ∃ A : Finset (Fin 3), IsIndepFinset pathThreeGraph A ∧
      varB pathThreeGraph univ (2 / 3) univ ≤
        (gammaTheta .B / (1 + (2 / 3 : ℝ))) * ∑ v ∈ A, gMarg pathThreeGraph (2 / 3) v :=
  pathThree_B (allRowsVarianceRatio hLight)

theorem pathThree_D_of_light
    (hLight : ∀ r : F4Unified.Row, F4Unified.LightCore r) :
    ∃ A : Finset (Fin 3), IsIndepFinset pathThreeGraph A ∧
      varB pathThreeGraph univ 1 univ ≤
        (gammaTheta .D / (1 + (1 : ℝ))) * ∑ v ∈ A, gMarg pathThreeGraph 1 v :=
  pathThree_D (allRowsVarianceRatio hLight)

end Erdos993Lean.Analytic.V213.Theorem51

#check Erdos993Lean.Analytic.V213.Theorem51.heavy_localEvidence
#print axioms Erdos993Lean.Analytic.V213.Theorem51.heavy_localEvidence
#check Erdos993Lean.Analytic.V213.Theorem51.heavy_pairPositive
#print axioms Erdos993Lean.Analytic.V213.Theorem51.heavy_pairPositive
#check Erdos993Lean.Analytic.V213.Theorem51.variance_ratio_bound_all_rows
#print axioms Erdos993Lean.Analytic.V213.Theorem51.variance_ratio_bound_all_rows
#check Erdos993Lean.Analytic.V213.Theorem51.allRowsVarianceRatio
#print axioms Erdos993Lean.Analytic.V213.Theorem51.allRowsVarianceRatio
#check Erdos993Lean.Analytic.V213.Theorem51.exists_independent_variance_ratio_bound
#print axioms Erdos993Lean.Analytic.V213.Theorem51.exists_independent_variance_ratio_bound
#check Erdos993Lean.Analytic.V213.Theorem51.finiteForest_variance_ratio_bound
#print axioms Erdos993Lean.Analytic.V213.Theorem51.finiteForest_variance_ratio_bound
#check Erdos993Lean.Analytic.V213.Theorem51.finiteForest_exists_variance_ratio
#print axioms Erdos993Lean.Analytic.V213.Theorem51.finiteForest_exists_variance_ratio

#check Erdos993Lean.Analytic.V213.Theorem51.empty_A_of_light
#print axioms Erdos993Lean.Analytic.V213.Theorem51.empty_A_of_light

#check Erdos993Lean.Analytic.V213.Theorem51.empty_B_of_light
#print axioms Erdos993Lean.Analytic.V213.Theorem51.empty_B_of_light

#check Erdos993Lean.Analytic.V213.Theorem51.empty_D_of_light
#print axioms Erdos993Lean.Analytic.V213.Theorem51.empty_D_of_light

#check Erdos993Lean.Analytic.V213.Theorem51.singleton_A_of_light
#print axioms Erdos993Lean.Analytic.V213.Theorem51.singleton_A_of_light

#check Erdos993Lean.Analytic.V213.Theorem51.singleton_B_of_light
#print axioms Erdos993Lean.Analytic.V213.Theorem51.singleton_B_of_light

#check Erdos993Lean.Analytic.V213.Theorem51.singleton_D_of_light
#print axioms Erdos993Lean.Analytic.V213.Theorem51.singleton_D_of_light

#check Erdos993Lean.Analytic.V213.Theorem51.edge_A_of_light
#print axioms Erdos993Lean.Analytic.V213.Theorem51.edge_A_of_light

#check Erdos993Lean.Analytic.V213.Theorem51.edge_B_of_light
#print axioms Erdos993Lean.Analytic.V213.Theorem51.edge_B_of_light

#check Erdos993Lean.Analytic.V213.Theorem51.edge_D_of_light
#print axioms Erdos993Lean.Analytic.V213.Theorem51.edge_D_of_light

#check Erdos993Lean.Analytic.V213.Theorem51.pathThree_A_of_light
#print axioms Erdos993Lean.Analytic.V213.Theorem51.pathThree_A_of_light

#check Erdos993Lean.Analytic.V213.Theorem51.pathThree_B_of_light
#print axioms Erdos993Lean.Analytic.V213.Theorem51.pathThree_B_of_light

#check Erdos993Lean.Analytic.V213.Theorem51.pathThree_D_of_light
#print axioms Erdos993Lean.Analytic.V213.Theorem51.pathThree_D_of_light
