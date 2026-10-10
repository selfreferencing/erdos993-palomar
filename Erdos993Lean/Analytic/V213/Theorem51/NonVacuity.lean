module

public import Erdos993Lean.Analytic.V213.Theorem51.Statements
public import Mathlib.Combinatorics.SimpleGraph.Star

/-! Finite marginal-weight maximizers exist, and the common all-row statement
therefore gives an independent-set bound on four explicit small forests.
The all-row theorem is an explicit input here, not an asserted theorem. -/

@[expose] public section

noncomputable section
universe u

namespace Erdos993Lean.Analytic.V213.Theorem51

open Finset Erdos993Lean.Analytic Tail Reserve O2

theorem exists_maximum_gMarg_independent_set
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ) :
    ∃ A : Finset V, IsIndepFinset G A ∧
      ∀ B : Finset V, IsIndepFinset G B →
        (∑ v ∈ B, gMarg G lam v) ≤ ∑ v ∈ A, gMarg G lam v := by
  classical
  let S := (univ : Finset V).powerset.filter (IsIndepFinset G)
  have hS : S.Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset _, ?_⟩⟩
    intro v hv
    exact False.elim (Finset.notMem_empty v hv)
  obtain ⟨A, hA, hmax⟩ :=
    Finset.exists_max_image S (fun B => ∑ v ∈ B, gMarg G lam v) hS
  refine ⟨A, (Finset.mem_filter.mp hA).2, ?_⟩
  intro B hB
  exact hmax B (Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.subset_univ B), hB⟩)

theorem exists_independent_variance_bound (hAll : AllRowsVarianceRatio.{u})
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsAcyclic)
    {r : TableRow} {lam : ℝ} (hrow : InTableRow r lam) :
    ∃ A : Finset V, IsIndepFinset G A ∧
      varB G univ lam univ ≤ (gammaTheta r / (1 + lam)) * ∑ v ∈ A, gMarg G lam v := by
  obtain ⟨A, hA, hmax⟩ := exists_maximum_gMarg_independent_set G lam
  exact ⟨A, hA, hAll V G hG r lam hrow A hA hmax⟩

def emptyGraph : SimpleGraph (Fin 0) := ⊥

def singletonGraph : SimpleGraph (Fin 1) := ⊥

/-- The star on two vertices has exactly the edge joining 0 and 1. -/
def edgeGraph : SimpleGraph (Fin 2) := SimpleGraph.starGraph 0

/-- The star centered at 1 on three vertices is the ordered path 0--1--2. -/
def pathThreeGraph : SimpleGraph (Fin 3) := SimpleGraph.starGraph 1

instance : DecidableRel emptyGraph.Adj := by
  unfold emptyGraph
  infer_instance

instance : DecidableRel singletonGraph.Adj := by
  unfold singletonGraph
  infer_instance

instance : DecidableRel edgeGraph.Adj := by
  unfold edgeGraph
  infer_instance

instance : DecidableRel pathThreeGraph.Adj := by
  unfold pathThreeGraph
  infer_instance

theorem emptyGraph_acyclic : emptyGraph.IsAcyclic := SimpleGraph.isAcyclic_bot

theorem singletonGraph_acyclic : singletonGraph.IsAcyclic := SimpleGraph.isAcyclic_bot

theorem edgeGraph_acyclic : edgeGraph.IsAcyclic :=
  SimpleGraph.isAcyclic_starGraph (0 : Fin 2)

theorem pathThreeGraph_acyclic : pathThreeGraph.IsAcyclic :=
  SimpleGraph.isAcyclic_starGraph (1 : Fin 3)

theorem edgeGraph_eq_pathGraph : edgeGraph = SimpleGraph.pathGraph 2 := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [edgeGraph, SimpleGraph.starGraph_adj, SimpleGraph.pathGraph_adj]

theorem pathThreeGraph_eq_pathGraph : pathThreeGraph = SimpleGraph.pathGraph 3 := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [pathThreeGraph, SimpleGraph.starGraph_adj, SimpleGraph.pathGraph_adj]

theorem row_A_half : InTableRow .A (1 / 2) := by
  norm_num [InTableRow, rowLo, rowHi]

theorem row_B_two_thirds : InTableRow .B (2 / 3) := by
  norm_num [InTableRow, rowLo, rowHi]

theorem row_D_one : InTableRow .D 1 := by
  norm_num [InTableRow, rowLo, rowHi]

theorem empty_A (hAll : AllRowsVarianceRatio.{0}) :
    ∃ A : Finset (Fin 0), IsIndepFinset emptyGraph A ∧
      varB emptyGraph univ (1 / 2) univ ≤
        (gammaTheta .A / (1 + (1 / 2 : ℝ))) * ∑ v ∈ A, gMarg emptyGraph (1 / 2) v :=
  exists_independent_variance_bound hAll emptyGraph emptyGraph_acyclic row_A_half

theorem empty_B (hAll : AllRowsVarianceRatio.{0}) :
    ∃ A : Finset (Fin 0), IsIndepFinset emptyGraph A ∧
      varB emptyGraph univ (2 / 3) univ ≤
        (gammaTheta .B / (1 + (2 / 3 : ℝ))) * ∑ v ∈ A, gMarg emptyGraph (2 / 3) v :=
  exists_independent_variance_bound hAll emptyGraph emptyGraph_acyclic row_B_two_thirds

theorem empty_D (hAll : AllRowsVarianceRatio.{0}) :
    ∃ A : Finset (Fin 0), IsIndepFinset emptyGraph A ∧
      varB emptyGraph univ 1 univ ≤
        (gammaTheta .D / (1 + (1 : ℝ))) * ∑ v ∈ A, gMarg emptyGraph 1 v :=
  exists_independent_variance_bound hAll emptyGraph emptyGraph_acyclic row_D_one

theorem singleton_A (hAll : AllRowsVarianceRatio.{0}) :
    ∃ A : Finset (Fin 1), IsIndepFinset singletonGraph A ∧
      varB singletonGraph univ (1 / 2) univ ≤
        (gammaTheta .A / (1 + (1 / 2 : ℝ))) * ∑ v ∈ A, gMarg singletonGraph (1 / 2) v :=
  exists_independent_variance_bound hAll singletonGraph singletonGraph_acyclic row_A_half

theorem singleton_B (hAll : AllRowsVarianceRatio.{0}) :
    ∃ A : Finset (Fin 1), IsIndepFinset singletonGraph A ∧
      varB singletonGraph univ (2 / 3) univ ≤
        (gammaTheta .B / (1 + (2 / 3 : ℝ))) * ∑ v ∈ A, gMarg singletonGraph (2 / 3) v :=
  exists_independent_variance_bound hAll singletonGraph singletonGraph_acyclic row_B_two_thirds

theorem singleton_D (hAll : AllRowsVarianceRatio.{0}) :
    ∃ A : Finset (Fin 1), IsIndepFinset singletonGraph A ∧
      varB singletonGraph univ 1 univ ≤
        (gammaTheta .D / (1 + (1 : ℝ))) * ∑ v ∈ A, gMarg singletonGraph 1 v :=
  exists_independent_variance_bound hAll singletonGraph singletonGraph_acyclic row_D_one

theorem edge_A (hAll : AllRowsVarianceRatio.{0}) :
    ∃ A : Finset (Fin 2), IsIndepFinset edgeGraph A ∧
      varB edgeGraph univ (1 / 2) univ ≤
        (gammaTheta .A / (1 + (1 / 2 : ℝ))) * ∑ v ∈ A, gMarg edgeGraph (1 / 2) v :=
  exists_independent_variance_bound hAll edgeGraph edgeGraph_acyclic row_A_half

theorem edge_B (hAll : AllRowsVarianceRatio.{0}) :
    ∃ A : Finset (Fin 2), IsIndepFinset edgeGraph A ∧
      varB edgeGraph univ (2 / 3) univ ≤
        (gammaTheta .B / (1 + (2 / 3 : ℝ))) * ∑ v ∈ A, gMarg edgeGraph (2 / 3) v :=
  exists_independent_variance_bound hAll edgeGraph edgeGraph_acyclic row_B_two_thirds

theorem edge_D (hAll : AllRowsVarianceRatio.{0}) :
    ∃ A : Finset (Fin 2), IsIndepFinset edgeGraph A ∧
      varB edgeGraph univ 1 univ ≤
        (gammaTheta .D / (1 + (1 : ℝ))) * ∑ v ∈ A, gMarg edgeGraph 1 v :=
  exists_independent_variance_bound hAll edgeGraph edgeGraph_acyclic row_D_one

theorem pathThree_A (hAll : AllRowsVarianceRatio.{0}) :
    ∃ A : Finset (Fin 3), IsIndepFinset pathThreeGraph A ∧
      varB pathThreeGraph univ (1 / 2) univ ≤
        (gammaTheta .A / (1 + (1 / 2 : ℝ))) * ∑ v ∈ A, gMarg pathThreeGraph (1 / 2) v :=
  exists_independent_variance_bound hAll pathThreeGraph pathThreeGraph_acyclic row_A_half

theorem pathThree_B (hAll : AllRowsVarianceRatio.{0}) :
    ∃ A : Finset (Fin 3), IsIndepFinset pathThreeGraph A ∧
      varB pathThreeGraph univ (2 / 3) univ ≤
        (gammaTheta .B / (1 + (2 / 3 : ℝ))) * ∑ v ∈ A, gMarg pathThreeGraph (2 / 3) v :=
  exists_independent_variance_bound hAll pathThreeGraph pathThreeGraph_acyclic row_B_two_thirds

theorem pathThree_D (hAll : AllRowsVarianceRatio.{0}) :
    ∃ A : Finset (Fin 3), IsIndepFinset pathThreeGraph A ∧
      varB pathThreeGraph univ 1 univ ≤
        (gammaTheta .D / (1 + (1 : ℝ))) * ∑ v ∈ A, gMarg pathThreeGraph 1 v :=
  exists_independent_variance_bound hAll pathThreeGraph pathThreeGraph_acyclic row_D_one

end Erdos993Lean.Analytic.V213.Theorem51

#check Erdos993Lean.Analytic.V213.Theorem51.exists_maximum_gMarg_independent_set
#print axioms Erdos993Lean.Analytic.V213.Theorem51.exists_maximum_gMarg_independent_set
#check Erdos993Lean.Analytic.V213.Theorem51.exists_independent_variance_bound
#print axioms Erdos993Lean.Analytic.V213.Theorem51.exists_independent_variance_bound
#check Erdos993Lean.Analytic.V213.Theorem51.emptyGraph_acyclic
#print axioms Erdos993Lean.Analytic.V213.Theorem51.emptyGraph_acyclic
#check Erdos993Lean.Analytic.V213.Theorem51.singletonGraph_acyclic
#print axioms Erdos993Lean.Analytic.V213.Theorem51.singletonGraph_acyclic
#check Erdos993Lean.Analytic.V213.Theorem51.edgeGraph_acyclic
#print axioms Erdos993Lean.Analytic.V213.Theorem51.edgeGraph_acyclic
#check Erdos993Lean.Analytic.V213.Theorem51.pathThreeGraph_acyclic
#print axioms Erdos993Lean.Analytic.V213.Theorem51.pathThreeGraph_acyclic
#check Erdos993Lean.Analytic.V213.Theorem51.edgeGraph_eq_pathGraph
#print axioms Erdos993Lean.Analytic.V213.Theorem51.edgeGraph_eq_pathGraph
#check Erdos993Lean.Analytic.V213.Theorem51.pathThreeGraph_eq_pathGraph
#print axioms Erdos993Lean.Analytic.V213.Theorem51.pathThreeGraph_eq_pathGraph
#check Erdos993Lean.Analytic.V213.Theorem51.row_A_half
#print axioms Erdos993Lean.Analytic.V213.Theorem51.row_A_half
#check Erdos993Lean.Analytic.V213.Theorem51.row_B_two_thirds
#print axioms Erdos993Lean.Analytic.V213.Theorem51.row_B_two_thirds
#check Erdos993Lean.Analytic.V213.Theorem51.row_D_one
#print axioms Erdos993Lean.Analytic.V213.Theorem51.row_D_one
#check Erdos993Lean.Analytic.V213.Theorem51.empty_A
#print axioms Erdos993Lean.Analytic.V213.Theorem51.empty_A
#check Erdos993Lean.Analytic.V213.Theorem51.empty_B
#print axioms Erdos993Lean.Analytic.V213.Theorem51.empty_B
#check Erdos993Lean.Analytic.V213.Theorem51.empty_D
#print axioms Erdos993Lean.Analytic.V213.Theorem51.empty_D
#check Erdos993Lean.Analytic.V213.Theorem51.singleton_A
#print axioms Erdos993Lean.Analytic.V213.Theorem51.singleton_A
#check Erdos993Lean.Analytic.V213.Theorem51.singleton_B
#print axioms Erdos993Lean.Analytic.V213.Theorem51.singleton_B
#check Erdos993Lean.Analytic.V213.Theorem51.singleton_D
#print axioms Erdos993Lean.Analytic.V213.Theorem51.singleton_D
#check Erdos993Lean.Analytic.V213.Theorem51.edge_A
#print axioms Erdos993Lean.Analytic.V213.Theorem51.edge_A
#check Erdos993Lean.Analytic.V213.Theorem51.edge_B
#print axioms Erdos993Lean.Analytic.V213.Theorem51.edge_B
#check Erdos993Lean.Analytic.V213.Theorem51.edge_D
#print axioms Erdos993Lean.Analytic.V213.Theorem51.edge_D
#check Erdos993Lean.Analytic.V213.Theorem51.pathThree_A
#print axioms Erdos993Lean.Analytic.V213.Theorem51.pathThree_A
#check Erdos993Lean.Analytic.V213.Theorem51.pathThree_B
#print axioms Erdos993Lean.Analytic.V213.Theorem51.pathThree_B
#check Erdos993Lean.Analytic.V213.Theorem51.pathThree_D
#print axioms Erdos993Lean.Analytic.V213.Theorem51.pathThree_D
