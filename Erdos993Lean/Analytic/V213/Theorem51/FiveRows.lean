module

public import Erdos993Lean.Analytic.V213.Theorem51.Statements
public import Erdos993Lean.Analytic.V213.RowAForest
public import Erdos993Lean.BCFG.RowForest

/-! Theorem 5.1 for rows A, B, C, F and G in the common nine-row vocabulary. -/

@[expose] public section

noncomputable section

namespace Erdos993Lean.Analytic.V213.Theorem51

open Finset Erdos993Lean.Analytic Tail Reserve O2

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

theorem variance_ratio_bound_five_rows (hG : G.IsAcyclic)
    {r : TableRow} (hfive : r = .A ∨ r = .B ∨ r = .C ∨ r = .F ∨ r = .G)
    {lam : ℝ} (hrow : InTableRow r lam)
    (A : Finset V) (hA : IsIndepFinset G A)
    (hmax : ∀ B : Finset V, IsIndepFinset G B →
      (∑ v ∈ B, gMarg G lam v) ≤ ∑ v ∈ A, gMarg G lam v) :
    varB G univ lam univ ≤ (gammaTheta r/(1+lam))*∑ v ∈ A, gMarg G lam v := by
  rcases hfive with rfl | rfl | rfl | rfl | rfl
  · exact VarianceResponse.RowA.rowA_forest_variance_bound hG hrow.1 hrow.2 A hA hmax
  · exact Erdos993Lean.BCFG.Analytic.bcfg_forest_variance_bound (r := .B) hG hrow A hA hmax
  · exact Erdos993Lean.BCFG.Analytic.bcfg_forest_variance_bound (r := .C) hG hrow A hA hmax
  · exact Erdos993Lean.BCFG.Analytic.bcfg_forest_variance_bound (r := .F) hG hrow A hA hmax
  · exact Erdos993Lean.BCFG.Analytic.bcfg_forest_variance_bound (r := .G) hG hrow A hA hmax

end Erdos993Lean.Analytic.V213.Theorem51

#check Erdos993Lean.Analytic.V213.Theorem51.variance_ratio_bound_five_rows
#print axioms Erdos993Lean.Analytic.V213.Theorem51.variance_ratio_bound_five_rows
