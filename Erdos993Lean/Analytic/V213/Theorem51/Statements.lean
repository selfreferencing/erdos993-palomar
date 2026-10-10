module

public import F4Heavy.Contract
public import Erdos993Lean.BCFG.RowParameters
public import Erdos993Lean.Analytic.O2.Source

/-! The nine closed rows of Table 1 and the actual forest statement of Theorem 5.1.
The statement definitions assert no proof and hide no mathematical premise. -/

@[expose] public section

noncomputable section
universe u

namespace Erdos993Lean.Analytic.V213.Theorem51

open Finset Erdos993Lean.Analytic Tail Reserve O2

inductive TableRow where
  | A | B | C | D | E1 | E2 | F | G | H
  deriving DecidableEq, Repr

def rowLo : TableRow → ℝ
  | .A => 1/3 | .B => 3/5 | .C => 39/50 | .D => 4/5
  | .E1 => 13/10 | .E2 => 29/20 | .F => 8/5 | .G => 33/20 | .H => 7/4

def rowHi : TableRow → ℝ
  | .A => 3/5 | .B => 39/50 | .C => 4/5 | .D => 13/10
  | .E1 => 29/20 | .E2 => 8/5 | .F => 33/20 | .G => 7/4 | .H => 7/3

def gammaTheta : TableRow → ℝ
  | .A => 2 | .B => 17/10 | .C => 33/20 | .D => 8/5
  | .E1 => 17/10 | .E2 => 17/10 | .F => 19/10 | .G => 39/20 | .H => 2

def InTableRow (r : TableRow) (lam : ℝ) : Prop := rowLo r ≤ lam ∧ lam ≤ rowHi r

def tableRowOfBCFG : Erdos993Lean.BCFG.AnalyticRow → TableRow
  | .B => .B | .C => .C | .F => .F | .G => .G

def tableRowOfHeavy : F4Unified.Row → TableRow
  | .D => .D | .E1 => .E1 | .E2 => .E2 | .H => .H

theorem bcfg_rowLo_eq (r : Erdos993Lean.BCFG.AnalyticRow) :
    rowLo (tableRowOfBCFG r) = Erdos993Lean.BCFG.Analytic.rowLow r := by
  cases r <;> rfl

theorem bcfg_rowHi_eq (r : Erdos993Lean.BCFG.AnalyticRow) :
    rowHi (tableRowOfBCFG r) = Erdos993Lean.BCFG.Analytic.rowHigh r := by
  cases r <;> rfl

theorem bcfg_gammaTheta_eq (r : Erdos993Lean.BCFG.AnalyticRow) :
    gammaTheta (tableRowOfBCFG r) = Erdos993Lean.BCFG.Analytic.theta r := by
  cases r <;> rfl

theorem bcfg_inTableRow_iff (r : Erdos993Lean.BCFG.AnalyticRow) (lam : ℝ) :
    InTableRow (tableRowOfBCFG r) lam ↔ Erdos993Lean.BCFG.Analytic.InRow r lam := by
  simp only [InTableRow, bcfg_rowLo_eq, bcfg_rowHi_eq, Erdos993Lean.BCFG.Analytic.InRow]

theorem heavy_rowLo_eq (r : F4Unified.Row) :
    rowLo (tableRowOfHeavy r) = (F4Unified.rowData r).lo := by
  cases r <;> rfl

theorem heavy_rowHi_eq (r : F4Unified.Row) :
    rowHi (tableRowOfHeavy r) = (F4Unified.rowData r).hi := by
  cases r <;> rfl

theorem heavy_gammaTheta_eq (r : F4Unified.Row) :
    gammaTheta (tableRowOfHeavy r) = (F4Unified.rowData r).price := by
  cases r <;> rfl

theorem heavy_inTableRow_iff (r : F4Unified.Row) (lam : ℝ) :
    InTableRow (tableRowOfHeavy r) lam ↔ F4Unified.InRow r lam := by
  simp only [InTableRow, heavy_rowLo_eq, heavy_rowHi_eq, F4Unified.InRow]

theorem table_row_nondegenerate (r : TableRow) : rowLo r < rowHi r := by
  cases r <;> norm_num [rowLo, rowHi]

theorem table_row_nonempty (r : TableRow) : ∃ lam, InTableRow r lam :=
  ⟨rowLo r, le_rfl, (table_row_nondegenerate r).le⟩

theorem table_activity_pos {r : TableRow} {lam : ℝ} (h : InTableRow r lam) :
    0 < lam := by
  have hlo : 0 < rowLo r := by cases r <;> norm_num [rowLo]
  exact hlo.trans_le h.1

/-- Printed Theorem 5.1 about the actual variance and maximum marginal-weight set. -/
def AllRowsVarianceRatio : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.IsAcyclic → ∀ (r : TableRow) (lam : ℝ), InTableRow r lam →
    ∀ A : Finset V, IsIndepFinset G A →
      (∀ B : Finset V, IsIndepFinset G B →
        (∑ v ∈ B, gMarg G lam v) ≤ ∑ v ∈ A, gMarg G lam v) →
      varB G univ lam univ ≤ (gammaTheta r/(1+lam))*∑ v ∈ A, gMarg G lam v

/-- The sole permitted open input is the light core for the four heavy rows. -/
def AllRowsVarianceRatioOfLight : Prop :=
  (∀ r : F4Unified.Row, F4Unified.LightCore r) → AllRowsVarianceRatio.{u}

end Erdos993Lean.Analytic.V213.Theorem51

#check Erdos993Lean.Analytic.V213.Theorem51.AllRowsVarianceRatio
#check Erdos993Lean.Analytic.V213.Theorem51.AllRowsVarianceRatioOfLight
#print axioms Erdos993Lean.Analytic.V213.Theorem51.bcfg_inTableRow_iff
#print axioms Erdos993Lean.Analytic.V213.Theorem51.heavy_inTableRow_iff
#print axioms Erdos993Lean.Analytic.V213.Theorem51.table_row_nonempty
