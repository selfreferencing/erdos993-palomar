module

public import F4Heavy.Contract
public import Erdos993Lean.Analytic.V213.ResponseParentRowRecords
public import Erdos993Lean.Analytic.O2.Defs
public import Erdos993Lean.BCFG.RowParameters

/-! Exact identifications of the two heavy-row tables and their scalar conventions. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.Theorem51

open VarianceResponse

/-- The order of the four literal parent rows is D, E1, E2, H. -/
def parentRowIndex : F4Unified.Row → Fin 4
  | .D => 0
  | .E1 => 1
  | .E2 => 2
  | .H => 3

theorem row_low_eq (r : F4Unified.Row) :
    (F4Unified.rowData r).lo = (ParentRows.rowData (parentRowIndex r)).low := by
  cases r <;> norm_num [parentRowIndex, F4Unified.rowData, ParentRows.rowData]

theorem row_high_eq (r : F4Unified.Row) :
    (F4Unified.rowData r).hi = (ParentRows.rowData (parentRowIndex r)).high := by
  cases r <;> norm_num [parentRowIndex, F4Unified.rowData, ParentRows.rowData]

/-- The contract's `price` field is the table numerator, not the divided row price. -/
theorem row_price_eq (r : F4Unified.Row) :
    (F4Unified.rowData r).price =
      (ParentRows.rowData (parentRowIndex r)).gammaTheta := by
  cases r <;> norm_num [parentRowIndex, F4Unified.rowData, ParentRows.rowData]

theorem row_center_eq (r : F4Unified.Row) :
    (F4Unified.rowData r).center = (ParentRows.rowData (parentRowIndex r)).center := by
  cases r <;> norm_num [parentRowIndex, F4Unified.rowData, ParentRows.rowData]

theorem row_alpha0_eq (r : F4Unified.Row) :
    (F4Unified.rowData r).alpha0 = (ParentRows.rowData (parentRowIndex r)).alpha0 := by
  cases r <;> norm_num [parentRowIndex, F4Unified.rowData, ParentRows.rowData]

theorem row_alpha1_eq (r : F4Unified.Row) :
    (F4Unified.rowData r).alpha1 = (ParentRows.rowData (parentRowIndex r)).alpha1 := by
  cases r <;> norm_num [parentRowIndex, F4Unified.rowData, ParentRows.rowData]

theorem row_beta0_eq (r : F4Unified.Row) :
    (F4Unified.rowData r).beta0 = (ParentRows.rowData (parentRowIndex r)).beta0 := by
  cases r <;> norm_num [parentRowIndex, F4Unified.rowData, ParentRows.rowData]

theorem row_beta1_eq (r : F4Unified.Row) :
    (F4Unified.rowData r).beta1 = (ParentRows.rowData (parentRowIndex r)).beta1 := by
  cases r <;> norm_num [parentRowIndex, F4Unified.rowData, ParentRows.rowData]

theorem row_gamma0_eq (r : F4Unified.Row) :
    (F4Unified.rowData r).gamma0 = (ParentRows.rowData (parentRowIndex r)).gamma0 := by
  cases r <;> norm_num [parentRowIndex, F4Unified.rowData, ParentRows.rowData]

theorem row_gamma1_eq (r : F4Unified.Row) :
    (F4Unified.rowData r).gamma1 = (ParentRows.rowData (parentRowIndex r)).gamma1 := by
  cases r <;> norm_num [parentRowIndex, F4Unified.rowData, ParentRows.rowData]

theorem row_delta0_eq (r : F4Unified.Row) :
    (F4Unified.rowData r).delta0 = (ParentRows.rowData (parentRowIndex r)).delta0 := by
  cases r <;> norm_num [parentRowIndex, F4Unified.rowData, ParentRows.rowData]

theorem row_delta1_eq (r : F4Unified.Row) :
    (F4Unified.rowData r).delta1 = (ParentRows.rowData (parentRowIndex r)).delta1 := by
  cases r <;> norm_num [parentRowIndex, F4Unified.rowData, ParentRows.rowData]

theorem inRow_iff (r : F4Unified.Row) (lam : ℝ) :
    F4Unified.InRow r lam ↔ ParentRows.inRow (parentRowIndex r) lam := by
  unfold F4Unified.InRow ParentRows.inRow
  rw [row_low_eq, row_high_eq]

theorem alpha_eq (r : F4Unified.Row) (lam : ℝ) :
    F4Unified.alpha r lam = ParentRows.alpha (parentRowIndex r) lam := by
  unfold F4Unified.alpha F4Unified.field ParentRows.alpha ParentRows.affineField
  rw [row_alpha0_eq, row_alpha1_eq, row_center_eq]

theorem beta_eq (r : F4Unified.Row) (lam : ℝ) :
    F4Unified.beta r lam = ParentRows.beta (parentRowIndex r) lam := by
  unfold F4Unified.beta F4Unified.field ParentRows.beta ParentRows.affineField
  rw [row_beta0_eq, row_beta1_eq, row_center_eq]

theorem gamma_eq (r : F4Unified.Row) (lam : ℝ) :
    F4Unified.gamma r lam = ParentRows.gamma (parentRowIndex r) lam := by
  unfold F4Unified.gamma F4Unified.field ParentRows.gamma ParentRows.affineField
  rw [row_gamma0_eq, row_gamma1_eq, row_center_eq]

theorem delta_eq (r : F4Unified.Row) (lam : ℝ) :
    F4Unified.delta r lam = ParentRows.delta (parentRowIndex r) lam := by
  unfold F4Unified.delta F4Unified.field ParentRows.delta ParentRows.affineField
  rw [row_delta0_eq, row_delta1_eq, row_center_eq]

/-- ParentRows has already divided the literal table price by `1 + lam`. -/
theorem price_eq (r : F4Unified.Row) (lam : ℝ) :
    ParentRows.price (parentRowIndex r) lam = (F4Unified.rowData r).price / (1 + lam) := by
  unfold ParentRows.price
  rw [row_price_eq]

theorem q_eq_actQ (lam : ℝ) : F4Unified.q lam = actQ lam := by
  rfl

theorem q_eq_bcfg (lam : ℝ) :
    F4Unified.q lam = Erdos993Lean.BCFG.Analytic.q lam := by
  rfl

/-- This identity uses total real division, so it needs no activity hypothesis. -/
theorem f_eq_fq (lam t : ℝ) : F4Unified.f lam t = O2.fq (actQ lam) t := by
  unfold F4Unified.f O2.fq
  rw [q_eq_actQ]
  congr 1 <;> ring

theorem row_activity_pos {r : F4Unified.Row} {lam : ℝ}
    (hrow : F4Unified.InRow r lam) : 0 < lam := by
  have hlo : 0 < (F4Unified.rowData r).lo := by
    cases r <;> norm_num [F4Unified.rowData]
  exact lt_of_lt_of_le hlo hrow.1

end Erdos993Lean.Analytic.V213.Theorem51

#check Erdos993Lean.Analytic.V213.Theorem51.inRow_iff
#print axioms Erdos993Lean.Analytic.V213.Theorem51.inRow_iff
#check Erdos993Lean.Analytic.V213.Theorem51.alpha_eq
#print axioms Erdos993Lean.Analytic.V213.Theorem51.alpha_eq
#check Erdos993Lean.Analytic.V213.Theorem51.beta_eq
#print axioms Erdos993Lean.Analytic.V213.Theorem51.beta_eq
#check Erdos993Lean.Analytic.V213.Theorem51.gamma_eq
#print axioms Erdos993Lean.Analytic.V213.Theorem51.gamma_eq
#check Erdos993Lean.Analytic.V213.Theorem51.delta_eq
#print axioms Erdos993Lean.Analytic.V213.Theorem51.delta_eq
#check Erdos993Lean.Analytic.V213.Theorem51.price_eq
#print axioms Erdos993Lean.Analytic.V213.Theorem51.price_eq
#check Erdos993Lean.Analytic.V213.Theorem51.q_eq_actQ
#print axioms Erdos993Lean.Analytic.V213.Theorem51.q_eq_actQ
#check Erdos993Lean.Analytic.V213.Theorem51.q_eq_bcfg
#print axioms Erdos993Lean.Analytic.V213.Theorem51.q_eq_bcfg
#check Erdos993Lean.Analytic.V213.Theorem51.f_eq_fq
#print axioms Erdos993Lean.Analytic.V213.Theorem51.f_eq_fq
