module

public import Erdos993Lean.Analytic.V213.Theorem51.TableBinding
public import Erdos993Lean.Analytic.V213.ResponseParentRowAffineBounds

/-! Closed-row multiplier signs transported from the existing parent-row affine bounds. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.Theorem51

open VarianceResponse

theorem row_price_pos (r : F4Unified.Row) : 0 < (F4Unified.rowData r).price := by
  cases r <;> norm_num [F4Unified.rowData]

theorem price_pos {r : F4Unified.Row} {lam : ℝ} (hrow : F4Unified.InRow r lam) :
    0 < (F4Unified.rowData r).price / (1 + lam) := by
  have hl := row_activity_pos hrow
  exact div_pos (row_price_pos r) (by linarith)

theorem price_nonneg {r : F4Unified.Row} {lam : ℝ} (hrow : F4Unified.InRow r lam) :
    0 ≤ (F4Unified.rowData r).price / (1 + lam) :=
  (price_pos hrow).le

theorem fields_positive {r : F4Unified.Row} {lam : ℝ} (hrow : F4Unified.InRow r lam) :
    0 < F4Unified.alpha r lam ∧ 0 < F4Unified.beta r lam ∧
      0 < F4Unified.gamma r lam ∧ 0 < F4Unified.delta r lam := by
  rw [alpha_eq, beta_eq, gamma_eq, delta_eq]
  exact ParentRows.all_rows_fields_positive ((inRow_iff r lam).1 hrow)

theorem gamma_pos {r : F4Unified.Row} {lam : ℝ} (hrow : F4Unified.InRow r lam) :
    0 < F4Unified.gamma r lam :=
  (fields_positive hrow).2.2.1

theorem delta_pos {r : F4Unified.Row} {lam : ℝ} (hrow : F4Unified.InRow r lam) :
    0 < F4Unified.delta r lam :=
  (fields_positive hrow).2.2.2

theorem multiplier_signs {r : F4Unified.Row} {lam : ℝ} (hrow : F4Unified.InRow r lam) :
    0 ≤ (F4Unified.rowData r).price / (1 + lam) ∧
      0 ≤ F4Unified.gamma r lam ∧ 0 < F4Unified.delta r lam :=
  ⟨price_nonneg hrow, (gamma_pos hrow).le, delta_pos hrow⟩

theorem D_multiplier_signs {lam : ℝ} (hrow : F4Unified.InRow .D lam) :
    0 ≤ (F4Unified.rowData .D).price / (1 + lam) ∧
      0 ≤ F4Unified.gamma .D lam ∧ 0 < F4Unified.delta .D lam :=
  multiplier_signs hrow

theorem E1_multiplier_signs {lam : ℝ} (hrow : F4Unified.InRow .E1 lam) :
    0 ≤ (F4Unified.rowData .E1).price / (1 + lam) ∧
      0 ≤ F4Unified.gamma .E1 lam ∧ 0 < F4Unified.delta .E1 lam :=
  multiplier_signs hrow

theorem E2_multiplier_signs {lam : ℝ} (hrow : F4Unified.InRow .E2 lam) :
    0 ≤ (F4Unified.rowData .E2).price / (1 + lam) ∧
      0 ≤ F4Unified.gamma .E2 lam ∧ 0 < F4Unified.delta .E2 lam :=
  multiplier_signs hrow

theorem H_multiplier_signs {lam : ℝ} (hrow : F4Unified.InRow .H lam) :
    0 ≤ (F4Unified.rowData .H).price / (1 + lam) ∧
      0 ≤ F4Unified.gamma .H lam ∧ 0 < F4Unified.delta .H lam :=
  multiplier_signs hrow

end Erdos993Lean.Analytic.V213.Theorem51

#check Erdos993Lean.Analytic.V213.Theorem51.multiplier_signs
#print axioms Erdos993Lean.Analytic.V213.Theorem51.multiplier_signs
#check Erdos993Lean.Analytic.V213.Theorem51.D_multiplier_signs
#print axioms Erdos993Lean.Analytic.V213.Theorem51.D_multiplier_signs
#check Erdos993Lean.Analytic.V213.Theorem51.E1_multiplier_signs
#print axioms Erdos993Lean.Analytic.V213.Theorem51.E1_multiplier_signs
#check Erdos993Lean.Analytic.V213.Theorem51.E2_multiplier_signs
#print axioms Erdos993Lean.Analytic.V213.Theorem51.E2_multiplier_signs
#check Erdos993Lean.Analytic.V213.Theorem51.H_multiplier_signs
#print axioms Erdos993Lean.Analytic.V213.Theorem51.H_multiplier_signs
