module

public import Erdos993Lean.Analytic.V213.FiberBudgetInputCheck
public import Erdos993Lean.Analytic.V213.LowMeanCoverageData
public import Erdos993Lean.Analytic.V213.Theorem51.Statements
public import Erdos993Lean.Analytic.Translate

/-! Numeric bindings between the 55 activity inputs and the nine variance rows.
Only numeric projections of the fiber route records are reduced. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

theorem fiber_input_index_at (i : ℕ) (hi : i < 55) :
    fiberInputIndex (fiberInputIdentityAt i) = i := by
  interval_cases i <;> rfl

theorem fiber_input_iota_at (i : ℕ) (hi : i < 55) :
    (fiberInputRouteById (fiberInputIdentityAt i)).iota = i := by
  rcases fiber_input_domain_facts (fiberInputIdentityAt i) with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, h, _, _⟩
  exact h.trans (fiber_input_index_at i hi)

theorem fiber_input_starting_mean_eq (id : FiberInputIdentity) :
    lowMeanFractionReal (fiberInputPaperRow id).mu0 =
      lowMeanFractionReal (fiberInputRouteById id).mu0 := by
  rcases fiber_input_domain_facts id with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hv, _⟩
  rcases fiber_budget_input_facts id with ⟨_, _, hp, _, _, _, _, he, _⟩
  exact (lowMean_fraction_eq_iff hp hv).mp he

set_option maxHeartbeats 400000 in
theorem fiber_input_rate_eq (i : ℕ) (hi : i < 55) :
    lowMeanFractionReal (fiberInputRouteById (fiberInputIdentityAt i)).ell0 =
      ((N44.Data.rates44.getD i []).getD 0 0 : ℝ) := by
  have h : ((fiberInputRouteById (fiberInputIdentityAt i)).ell0.1 : ℚ) /
      ((fiberInputRouteById (fiberInputIdentityAt i)).ell0.2 : ℚ) =
      (N44.Data.rates44.getD i []).getD 0 0 := by
    interval_cases i <;> decide +kernel
  unfold lowMeanFractionReal
  exact_mod_cast h

theorem fiber_input_rate_le (i : ℕ) (hi : i < 55) :
    lowMeanFractionReal (fiberInputRouteById (fiberInputIdentityAt i)).ell0 ≤
      ((N44.Data.rates44.getD i []).getD 0 0 : ℝ) :=
  (fiber_input_rate_eq i hi).le

theorem FreeCountVariance.q_eq_actQ (lam : ℝ) :
    FreeCountVariance.q lam = actQ lam := rfl

/-- The closed table row containing each retained closed activity input. -/
def inputTableRow (i : ℕ) : Theorem51.TableRow :=
  if i < 6 then .A else if i < 10 then .B else if i < 11 then .C
  else if i < 38 then .D else if i < 42 then .E1 else if i < 44 then .E2
  else if i < 45 then .F else if i < 47 then .G else .H

/-- Rational views of the existing nine closed-row endpoints. -/
def tableRowLoRat : Theorem51.TableRow → ℚ
  | .A => 1/3 | .B => 3/5 | .C => 39/50 | .D => 4/5
  | .E1 => 13/10 | .E2 => 29/20 | .F => 8/5 | .G => 33/20 | .H => 7/4

def tableRowHiRat : Theorem51.TableRow → ℚ
  | .A => 3/5 | .B => 39/50 | .C => 4/5 | .D => 13/10
  | .E1 => 29/20 | .E2 => 8/5 | .F => 33/20 | .G => 7/4 | .H => 7/3

theorem table_row_endpoint_cast (r : Theorem51.TableRow) :
    (tableRowLoRat r : ℝ) = Theorem51.rowLo r ∧
    (tableRowHiRat r : ℝ) = Theorem51.rowHi r := by
  cases r <;> norm_num [tableRowLoRat, tableRowHiRat, Theorem51.rowLo, Theorem51.rowHi]

theorem input_table_row_endpoints (i : ℕ) (hi : i < 55) :
    Theorem51.rowLo (inputTableRow i) ≤ (N44.Data.pieceLo.getD i 0 : ℝ) ∧
    (N44.Data.pieceHi.getD i 0 : ℝ) ≤ Theorem51.rowHi (inputTableRow i) := by
  have h : ∀ j : Fin 55,
      tableRowLoRat (inputTableRow j) ≤ N44.Data.pieceLo.getD j 0 ∧
      N44.Data.pieceHi.getD j 0 ≤ tableRowHiRat (inputTableRow j) := by
    decide +kernel
  have h' := h ⟨i, hi⟩
  have hlo : (tableRowLoRat (inputTableRow i) : ℝ) ≤
      (N44.Data.pieceLo.getD i 0 : ℝ) := by exact_mod_cast h'.1
  have hhi : (N44.Data.pieceHi.getD i 0 : ℝ) ≤
      (tableRowHiRat (inputTableRow i) : ℝ) := by exact_mod_cast h'.2
  rw [(table_row_endpoint_cast _).1] at hlo
  rw [(table_row_endpoint_cast _).2] at hhi
  exact ⟨hlo, hhi⟩

set_option maxHeartbeats 400000 in
theorem input_table_row_theta (i : ℕ) (hi : i < 55) :
    Theorem51.gammaTheta (inputTableRow i) =
      1 + lowMeanFractionReal (lowMeanInputRowAt i).theta := by
  interval_cases i <;>
    norm_num [inputTableRow, Theorem51.gammaTheta, lowMeanInputRowAt, lowMeanInputRows,
      lowMeanFractionReal]

theorem input_table_row_facts (i : ℕ) (hi : i < 55) :
    Theorem51.rowLo (inputTableRow i) ≤ (N44.Data.pieceLo.getD i 0 : ℝ) ∧
    (N44.Data.pieceHi.getD i 0 : ℝ) ≤ Theorem51.rowHi (inputTableRow i) ∧
    Theorem51.gammaTheta (inputTableRow i) =
      1 + lowMeanFractionReal (lowMeanInputRowAt i).theta :=
  ⟨(input_table_row_endpoints i hi).1, (input_table_row_endpoints i hi).2,
    input_table_row_theta i hi⟩

theorem input_in_table_row (i : ℕ) (hi : i < 55) {lam : ℝ}
    (hlam : lam ∈ Set.Icc (N44.Data.pieceLo.getD i 0 : ℝ)
      (N44.Data.pieceHi.getD i 0 : ℝ)) :
    Theorem51.InTableRow (inputTableRow i) lam := by
  have h := input_table_row_facts i hi
  exact ⟨h.1.trans hlam.1, hlam.2.trans h.2.1⟩

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.fiber_input_index_at
#print axioms Erdos993Lean.Analytic.V213.fiber_input_starting_mean_eq
#print axioms Erdos993Lean.Analytic.V213.fiber_input_rate_eq
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.q_eq_actQ
#print axioms Erdos993Lean.Analytic.V213.input_table_row_facts

#print axioms Erdos993Lean.Analytic.V213.fiber_input_iota_at
#print axioms Erdos993Lean.Analytic.V213.fiber_input_rate_le
#print axioms Erdos993Lean.Analytic.V213.input_in_table_row
