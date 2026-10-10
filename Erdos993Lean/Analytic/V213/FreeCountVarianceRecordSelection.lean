module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordDomains

/-!
Structural selection from an already checked finite list.
These lemmas do not evaluate a comparison, a polynomial, or a guard.
The selected item remains the actual library list element.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

open Erdos993Lean.ExactComparisons

theorem comparison_record_at {records : List Comparison}
    (hall : check records = true) (i : Nat) (hi : i < records.length) :
    (records[i]'hi).check = true := by
  exact (List.all_eq_true.mp hall) _ (List.getElem_mem hi)

theorem boolean_record_at {records : List Bool}
    (hall : records.all id = true) (i : Nat) (hi : i < records.length) :
    records[i]'hi = true := by
  exact (List.all_eq_true.mp hall) _ (List.getElem_mem hi)

/-- A literal expression can be used only after its exact selected-item equality. -/
theorem comparison_record_literal {records : List Comparison}
    (hall : check records = true) (i : Nat) (hi : i < records.length)
    (c : Comparison) (hselected : records[i]'hi = c) : c.check = true := by
  rw [← hselected]
  exact comparison_record_at hall i hi

theorem boolean_record_literal {records : List Bool}
    (hall : records.all id = true) (i : Nat) (hi : i < records.length)
    (b : Bool) (hselected : records[i]'hi = b) : b = true := by
  rw [← hselected]
  exact boolean_record_at hall i hi

end Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

-- Type and axiom audit commands.
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.comparison_record_at
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.comparison_record_at
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.boolean_record_at
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.boolean_record_at
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.comparison_record_literal
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.comparison_record_literal
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.boolean_record_literal
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.boolean_record_literal
