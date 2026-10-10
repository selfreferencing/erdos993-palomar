module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.FreeCountRationalTransfer
public import Erdos993Lean.ExactComparisons.F3All.Validity015

/-! Every assertion selects an already checked original
record at its reviewed index. Real comparisons use the generic exact Rat cast.
No rational comparison is recomputed, and no analytic closure is asserted. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords

open Erdos993Lean.ExactComparisons Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates
open Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes

-- log.domain0002
theorem guard_log_domain0002 : logUseOK (((369 : Rat) / (80 : Rat))) = true :=
  boolean_record_at Validity015.checked 56 (by change 56 < 64; omega)

-- log.domain0003
theorem guard_log_domain0003 : logUseOK (((463 : Rat) / (200 : Rat))) = true :=
  boolean_record_at Validity015.checked 57 (by change 57 < 64; omega)

end Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords

#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.guard_log_domain0002
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.guard_log_domain0002
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.guard_log_domain0003
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.guard_log_domain0003
