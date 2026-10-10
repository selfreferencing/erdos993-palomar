module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.FreeCountRationalTransfer
public import Erdos993Lean.ExactComparisons.F3All.Strict004

/-! Every assertion selects an already checked original
record at its reviewed index. Real comparisons use the generic exact Rat cast.
No rational comparison is recomputed, and no analytic closure is asserted. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords

open Erdos993Lean.ExactComparisons Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates
open Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes

-- F49: N_5(2/3,9/5)>5    [childless diagonal, cap 4]
theorem fixed_F49 : ((((5 : Rat)) : Rat) : ℝ) < ((((nFive (((2 : Rat) / (3 : Rat))) (((9 : Rat) / (5 : Rat))))) : Rat) : ℝ) :=
  ofRats_lt_real (comparison_record_at Strict004.checked 0
    (by change 0 < 16; omega))

-- F50: N_4(7/10,21/10)>9    [childless diagonal, cap 5]
theorem fixed_F50 : ((((9 : Rat)) : Rat) : ℝ) < ((((nFour (((7 : Rat) / (10 : Rat))) (((21 : Rat) / (10 : Rat))))) : Rat) : ℝ) :=
  ofRats_lt_real (comparison_record_at Strict004.checked 1
    (by change 1 < 16; omega))

-- F51: N_5(7/10,21/10)>5    [childless diagonal, cap 5]
theorem fixed_F51 : ((((5 : Rat)) : Rat) : ℝ) < ((((nFive (((7 : Rat) / (10 : Rat))) (((21 : Rat) / (10 : Rat))))) : Rat) : ℝ) :=
  ofRats_lt_real (comparison_record_at Strict004.checked 2
    (by change 2 < 16; omega))

end Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords

#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F49
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F49
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F50
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F50
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F51
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F51
