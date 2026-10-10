module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.FreeCountRationalTransfer
public import Erdos993Lean.ExactComparisons.F3All.Strict001

/-! Every assertion selects an already checked original
record at its reviewed index. Real comparisons use the generic exact Rat cast.
No rational comparison is recomputed, and no analytic closure is asserted. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords

open Erdos993Lean.ExactComparisons Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates
open Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes

-- F10: \mathcal L_+(369/80)<153/100    [J below 1/3]
theorem fixed_F10 : ((((logUpper (((369 : Rat) / (80 : Rat))))) : Rat) : ℝ) < (((((153 : Rat) / (100 : Rat))) : Rat) : ℝ) :=
  ofRats_lt_real (comparison_record_at Strict001.checked 9
    (by change 9 < 16; omega))

-- F11: \mathcal L_-(463/200)>4/5    [gamma at cap endpoints]
theorem fixed_F11 : (((((4 : Rat) / (5 : Rat))) : Rat) : ℝ) < ((((logLower (((463 : Rat) / (200 : Rat))))) : Rat) : ℝ) :=
  ofRats_lt_real (comparison_record_at Strict001.checked 10
    (by change 10 < 16; omega))

-- F12: \mathcal E_+(5/4)<4    [CA face curvature]
theorem fixed_F12 : ((((expUpper (((5 : Rat) / (4 : Rat))))) : Rat) : ℝ) < ((((4 : Rat)) : Rat) : ℝ) :=
  ofRats_lt_real (comparison_record_at Strict001.checked 11
    (by change 11 < 16; omega))

-- F16: E_5(405884/267809)>181/40    [negative L, cap 1]
theorem fixed_F16 : (((((181 : Rat) / (40 : Rat))) : Rat) : ℝ) < ((((expFive (((405884 : Rat) / (267809 : Rat))))) : Rat) : ℝ) :=
  ofRats_lt_real (comparison_record_at Strict001.checked 15
    (by change 15 < 16; omega))

end Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords

#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F10
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F10
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F11
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F11
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F12
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F12
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F16
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F16
