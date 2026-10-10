module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.FreeCountRationalTransfer
public import Erdos993Lean.ExactComparisons.F3All.Strict003

/-! Every assertion selects an already checked original
record at its reviewed index. Real comparisons use the generic exact Rat cast.
No rational comparison is recomputed, and no analytic closure is asserted. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords

open Erdos993Lean.ExactComparisons Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates
open Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes

-- F33: [25/24+(81/200)(3/2)]/[(5/12)(7/5)]<10/3    [lambda/gamma, cap 2]
theorem fixed_F33 : (((((((25 : Rat) / (24 : Rat)) + (((81 : Rat) / (200 : Rat)) * ((3 : Rat) / (2 : Rat)))) / (((5 : Rat) / (12 : Rat)) * ((7 : Rat) / (5 : Rat))))) : Rat) : ℝ) < (((((10 : Rat) / (3 : Rat))) : Rat) : ℝ) :=
  ofRats_lt_real (comparison_record_at Strict003.checked 0
    (by change 0 < 16; omega))

-- F34: [25/24+(81/200)(7/4)]/[(5/12)(8/5)]<10/3    [lambda/gamma, cap 3]
theorem fixed_F34 : (((((((25 : Rat) / (24 : Rat)) + (((81 : Rat) / (200 : Rat)) * ((7 : Rat) / (4 : Rat)))) / (((5 : Rat) / (12 : Rat)) * ((8 : Rat) / (5 : Rat))))) : Rat) : ℝ) < (((((10 : Rat) / (3 : Rat))) : Rat) : ℝ) :=
  ofRats_lt_real (comparison_record_at Strict003.checked 1
    (by change 1 < 16; omega))

-- F35: [25/24+(81/200)(2)]/[(5/12)(9/5)]<10/3    [lambda/gamma, cap 4]
theorem fixed_F35 : (((((((25 : Rat) / (24 : Rat)) + (((81 : Rat) / (200 : Rat)) * (2 : Rat))) / (((5 : Rat) / (12 : Rat)) * ((9 : Rat) / (5 : Rat))))) : Rat) : ℝ) < (((((10 : Rat) / (3 : Rat))) : Rat) : ℝ) :=
  ofRats_lt_real (comparison_record_at Strict003.checked 2
    (by change 2 < 16; omega))

-- F36: [25/24+(81/200)(7/3)]/[(5/12)(21/10)]<10/3    [lambda/gamma, cap 5]
theorem fixed_F36 : (((((((25 : Rat) / (24 : Rat)) + (((81 : Rat) / (200 : Rat)) * ((7 : Rat) / (3 : Rat)))) / (((5 : Rat) / (12 : Rat)) * ((21 : Rat) / (10 : Rat))))) : Rat) : ℝ) < (((((10 : Rat) / (3 : Rat))) : Rat) : ℝ) :=
  ofRats_lt_real (comparison_record_at Strict003.checked 3
    (by change 3 < 16; omega))

-- F37: \beta_+(263/200)<21/25    [CA face cover, cap 1]
theorem fixed_F37 : (((b05.hi) : Rat) : ℝ) < (((((21 : Rat) / (25 : Rat))) : Rat) : ℝ) :=
  ofRats_lt_real (comparison_record_at Strict003.checked 4
    (by change 4 < 16; omega))

-- F38: \beta_+(3/2)<23/25    [CA face cover, cap 2]
theorem fixed_F38 : (((b06.hi) : Rat) : ℝ) < (((((23 : Rat) / (25 : Rat))) : Rat) : ℝ) :=
  ofRats_lt_real (comparison_record_at Strict003.checked 5
    (by change 5 < 16; omega))

-- F39: \beta_+(7/4)<51/50    [CA face cover, cap 3]
theorem fixed_F39 : (((b07.hi) : Rat) : ℝ) < (((((51 : Rat) / (50 : Rat))) : Rat) : ℝ) :=
  ofRats_lt_real (comparison_record_at Strict003.checked 6
    (by change 6 < 16; omega))

-- F40: \beta_+(2)<11/10    [CA face cover, cap 4]
theorem fixed_F40 : (((b08.hi) : Rat) : ℝ) < (((((11 : Rat) / (10 : Rat))) : Rat) : ℝ) :=
  ofRats_lt_real (comparison_record_at Strict003.checked 7
    (by change 7 < 16; omega))

-- F41: \beta_+(7/3)<121/100    [CA face cover, cap 5]
theorem fixed_F41 : (((b09.hi) : Rat) : ℝ) < (((((121 : Rat) / (100 : Rat))) : Rat) : ℝ) :=
  ofRats_lt_real (comparison_record_at Strict003.checked 8
    (by change 8 < 16; omega))

-- F42: N_4(263/463,6/5)>1    [childless diagonal, cap 1]
theorem fixed_F42 : ((((1 : Rat)) : Rat) : ℝ) < ((((nFour (((263 : Rat) / (463 : Rat))) (((6 : Rat) / (5 : Rat))))) : Rat) : ℝ) :=
  ofRats_lt_real (comparison_record_at Strict003.checked 9
    (by change 9 < 16; omega))

-- F43: N_5(263/463,6/5)>3    [childless diagonal, cap 1]
theorem fixed_F43 : ((((3 : Rat)) : Rat) : ℝ) < ((((nFive (((263 : Rat) / (463 : Rat))) (((6 : Rat) / (5 : Rat))))) : Rat) : ℝ) :=
  ofRats_lt_real (comparison_record_at Strict003.checked 10
    (by change 10 < 16; omega))

-- F44: N_4(3/5,7/5)>4    [childless diagonal, cap 2]
theorem fixed_F44 : ((((4 : Rat)) : Rat) : ℝ) < ((((nFour (((3 : Rat) / (5 : Rat))) (((7 : Rat) / (5 : Rat))))) : Rat) : ℝ) :=
  ofRats_lt_real (comparison_record_at Strict003.checked 11
    (by change 11 < 16; omega))

-- F45: N_5(3/5,7/5)>5    [childless diagonal, cap 2]
theorem fixed_F45 : ((((5 : Rat)) : Rat) : ℝ) < ((((nFive (((3 : Rat) / (5 : Rat))) (((7 : Rat) / (5 : Rat))))) : Rat) : ℝ) :=
  ofRats_lt_real (comparison_record_at Strict003.checked 12
    (by change 12 < 16; omega))

-- F46: N_4(7/11,8/5)>5    [childless diagonal, cap 3]
theorem fixed_F46 : ((((5 : Rat)) : Rat) : ℝ) < ((((nFour (((7 : Rat) / (11 : Rat))) (((8 : Rat) / (5 : Rat))))) : Rat) : ℝ) :=
  ofRats_lt_real (comparison_record_at Strict003.checked 13
    (by change 13 < 16; omega))

-- F47: N_5(7/11,8/5)>5    [childless diagonal, cap 3]
theorem fixed_F47 : ((((5 : Rat)) : Rat) : ℝ) < ((((nFive (((7 : Rat) / (11 : Rat))) (((8 : Rat) / (5 : Rat))))) : Rat) : ℝ) :=
  ofRats_lt_real (comparison_record_at Strict003.checked 14
    (by change 14 < 16; omega))

-- F48: N_4(2/3,9/5)>7    [childless diagonal, cap 4]
theorem fixed_F48 : ((((7 : Rat)) : Rat) : ℝ) < ((((nFour (((2 : Rat) / (3 : Rat))) (((9 : Rat) / (5 : Rat))))) : Rat) : ℝ) :=
  ofRats_lt_real (comparison_record_at Strict003.checked 15
    (by change 15 < 16; omega))

end Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords

#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F33
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F33
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F34
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F34
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F35
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F35
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F36
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F36
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F37
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F37
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F38
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F38
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F39
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F39
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F40
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F40
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F41
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F41
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F42
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F42
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F43
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F43
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F44
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F44
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F45
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F45
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F46
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F46
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F47
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F47
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F48
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F48
