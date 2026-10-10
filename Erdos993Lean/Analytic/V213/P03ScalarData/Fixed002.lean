module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.FreeCountRationalTransfer
public import Erdos993Lean.ExactComparisons.F3All.Strict002

/-! Every assertion selects an already checked original
record at its reviewed index. Real comparisons use the generic exact Rat cast.
No rational comparison is recomputed, and no analytic closure is asserted. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords

open Erdos993Lean.ExactComparisons Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates
open Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes

-- F17: 1-(267809/60000)/(181/40)-(263/200)^2(3/8)^{4}/4>0    [negative L, cap 1]
theorem fixed_F17 : ((((0 : Rat)) : Rat) : ℝ) < ((((((1 : Rat) - (((267809 : Rat) / (60000 : Rat)) / ((181 : Rat) / (40 : Rat)))) - (((((263 : Rat) / (200 : Rat)) ^ 2) * (((3 : Rat) / (8 : Rat)) ^ 4)) / (4 : Rat)))) : Rat) : ℝ) :=
  ofRats_lt_real (comparison_record_at Strict002.checked 0
    (by change 0 < 16; omega))

-- F18: E_5(9733/6058)>49/10    [negative L, cap 2]
theorem fixed_F18 : (((((49 : Rat) / (10 : Rat))) : Rat) : ℝ) < ((((expFive (((9733 : Rat) / (6058 : Rat))))) : Rat) : ℝ) :=
  ofRats_lt_real (comparison_record_at Strict002.checked 1
    (by change 1 < 16; omega))

-- F19: 1-(3029/700)/(49/10)-(3/2)^2(3/8)^{4}/4>0    [negative L, cap 2]
theorem fixed_F19 : ((((0 : Rat)) : Rat) : ℝ) < ((((((1 : Rat) - (((3029 : Rat) / (700 : Rat)) / ((49 : Rat) / (10 : Rat)))) - (((((3 : Rat) / (2 : Rat)) ^ 2) * (((3 : Rat) / (8 : Rat)) ^ 4)) / (4 : Rat)))) : Rat) : ℝ) :=
  ofRats_lt_real (comparison_record_at Strict002.checked 2
    (by change 2 < 16; omega))

-- F20: E_5(11201/7001)>49/10    [negative L, cap 3]
theorem fixed_F20 : (((((49 : Rat) / (10 : Rat))) : Rat) : ℝ) < ((((expFive (((11201 : Rat) / (7001 : Rat))))) : Rat) : ℝ) :=
  ofRats_lt_real (comparison_record_at Strict002.checked 3
    (by change 3 < 16; omega))

-- F21: 1-(7001/1600)/(49/10)-(7/4)^2(3/8)^{3}/4>0    [negative L, cap 3]
theorem fixed_F21 : ((((0 : Rat)) : Rat) : ℝ) < ((((((1 : Rat) - (((7001 : Rat) / (1600 : Rat)) / ((49 : Rat) / (10 : Rat)))) - (((((7 : Rat) / (4 : Rat)) ^ 2) * (((3 : Rat) / (8 : Rat)) ^ 3)) / (4 : Rat)))) : Rat) : ℝ) :=
  ofRats_lt_real (comparison_record_at Strict002.checked 4
    (by change 4 < 16; omega))

-- F22: E_5(3361/2011)>21/4    [negative L, cap 4]
theorem fixed_F22 : (((((21 : Rat) / (4 : Rat))) : Rat) : ℝ) < ((((expFive (((3361 : Rat) / (2011 : Rat))))) : Rat) : ℝ) :=
  ofRats_lt_real (comparison_record_at Strict002.checked 5
    (by change 5 < 16; omega))

-- F23: 1-(2011/450)/(21/4)-(2)^2(3/8)^{3}/4>0    [negative L, cap 4]
theorem fixed_F23 : ((((0 : Rat)) : Rat) : ℝ) < ((((((1 : Rat) - (((2011 : Rat) / (450 : Rat)) / ((21 : Rat) / (4 : Rat)))) - ((((2 : Rat) ^ 2) * (((3 : Rat) / (8 : Rat)) ^ 3)) / (4 : Rat)))) : Rat) : ℝ) :=
  ofRats_lt_real (comparison_record_at Strict002.checked 6
    (by change 6 < 16; omega))

-- F24: E_5(8509/4834)>23/4    [negative L, cap 5]
theorem fixed_F24 : (((((23 : Rat) / (4 : Rat))) : Rat) : ℝ) < ((((expFive (((8509 : Rat) / (4834 : Rat))))) : Rat) : ℝ) :=
  ofRats_lt_real (comparison_record_at Strict002.checked 7
    (by change 7 < 16; omega))

-- F25: 1-(2417/525)/(23/4)-(7/3)^2(3/8)^{3}/4>0    [negative L, cap 5]
theorem fixed_F25 : ((((0 : Rat)) : Rat) : ℝ) < ((((((1 : Rat) - (((2417 : Rat) / (525 : Rat)) / ((23 : Rat) / (4 : Rat)))) - (((((7 : Rat) / (3 : Rat)) ^ 2) * (((3 : Rat) / (8 : Rat)) ^ 3)) / (4 : Rat)))) : Rat) : ℝ) :=
  ofRats_lt_real (comparison_record_at Strict002.checked 8
    (by change 8 < 16; omega))

-- F26: (4097/1500)(7/8)+[(4097/1500)(1-7/8)+(4/5)/2]^2/[4(4097/1500+(4/5)/4)]<8/3    [ell decreases in lambda, row 1]
theorem fixed_F26 : (((((((4097 : Rat) / (1500 : Rat)) * ((7 : Rat) / (8 : Rat))) + ((((((4097 : Rat) / (1500 : Rat)) * ((1 : Rat) - ((7 : Rat) / (8 : Rat)))) + (((4 : Rat) / (5 : Rat)) / (2 : Rat))) ^ 2) / ((4 : Rat) * (((4097 : Rat) / (1500 : Rat)) + (((4 : Rat) / (5 : Rat)) / (4 : Rat))))))) : Rat) : ℝ) < (((((8 : Rat) / (3 : Rat))) : Rat) : ℝ) :=
  ofRats_lt_real (comparison_record_at Strict002.checked 9
    (by change 9 < 16; omega))

-- F27: (188909/60000)(7/9)+[(188909/60000)(1-7/9)+(263/200)/2]^2/[4(188909/60000+(263/200)/4)]<8/3    [ell decreases in lambda, row 2]
theorem fixed_F27 : (((((((188909 : Rat) / (60000 : Rat)) * ((7 : Rat) / (9 : Rat))) + ((((((188909 : Rat) / (60000 : Rat)) * ((1 : Rat) - ((7 : Rat) / (9 : Rat)))) + (((263 : Rat) / (200 : Rat)) / (2 : Rat))) ^ 2) / ((4 : Rat) * (((188909 : Rat) / (60000 : Rat)) + (((263 : Rat) / (200 : Rat)) / (4 : Rat))))))) : Rat) : ℝ) < (((((8 : Rat) / (3 : Rat))) : Rat) : ℝ) :=
  ofRats_lt_real (comparison_record_at Strict002.checked 10
    (by change 10 < 16; omega))

-- F28: (1979/700)(663/926)+[(1979/700)(1-663/926)+(3/2)/2]^2/[4(1979/700+(3/2)/4)]<8/3    [ell decreases in lambda, row 3]
theorem fixed_F28 : (((((((1979 : Rat) / (700 : Rat)) * ((663 : Rat) / (926 : Rat))) + ((((((1979 : Rat) / (700 : Rat)) * ((1 : Rat) - ((663 : Rat) / (926 : Rat)))) + (((3 : Rat) / (2 : Rat)) / (2 : Rat))) ^ 2) / ((4 : Rat) * (((1979 : Rat) / (700 : Rat)) + (((3 : Rat) / (2 : Rat)) / (4 : Rat))))))) : Rat) : ℝ) < (((((8 : Rat) / (3 : Rat))) : Rat) : ℝ) :=
  ofRats_lt_real (comparison_record_at Strict002.checked 11
    (by change 11 < 16; omega))

-- F29: (4201/1600)(7/10)+[(4201/1600)(1-7/10)+(7/4)/2]^2/[4(4201/1600+(7/4)/4)]<8/3    [ell decreases in lambda, row 4]
theorem fixed_F29 : (((((((4201 : Rat) / (1600 : Rat)) * ((7 : Rat) / (10 : Rat))) + ((((((4201 : Rat) / (1600 : Rat)) * ((1 : Rat) - ((7 : Rat) / (10 : Rat)))) + (((7 : Rat) / (4 : Rat)) / (2 : Rat))) ^ 2) / ((4 : Rat) * (((4201 : Rat) / (1600 : Rat)) + (((7 : Rat) / (4 : Rat)) / (4 : Rat))))))) : Rat) : ℝ) < (((((8 : Rat) / (3 : Rat))) : Rat) : ℝ) :=
  ofRats_lt_real (comparison_record_at Strict002.checked 12
    (by change 12 < 16; omega))

-- F30: (1111/450)(15/22)+[(1111/450)(1-15/22)+(2)/2]^2/[4(1111/450+(2)/4)]<8/3    [ell decreases in lambda, row 5]
theorem fixed_F30 : (((((((1111 : Rat) / (450 : Rat)) * ((15 : Rat) / (22 : Rat))) + ((((((1111 : Rat) / (450 : Rat)) * ((1 : Rat) - ((15 : Rat) / (22 : Rat)))) + ((2 : Rat) / (2 : Rat))) ^ 2) / ((4 : Rat) * (((1111 : Rat) / (450 : Rat)) + ((2 : Rat) / (4 : Rat))))))) : Rat) : ℝ) < (((((8 : Rat) / (3 : Rat))) : Rat) : ℝ) :=
  ofRats_lt_real (comparison_record_at Strict002.checked 13
    (by change 13 < 16; omega))

-- F31: (1192/525)(2/3)+[(1192/525)(1-2/3)+(7/3)/2]^2/[4(1192/525+(7/3)/4)]<8/3    [ell decreases in lambda, row 6]
theorem fixed_F31 : (((((((1192 : Rat) / (525 : Rat)) * ((2 : Rat) / (3 : Rat))) + ((((((1192 : Rat) / (525 : Rat)) * ((1 : Rat) - ((2 : Rat) / (3 : Rat)))) + (((7 : Rat) / (3 : Rat)) / (2 : Rat))) ^ 2) / ((4 : Rat) * (((1192 : Rat) / (525 : Rat)) + (((7 : Rat) / (3 : Rat)) / (4 : Rat))))))) : Rat) : ℝ) < (((((8 : Rat) / (3 : Rat))) : Rat) : ℝ) :=
  ofRats_lt_real (comparison_record_at Strict002.checked 14
    (by change 14 < 16; omega))

-- F32: [25/24+(81/200)(263/200)]/[(5/12)(6/5)]<10/3    [lambda/gamma, cap 1]
theorem fixed_F32 : (((((((25 : Rat) / (24 : Rat)) + (((81 : Rat) / (200 : Rat)) * ((263 : Rat) / (200 : Rat)))) / (((5 : Rat) / (12 : Rat)) * ((6 : Rat) / (5 : Rat))))) : Rat) : ℝ) < (((((10 : Rat) / (3 : Rat))) : Rat) : ℝ) :=
  ofRats_lt_real (comparison_record_at Strict002.checked 15
    (by change 15 < 16; omega))

end Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords

#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F17
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F17
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F18
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F18
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F19
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F19
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F20
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F20
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F21
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F21
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F22
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F22
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F23
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F23
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F24
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F24
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F25
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F25
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F26
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F26
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F27
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F27
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F28
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F28
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F29
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F29
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F30
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F30
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F31
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F31
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F32
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.fixed_F32
