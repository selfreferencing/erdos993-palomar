module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceRecordSelection
public import Erdos993Lean.Analytic.V213.FreeCountRationalTransfer
public import Erdos993Lean.ExactComparisons.F3All.ParameterEquality001

/-! Every assertion selects an already checked original
record at its reviewed index. Real comparisons use the generic exact Rat cast.
No rational comparison is recomputed, and no analytic closure is asserted. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords

open Erdos993Lean.ExactComparisons Erdos993Lean.ExactComparisons.F3All
open Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates
open Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes

-- H1.M: 267809/60000 = (25/24)/(5*(6/5)/12) + (1+(81/200)/(5*(6/5)/12))*(263/200)
theorem parameter_H1_M : (((((267809 : Rat) / (60000 : Rat))) : Rat) : ℝ) = (((((((25 : Rat) / (24 : Rat)) / (((5 : Rat) * ((6 : Rat) / (5 : Rat))) / (12 : Rat))) + (((1 : Rat) + (((81 : Rat) / (200 : Rat)) / (((5 : Rat) * ((6 : Rat) / (5 : Rat))) / (12 : Rat)))) * ((263 : Rat) / (200 : Rat))))) : Rat) : ℝ) :=
  ofRats_eq_real (comparison_record_at ParameterEquality001.checked 0
    (by change 0 < 27; omega))

-- H1.R: 405884/267809 = 1 + (1+(3/4))*(263/200)/(267809/60000)
theorem parameter_H1_R : (((((405884 : Rat) / (267809 : Rat))) : Rat) : ℝ) = (((((1 : Rat) + ((((1 : Rat) + ((3 : Rat) / (4 : Rat))) * ((263 : Rat) / (200 : Rat))) / ((267809 : Rat) / (60000 : Rat))))) : Rat) : ℝ) :=
  ofRats_eq_real (comparison_record_at ParameterEquality001.checked 1
    (by change 1 < 27; omega))

-- H2.M: 3029/700 = (25/24)/(5*(7/5)/12) + (1+(81/200)/(5*(7/5)/12))*(3/2)
theorem parameter_H2_M : (((((3029 : Rat) / (700 : Rat))) : Rat) : ℝ) = (((((((25 : Rat) / (24 : Rat)) / (((5 : Rat) * ((7 : Rat) / (5 : Rat))) / (12 : Rat))) + (((1 : Rat) + (((81 : Rat) / (200 : Rat)) / (((5 : Rat) * ((7 : Rat) / (5 : Rat))) / (12 : Rat)))) * ((3 : Rat) / (2 : Rat))))) : Rat) : ℝ) :=
  ofRats_eq_real (comparison_record_at ParameterEquality001.checked 2
    (by change 2 < 27; omega))

-- H2.R: 9733/6058 = 1 + (1+(3/4))*(3/2)/(3029/700)
theorem parameter_H2_R : (((((9733 : Rat) / (6058 : Rat))) : Rat) : ℝ) = (((((1 : Rat) + ((((1 : Rat) + ((3 : Rat) / (4 : Rat))) * ((3 : Rat) / (2 : Rat))) / ((3029 : Rat) / (700 : Rat))))) : Rat) : ℝ) :=
  ofRats_eq_real (comparison_record_at ParameterEquality001.checked 3
    (by change 3 < 27; omega))

-- H3.M: 7001/1600 = (25/24)/(5*(8/5)/12) + (1+(81/200)/(5*(8/5)/12))*(7/4)
theorem parameter_H3_M : (((((7001 : Rat) / (1600 : Rat))) : Rat) : ℝ) = (((((((25 : Rat) / (24 : Rat)) / (((5 : Rat) * ((8 : Rat) / (5 : Rat))) / (12 : Rat))) + (((1 : Rat) + (((81 : Rat) / (200 : Rat)) / (((5 : Rat) * ((8 : Rat) / (5 : Rat))) / (12 : Rat)))) * ((7 : Rat) / (4 : Rat))))) : Rat) : ℝ) :=
  ofRats_eq_real (comparison_record_at ParameterEquality001.checked 4
    (by change 4 < 27; omega))

-- H3.R: 11201/7001 = 1 + (1+(1/2))*(7/4)/(7001/1600)
theorem parameter_H3_R : (((((11201 : Rat) / (7001 : Rat))) : Rat) : ℝ) = (((((1 : Rat) + ((((1 : Rat) + ((1 : Rat) / (2 : Rat))) * ((7 : Rat) / (4 : Rat))) / ((7001 : Rat) / (1600 : Rat))))) : Rat) : ℝ) :=
  ofRats_eq_real (comparison_record_at ParameterEquality001.checked 5
    (by change 5 < 27; omega))

-- H4.M: 2011/450 = (25/24)/(5*(9/5)/12) + (1+(81/200)/(5*(9/5)/12))*(2)
theorem parameter_H4_M : (((((2011 : Rat) / (450 : Rat))) : Rat) : ℝ) = (((((((25 : Rat) / (24 : Rat)) / (((5 : Rat) * ((9 : Rat) / (5 : Rat))) / (12 : Rat))) + (((1 : Rat) + (((81 : Rat) / (200 : Rat)) / (((5 : Rat) * ((9 : Rat) / (5 : Rat))) / (12 : Rat)))) * (2 : Rat)))) : Rat) : ℝ) :=
  ofRats_eq_real (comparison_record_at ParameterEquality001.checked 6
    (by change 6 < 27; omega))

-- H4.R: 3361/2011 = 1 + (1+(1/2))*(2)/(2011/450)
theorem parameter_H4_R : (((((3361 : Rat) / (2011 : Rat))) : Rat) : ℝ) = (((((1 : Rat) + ((((1 : Rat) + ((1 : Rat) / (2 : Rat))) * (2 : Rat)) / ((2011 : Rat) / (450 : Rat))))) : Rat) : ℝ) :=
  ofRats_eq_real (comparison_record_at ParameterEquality001.checked 7
    (by change 7 < 27; omega))

-- H5.M: 2417/525 = (25/24)/(5*(21/10)/12) + (1+(81/200)/(5*(21/10)/12))*(7/3)
theorem parameter_H5_M : (((((2417 : Rat) / (525 : Rat))) : Rat) : ℝ) = (((((((25 : Rat) / (24 : Rat)) / (((5 : Rat) * ((21 : Rat) / (10 : Rat))) / (12 : Rat))) + (((1 : Rat) + (((81 : Rat) / (200 : Rat)) / (((5 : Rat) * ((21 : Rat) / (10 : Rat))) / (12 : Rat)))) * ((7 : Rat) / (3 : Rat))))) : Rat) : ℝ) :=
  ofRats_eq_real (comparison_record_at ParameterEquality001.checked 8
    (by change 8 < 27; omega))

-- H5.R: 8509/4834 = 1 + (1+(1/2))*(7/3)/(2417/525)
theorem parameter_H5_R : (((((8509 : Rat) / (4834 : Rat))) : Rat) : ℝ) = (((((1 : Rat) + ((((1 : Rat) + ((1 : Rat) / (2 : Rat))) * ((7 : Rat) / (3 : Rat))) / ((2417 : Rat) / (525 : Rat))))) : Rat) : ℝ) :=
  ofRats_eq_real (comparison_record_at ParameterEquality001.checked 9
    (by change 9 < 27; omega))

-- K1.H: 7/8 = 1 - (1/3)/(2*(1+(1/3))).
theorem parameter_K1_H : (((((7 : Rat) / (8 : Rat))) : Rat) : ℝ) = (((((1 : Rat) - (((1 : Rat) / (3 : Rat)) / ((2 : Rat) * ((1 : Rat) + ((1 : Rat) / (3 : Rat))))))) : Rat) : ℝ) :=
  ofRats_eq_real (comparison_record_at ParameterEquality001.checked 10
    (by change 10 < 27; omega))

-- K1.K: 4097/1500 = (25/24+(81/200)*(4/5))/(5*(6/5)/12).
theorem parameter_K1_K : (((((4097 : Rat) / (1500 : Rat))) : Rat) : ℝ) = (((((((25 : Rat) / (24 : Rat)) + (((81 : Rat) / (200 : Rat)) * ((4 : Rat) / (5 : Rat)))) / (((5 : Rat) * ((6 : Rat) / (5 : Rat))) / (12 : Rat)))) : Rat) : ℝ) :=
  ofRats_eq_real (comparison_record_at ParameterEquality001.checked 11
    (by change 11 < 27; omega))

-- K2.H: 7/9 = 1 - (4/5)/(2*(1+(4/5))).
theorem parameter_K2_H : (((((7 : Rat) / (9 : Rat))) : Rat) : ℝ) = (((((1 : Rat) - (((4 : Rat) / (5 : Rat)) / ((2 : Rat) * ((1 : Rat) + ((4 : Rat) / (5 : Rat))))))) : Rat) : ℝ) :=
  ofRats_eq_real (comparison_record_at ParameterEquality001.checked 12
    (by change 12 < 27; omega))

-- K2.K: 188909/60000 = (25/24+(81/200)*(263/200))/(5*(6/5)/12).
theorem parameter_K2_K : (((((188909 : Rat) / (60000 : Rat))) : Rat) : ℝ) = (((((((25 : Rat) / (24 : Rat)) + (((81 : Rat) / (200 : Rat)) * ((263 : Rat) / (200 : Rat)))) / (((5 : Rat) * ((6 : Rat) / (5 : Rat))) / (12 : Rat)))) : Rat) : ℝ) :=
  ofRats_eq_real (comparison_record_at ParameterEquality001.checked 13
    (by change 13 < 27; omega))

-- K3.H: 663/926 = 1 - (263/200)/(2*(1+(263/200))).
theorem parameter_K3_H : (((((663 : Rat) / (926 : Rat))) : Rat) : ℝ) = (((((1 : Rat) - (((263 : Rat) / (200 : Rat)) / ((2 : Rat) * ((1 : Rat) + ((263 : Rat) / (200 : Rat))))))) : Rat) : ℝ) :=
  ofRats_eq_real (comparison_record_at ParameterEquality001.checked 14
    (by change 14 < 27; omega))

-- K3.K: 1979/700 = (25/24+(81/200)*(3/2))/(5*(7/5)/12).
theorem parameter_K3_K : (((((1979 : Rat) / (700 : Rat))) : Rat) : ℝ) = (((((((25 : Rat) / (24 : Rat)) + (((81 : Rat) / (200 : Rat)) * ((3 : Rat) / (2 : Rat)))) / (((5 : Rat) * ((7 : Rat) / (5 : Rat))) / (12 : Rat)))) : Rat) : ℝ) :=
  ofRats_eq_real (comparison_record_at ParameterEquality001.checked 15
    (by change 15 < 27; omega))

-- K4.H: 7/10 = 1 - (3/2)/(2*(1+(3/2))).
theorem parameter_K4_H : (((((7 : Rat) / (10 : Rat))) : Rat) : ℝ) = (((((1 : Rat) - (((3 : Rat) / (2 : Rat)) / ((2 : Rat) * ((1 : Rat) + ((3 : Rat) / (2 : Rat))))))) : Rat) : ℝ) :=
  ofRats_eq_real (comparison_record_at ParameterEquality001.checked 16
    (by change 16 < 27; omega))

-- K4.K: 4201/1600 = (25/24+(81/200)*(7/4))/(5*(8/5)/12).
theorem parameter_K4_K : (((((4201 : Rat) / (1600 : Rat))) : Rat) : ℝ) = (((((((25 : Rat) / (24 : Rat)) + (((81 : Rat) / (200 : Rat)) * ((7 : Rat) / (4 : Rat)))) / (((5 : Rat) * ((8 : Rat) / (5 : Rat))) / (12 : Rat)))) : Rat) : ℝ) :=
  ofRats_eq_real (comparison_record_at ParameterEquality001.checked 17
    (by change 17 < 27; omega))

-- K5.H: 15/22 = 1 - (7/4)/(2*(1+(7/4))).
theorem parameter_K5_H : (((((15 : Rat) / (22 : Rat))) : Rat) : ℝ) = (((((1 : Rat) - (((7 : Rat) / (4 : Rat)) / ((2 : Rat) * ((1 : Rat) + ((7 : Rat) / (4 : Rat))))))) : Rat) : ℝ) :=
  ofRats_eq_real (comparison_record_at ParameterEquality001.checked 18
    (by change 18 < 27; omega))

-- K5.K: 1111/450 = (25/24+(81/200)*(2))/(5*(9/5)/12).
theorem parameter_K5_K : (((((1111 : Rat) / (450 : Rat))) : Rat) : ℝ) = (((((((25 : Rat) / (24 : Rat)) + (((81 : Rat) / (200 : Rat)) * (2 : Rat))) / (((5 : Rat) * ((9 : Rat) / (5 : Rat))) / (12 : Rat)))) : Rat) : ℝ) :=
  ofRats_eq_real (comparison_record_at ParameterEquality001.checked 19
    (by change 19 < 27; omega))

-- K6.H: 2/3 = 1 - (2)/(2*(1+(2))).
theorem parameter_K6_H : (((((2 : Rat) / (3 : Rat))) : Rat) : ℝ) = (((((1 : Rat) - ((2 : Rat) / ((2 : Rat) * ((1 : Rat) + (2 : Rat)))))) : Rat) : ℝ) :=
  ofRats_eq_real (comparison_record_at ParameterEquality001.checked 20
    (by change 20 < 27; omega))

-- K6.K: 1192/525 = (25/24+(81/200)*(7/3))/(5*(21/10)/12).
theorem parameter_K6_K : (((((1192 : Rat) / (525 : Rat))) : Rat) : ℝ) = (((((((25 : Rat) / (24 : Rat)) + (((81 : Rat) / (200 : Rat)) * ((7 : Rat) / (3 : Rat)))) / (((5 : Rat) * ((21 : Rat) / (10 : Rat))) / (12 : Rat)))) : Rat) : ℝ) :=
  ofRats_eq_real (comparison_record_at ParameterEquality001.checked 21
    (by change 21 < 27; omega))

-- Q1: 263/463 = (263/200)/(1+(263/200)).
theorem parameter_Q1 : (((((263 : Rat) / (463 : Rat))) : Rat) : ℝ) = ((((((263 : Rat) / (200 : Rat)) / ((1 : Rat) + ((263 : Rat) / (200 : Rat))))) : Rat) : ℝ) :=
  ofRats_eq_real (comparison_record_at ParameterEquality001.checked 22
    (by change 22 < 27; omega))

-- Q2: 3/5 = (3/2)/(1+(3/2)).
theorem parameter_Q2 : (((((3 : Rat) / (5 : Rat))) : Rat) : ℝ) = ((((((3 : Rat) / (2 : Rat)) / ((1 : Rat) + ((3 : Rat) / (2 : Rat))))) : Rat) : ℝ) :=
  ofRats_eq_real (comparison_record_at ParameterEquality001.checked 23
    (by change 23 < 27; omega))

-- Q3: 7/11 = (7/4)/(1+(7/4)).
theorem parameter_Q3 : (((((7 : Rat) / (11 : Rat))) : Rat) : ℝ) = ((((((7 : Rat) / (4 : Rat)) / ((1 : Rat) + ((7 : Rat) / (4 : Rat))))) : Rat) : ℝ) :=
  ofRats_eq_real (comparison_record_at ParameterEquality001.checked 24
    (by change 24 < 27; omega))

-- Q4: 2/3 = (2)/(1+(2)).
theorem parameter_Q4 : (((((2 : Rat) / (3 : Rat))) : Rat) : ℝ) = (((((2 : Rat) / ((1 : Rat) + (2 : Rat)))) : Rat) : ℝ) :=
  ofRats_eq_real (comparison_record_at ParameterEquality001.checked 25
    (by change 25 < 27; omega))

-- Q5: 7/10 = (7/3)/(1+(7/3)).
theorem parameter_Q5 : (((((7 : Rat) / (10 : Rat))) : Rat) : ℝ) = ((((((7 : Rat) / (3 : Rat)) / ((1 : Rat) + ((7 : Rat) / (3 : Rat))))) : Rat) : ℝ) :=
  ofRats_eq_real (comparison_record_at ParameterEquality001.checked 26
    (by change 26 < 27; omega))

end Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords

#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.parameter_H1_M
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.parameter_H1_M
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.parameter_H1_R
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.parameter_H1_R
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.parameter_H2_M
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.parameter_H2_M
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.parameter_H2_R
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.parameter_H2_R
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.parameter_H3_M
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.parameter_H3_M
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.parameter_H3_R
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.parameter_H3_R
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.parameter_H4_M
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.parameter_H4_M
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.parameter_H4_R
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.parameter_H4_R
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.parameter_H5_M
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.parameter_H5_M
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.parameter_H5_R
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.parameter_H5_R
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.parameter_K1_H
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.parameter_K1_H
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.parameter_K1_K
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.parameter_K1_K
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.parameter_K2_H
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.parameter_K2_H
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.parameter_K2_K
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.parameter_K2_K
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.parameter_K3_H
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.parameter_K3_H
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.parameter_K3_K
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.parameter_K3_K
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.parameter_K4_H
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.parameter_K4_H
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.parameter_K4_K
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.parameter_K4_K
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.parameter_K5_H
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.parameter_K5_H
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.parameter_K5_K
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.parameter_K5_K
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.parameter_K6_H
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.parameter_K6_H
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.parameter_K6_K
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.parameter_K6_K
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.parameter_Q1
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.parameter_Q1
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.parameter_Q2
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.parameter_Q2
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.parameter_Q3
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.parameter_Q3
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.parameter_Q4
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.parameter_Q4
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.parameter_Q5
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedScalarRecords.parameter_Q5
