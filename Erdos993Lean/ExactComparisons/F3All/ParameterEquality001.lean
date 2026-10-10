module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.ParameterEquality001

def records : List Comparison := [
  -- H1.M: 267809/60000 = (25/24)/(5*(6/5)/12) + (1+(81/200)/(5*(6/5)/12))*(263/200)
  Comparison.ofRats (((267809 : Rat) / (60000 : Rat))) (((((25 : Rat) / (24 : Rat)) / (((5 : Rat) * ((6 : Rat) / (5 : Rat))) / (12 : Rat))) + (((1 : Rat) + (((81 : Rat) / (200 : Rat)) / (((5 : Rat) * ((6 : Rat) / (5 : Rat))) / (12 : Rat)))) * ((263 : Rat) / (200 : Rat))))) .eq,
  -- H1.R: 405884/267809 = 1 + (1+(3/4))*(263/200)/(267809/60000)
  Comparison.ofRats (((405884 : Rat) / (267809 : Rat))) (((1 : Rat) + ((((1 : Rat) + ((3 : Rat) / (4 : Rat))) * ((263 : Rat) / (200 : Rat))) / ((267809 : Rat) / (60000 : Rat))))) .eq,
  -- H2.M: 3029/700 = (25/24)/(5*(7/5)/12) + (1+(81/200)/(5*(7/5)/12))*(3/2)
  Comparison.ofRats (((3029 : Rat) / (700 : Rat))) (((((25 : Rat) / (24 : Rat)) / (((5 : Rat) * ((7 : Rat) / (5 : Rat))) / (12 : Rat))) + (((1 : Rat) + (((81 : Rat) / (200 : Rat)) / (((5 : Rat) * ((7 : Rat) / (5 : Rat))) / (12 : Rat)))) * ((3 : Rat) / (2 : Rat))))) .eq,
  -- H2.R: 9733/6058 = 1 + (1+(3/4))*(3/2)/(3029/700)
  Comparison.ofRats (((9733 : Rat) / (6058 : Rat))) (((1 : Rat) + ((((1 : Rat) + ((3 : Rat) / (4 : Rat))) * ((3 : Rat) / (2 : Rat))) / ((3029 : Rat) / (700 : Rat))))) .eq,
  -- H3.M: 7001/1600 = (25/24)/(5*(8/5)/12) + (1+(81/200)/(5*(8/5)/12))*(7/4)
  Comparison.ofRats (((7001 : Rat) / (1600 : Rat))) (((((25 : Rat) / (24 : Rat)) / (((5 : Rat) * ((8 : Rat) / (5 : Rat))) / (12 : Rat))) + (((1 : Rat) + (((81 : Rat) / (200 : Rat)) / (((5 : Rat) * ((8 : Rat) / (5 : Rat))) / (12 : Rat)))) * ((7 : Rat) / (4 : Rat))))) .eq,
  -- H3.R: 11201/7001 = 1 + (1+(1/2))*(7/4)/(7001/1600)
  Comparison.ofRats (((11201 : Rat) / (7001 : Rat))) (((1 : Rat) + ((((1 : Rat) + ((1 : Rat) / (2 : Rat))) * ((7 : Rat) / (4 : Rat))) / ((7001 : Rat) / (1600 : Rat))))) .eq,
  -- H4.M: 2011/450 = (25/24)/(5*(9/5)/12) + (1+(81/200)/(5*(9/5)/12))*(2)
  Comparison.ofRats (((2011 : Rat) / (450 : Rat))) (((((25 : Rat) / (24 : Rat)) / (((5 : Rat) * ((9 : Rat) / (5 : Rat))) / (12 : Rat))) + (((1 : Rat) + (((81 : Rat) / (200 : Rat)) / (((5 : Rat) * ((9 : Rat) / (5 : Rat))) / (12 : Rat)))) * (2 : Rat)))) .eq,
  -- H4.R: 3361/2011 = 1 + (1+(1/2))*(2)/(2011/450)
  Comparison.ofRats (((3361 : Rat) / (2011 : Rat))) (((1 : Rat) + ((((1 : Rat) + ((1 : Rat) / (2 : Rat))) * (2 : Rat)) / ((2011 : Rat) / (450 : Rat))))) .eq,
  -- H5.M: 2417/525 = (25/24)/(5*(21/10)/12) + (1+(81/200)/(5*(21/10)/12))*(7/3)
  Comparison.ofRats (((2417 : Rat) / (525 : Rat))) (((((25 : Rat) / (24 : Rat)) / (((5 : Rat) * ((21 : Rat) / (10 : Rat))) / (12 : Rat))) + (((1 : Rat) + (((81 : Rat) / (200 : Rat)) / (((5 : Rat) * ((21 : Rat) / (10 : Rat))) / (12 : Rat)))) * ((7 : Rat) / (3 : Rat))))) .eq,
  -- H5.R: 8509/4834 = 1 + (1+(1/2))*(7/3)/(2417/525)
  Comparison.ofRats (((8509 : Rat) / (4834 : Rat))) (((1 : Rat) + ((((1 : Rat) + ((1 : Rat) / (2 : Rat))) * ((7 : Rat) / (3 : Rat))) / ((2417 : Rat) / (525 : Rat))))) .eq,
  -- K1.H: 7/8 = 1 - (1/3)/(2*(1+(1/3))).
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (((1 : Rat) - (((1 : Rat) / (3 : Rat)) / ((2 : Rat) * ((1 : Rat) + ((1 : Rat) / (3 : Rat))))))) .eq,
  -- K1.K: 4097/1500 = (25/24+(81/200)*(4/5))/(5*(6/5)/12).
  Comparison.ofRats (((4097 : Rat) / (1500 : Rat))) (((((25 : Rat) / (24 : Rat)) + (((81 : Rat) / (200 : Rat)) * ((4 : Rat) / (5 : Rat)))) / (((5 : Rat) * ((6 : Rat) / (5 : Rat))) / (12 : Rat)))) .eq,
  -- K2.H: 7/9 = 1 - (4/5)/(2*(1+(4/5))).
  Comparison.ofRats (((7 : Rat) / (9 : Rat))) (((1 : Rat) - (((4 : Rat) / (5 : Rat)) / ((2 : Rat) * ((1 : Rat) + ((4 : Rat) / (5 : Rat))))))) .eq,
  -- K2.K: 188909/60000 = (25/24+(81/200)*(263/200))/(5*(6/5)/12).
  Comparison.ofRats (((188909 : Rat) / (60000 : Rat))) (((((25 : Rat) / (24 : Rat)) + (((81 : Rat) / (200 : Rat)) * ((263 : Rat) / (200 : Rat)))) / (((5 : Rat) * ((6 : Rat) / (5 : Rat))) / (12 : Rat)))) .eq,
  -- K3.H: 663/926 = 1 - (263/200)/(2*(1+(263/200))).
  Comparison.ofRats (((663 : Rat) / (926 : Rat))) (((1 : Rat) - (((263 : Rat) / (200 : Rat)) / ((2 : Rat) * ((1 : Rat) + ((263 : Rat) / (200 : Rat))))))) .eq,
  -- K3.K: 1979/700 = (25/24+(81/200)*(3/2))/(5*(7/5)/12).
  Comparison.ofRats (((1979 : Rat) / (700 : Rat))) (((((25 : Rat) / (24 : Rat)) + (((81 : Rat) / (200 : Rat)) * ((3 : Rat) / (2 : Rat)))) / (((5 : Rat) * ((7 : Rat) / (5 : Rat))) / (12 : Rat)))) .eq,
  -- K4.H: 7/10 = 1 - (3/2)/(2*(1+(3/2))).
  Comparison.ofRats (((7 : Rat) / (10 : Rat))) (((1 : Rat) - (((3 : Rat) / (2 : Rat)) / ((2 : Rat) * ((1 : Rat) + ((3 : Rat) / (2 : Rat))))))) .eq,
  -- K4.K: 4201/1600 = (25/24+(81/200)*(7/4))/(5*(8/5)/12).
  Comparison.ofRats (((4201 : Rat) / (1600 : Rat))) (((((25 : Rat) / (24 : Rat)) + (((81 : Rat) / (200 : Rat)) * ((7 : Rat) / (4 : Rat)))) / (((5 : Rat) * ((8 : Rat) / (5 : Rat))) / (12 : Rat)))) .eq,
  -- K5.H: 15/22 = 1 - (7/4)/(2*(1+(7/4))).
  Comparison.ofRats (((15 : Rat) / (22 : Rat))) (((1 : Rat) - (((7 : Rat) / (4 : Rat)) / ((2 : Rat) * ((1 : Rat) + ((7 : Rat) / (4 : Rat))))))) .eq,
  -- K5.K: 1111/450 = (25/24+(81/200)*(2))/(5*(9/5)/12).
  Comparison.ofRats (((1111 : Rat) / (450 : Rat))) (((((25 : Rat) / (24 : Rat)) + (((81 : Rat) / (200 : Rat)) * (2 : Rat))) / (((5 : Rat) * ((9 : Rat) / (5 : Rat))) / (12 : Rat)))) .eq,
  -- K6.H: 2/3 = 1 - (2)/(2*(1+(2))).
  Comparison.ofRats (((2 : Rat) / (3 : Rat))) (((1 : Rat) - ((2 : Rat) / ((2 : Rat) * ((1 : Rat) + (2 : Rat)))))) .eq,
  -- K6.K: 1192/525 = (25/24+(81/200)*(7/3))/(5*(21/10)/12).
  Comparison.ofRats (((1192 : Rat) / (525 : Rat))) (((((25 : Rat) / (24 : Rat)) + (((81 : Rat) / (200 : Rat)) * ((7 : Rat) / (3 : Rat)))) / (((5 : Rat) * ((21 : Rat) / (10 : Rat))) / (12 : Rat)))) .eq,
  -- Q1: 263/463 = (263/200)/(1+(263/200)).
  Comparison.ofRats (((263 : Rat) / (463 : Rat))) ((((263 : Rat) / (200 : Rat)) / ((1 : Rat) + ((263 : Rat) / (200 : Rat))))) .eq,
  -- Q2: 3/5 = (3/2)/(1+(3/2)).
  Comparison.ofRats (((3 : Rat) / (5 : Rat))) ((((3 : Rat) / (2 : Rat)) / ((1 : Rat) + ((3 : Rat) / (2 : Rat))))) .eq,
  -- Q3: 7/11 = (7/4)/(1+(7/4)).
  Comparison.ofRats (((7 : Rat) / (11 : Rat))) ((((7 : Rat) / (4 : Rat)) / ((1 : Rat) + ((7 : Rat) / (4 : Rat))))) .eq,
  -- Q4: 2/3 = (2)/(1+(2)).
  Comparison.ofRats (((2 : Rat) / (3 : Rat))) (((2 : Rat) / ((1 : Rat) + (2 : Rat)))) .eq,
  -- Q5: 7/10 = (7/3)/(1+(7/3)).
  Comparison.ofRats (((7 : Rat) / (10 : Rat))) ((((7 : Rat) / (3 : Rat)) / ((1 : Rat) + ((7 : Rat) / (3 : Rat))))) .eq
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 27 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.ParameterEquality001
