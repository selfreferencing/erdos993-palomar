module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Validity026

def records : List Bool := [
  -- exp.domain0270
  expUseOK (((69 : Rat) / (32 : Rat))),
  -- exp.domain0272
  expUseOK (((9 : Rat) / (4 : Rat))),
  -- exp.domain0274
  expUseOK (((39 : Rat) / (16 : Rat))),
  -- exp.domain0276
  expUseOK (((21 : Rat) / (8 : Rat))),
  -- exp.domain0278
  expUseOK (((45 : Rat) / (16 : Rat))),
  -- exp.domain0280
  expUseOK ((3 : Rat)),
  -- expression.denominator0001
  decide (((9 : Rat)) ≠ (0 : Rat)),
  -- expression.denominator0002
  decide ((((10 : Rat) ^ 7)) ≠ (0 : Rat)),
  -- expression.denominator0006
  decide (((11 : Rat)) ≠ (0 : Rat)),
  -- expression.denominator0013
  decide (((7 : Rat)) ≠ (0 : Rat)),
  -- expression.denominator0020
  decide ((((2 : Rat) * (((6931467 : Rat) / ((10 : Rat) ^ 7)) ^ 2))) ≠ (0 : Rat)),
  -- expression.denominator0021
  decide (((24 : Rat)) ≠ (0 : Rat)),
  -- expression.denominator0023
  decide ((((6931472 : Rat) / ((10 : Rat) ^ 7))) ≠ (0 : Rat)),
  -- expression.denominator0025
  decide ((((2 : Rat) * (((6931472 : Rat) / ((10 : Rat) ^ 7)) ^ 2))) ≠ (0 : Rat)),
  -- expression.denominator0026
  decide (((200 : Rat)) ≠ (0 : Rat)),
  -- expression.denominator0027
  decide (((3 : Rat)) ≠ (0 : Rat)),
  -- expression.denominator0028
  decide (((6 : Rat)) ≠ (0 : Rat)),
  -- expression.denominator0029
  decide (((80 : Rat)) ≠ (0 : Rat)),
  -- expression.denominator0030
  decide (((100 : Rat)) ≠ (0 : Rat)),
  -- expression.denominator0032
  decide (((5 : Rat)) ≠ (0 : Rat)),
  -- expression.denominator0033
  decide (((4 : Rat)) ≠ (0 : Rat)),
  -- expression.denominator0035
  decide (((10 : Rat)) ≠ (0 : Rat)),
  -- expression.denominator0036
  decide (((267809 : Rat)) ≠ (0 : Rat)),
  -- expression.denominator0037
  decide (((40 : Rat)) ≠ (0 : Rat)),
  -- expression.denominator0038
  decide (((60000 : Rat)) ≠ (0 : Rat)),
  -- expression.denominator0040
  decide ((((181 : Rat) / (40 : Rat))) ≠ (0 : Rat)),
  -- expression.denominator0042
  decide (((8 : Rat)) ≠ (0 : Rat)),
  -- expression.denominator0044
  decide (((6058 : Rat)) ≠ (0 : Rat)),
  -- expression.denominator0046
  decide (((700 : Rat)) ≠ (0 : Rat)),
  -- expression.denominator0048
  decide ((((49 : Rat) / (10 : Rat))) ≠ (0 : Rat)),
  -- expression.denominator0049
  decide (((2 : Rat)) ≠ (0 : Rat)),
  -- expression.denominator0052
  decide (((7001 : Rat)) ≠ (0 : Rat)),
  -- expression.denominator0054
  decide (((1600 : Rat)) ≠ (0 : Rat)),
  -- expression.denominator0060
  decide (((2011 : Rat)) ≠ (0 : Rat)),
  -- expression.denominator0062
  decide (((450 : Rat)) ≠ (0 : Rat)),
  -- expression.denominator0064
  decide ((((21 : Rat) / (4 : Rat))) ≠ (0 : Rat)),
  -- expression.denominator0067
  decide (((4834 : Rat)) ≠ (0 : Rat)),
  -- expression.denominator0069
  decide (((525 : Rat)) ≠ (0 : Rat)),
  -- expression.denominator0071
  decide ((((23 : Rat) / (4 : Rat))) ≠ (0 : Rat)),
  -- expression.denominator0075
  decide (((1500 : Rat)) ≠ (0 : Rat)),
  -- expression.denominator0084
  decide ((((4 : Rat) * (((4097 : Rat) / (1500 : Rat)) + (((4 : Rat) / (5 : Rat)) / (4 : Rat))))) ≠ (0 : Rat)),
  -- expression.denominator0095
  decide ((((4 : Rat) * (((188909 : Rat) / (60000 : Rat)) + (((263 : Rat) / (200 : Rat)) / (4 : Rat))))) ≠ (0 : Rat)),
  -- expression.denominator0098
  decide (((926 : Rat)) ≠ (0 : Rat)),
  -- expression.denominator0106
  decide ((((4 : Rat) * (((1979 : Rat) / (700 : Rat)) + (((3 : Rat) / (2 : Rat)) / (4 : Rat))))) ≠ (0 : Rat)),
  -- expression.denominator0117
  decide ((((4 : Rat) * (((4201 : Rat) / (1600 : Rat)) + (((7 : Rat) / (4 : Rat)) / (4 : Rat))))) ≠ (0 : Rat)),
  -- expression.denominator0120
  decide (((22 : Rat)) ≠ (0 : Rat)),
  -- expression.denominator0126
  decide ((((4 : Rat) * (((1111 : Rat) / (450 : Rat)) + ((2 : Rat) / (4 : Rat))))) ≠ (0 : Rat)),
  -- expression.denominator0137
  decide ((((4 : Rat) * (((1192 : Rat) / (525 : Rat)) + (((7 : Rat) / (3 : Rat)) / (4 : Rat))))) ≠ (0 : Rat)),
  -- expression.denominator0142
  decide (((12 : Rat)) ≠ (0 : Rat)),
  -- expression.denominator0144
  decide (((((5 : Rat) / (12 : Rat)) * ((6 : Rat) / (5 : Rat)))) ≠ (0 : Rat)),
  -- expression.denominator0151
  decide (((((5 : Rat) / (12 : Rat)) * ((7 : Rat) / (5 : Rat)))) ≠ (0 : Rat)),
  -- expression.denominator0158
  decide (((((5 : Rat) / (12 : Rat)) * ((8 : Rat) / (5 : Rat)))) ≠ (0 : Rat)),
  -- expression.denominator0164
  decide (((((5 : Rat) / (12 : Rat)) * ((9 : Rat) / (5 : Rat)))) ≠ (0 : Rat)),
  -- expression.denominator0171
  decide (((((5 : Rat) / (12 : Rat)) * ((21 : Rat) / (10 : Rat)))) ≠ (0 : Rat)),
  -- expression.denominator0173
  decide (((25 : Rat)) ≠ (0 : Rat)),
  -- expression.denominator0175
  decide (((50 : Rat)) ≠ (0 : Rat)),
  -- expression.denominator0178
  decide (((463 : Rat)) ≠ (0 : Rat)),
  -- expression.denominator0198
  decide (((20 : Rat)) ≠ (0 : Rat)),
  -- expression.denominator0200
  decide (((2000 : Rat)) ≠ (0 : Rat)),
  -- expression.denominator0203
  decide (((16000 : Rat)) ≠ (0 : Rat)),
  -- expression.denominator0204
  decide (((1420 : Rat)) ≠ (0 : Rat)),
  -- expression.denominator0208
  decide (((1775 : Rat)) ≠ (0 : Rat)),
  -- expression.denominator0213
  decide (((16 : Rat)) ≠ (0 : Rat)),
  -- expression.denominator0217
  decide (((125 : Rat)) ≠ (0 : Rat))
]
theorem checked : records.all id = true := by decide +kernel
theorem record_count : records.length = 64 := by decide +kernel
end Erdos993Lean.ExactComparisons.F3All.Validity026
