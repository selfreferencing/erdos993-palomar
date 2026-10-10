module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Validity024

def records : List Bool := [
  -- exp.domain0014
  expUseOK (((33 : Rat) / (128 : Rat))),
  -- exp.domain0016
  expUseOK (((9 : Rat) / (32 : Rat))),
  -- exp.domain0018
  expUseOK (((121 : Rat) / (400 : Rat))),
  -- exp.domain0020
  expUseOK (((39 : Rat) / (128 : Rat))),
  -- exp.domain0022
  expUseOK (((21 : Rat) / (64 : Rat))),
  -- exp.domain0024
  expUseOK (((45 : Rat) / (128 : Rat))),
  -- exp.domain0026
  expUseOK (((3 : Rat) / (8 : Rat))),
  -- exp.domain0028
  expUseOK (((51 : Rat) / (128 : Rat))),
  -- exp.domain0030
  expUseOK (((21 : Rat) / (50 : Rat))),
  -- exp.domain0032
  expUseOK (((27 : Rat) / (64 : Rat))),
  -- exp.domain0034
  expUseOK (((57 : Rat) / (128 : Rat))),
  -- exp.domain0036
  expUseOK (((23 : Rat) / (50 : Rat))),
  -- exp.domain0038
  expUseOK (((15 : Rat) / (32 : Rat))),
  -- exp.domain0040
  expUseOK (((123 : Rat) / (256 : Rat))),
  -- exp.domain0042
  expUseOK (((63 : Rat) / (128 : Rat))),
  -- exp.domain0044
  expUseOK (((129 : Rat) / (256 : Rat))),
  -- exp.domain0046
  expUseOK (((51 : Rat) / (100 : Rat))),
  -- exp.domain0048
  expUseOK (((33 : Rat) / (64 : Rat))),
  -- exp.domain0050
  expUseOK (((135 : Rat) / (256 : Rat))),
  -- exp.domain0052
  expUseOK (((69 : Rat) / (128 : Rat))),
  -- exp.domain0054
  expUseOK (((11 : Rat) / (20 : Rat))),
  -- exp.domain0056
  expUseOK (((141 : Rat) / (256 : Rat))),
  -- exp.domain0058
  expUseOK (((9 : Rat) / (16 : Rat))),
  -- exp.domain0060
  expUseOK (((147 : Rat) / (256 : Rat))),
  -- exp.domain0062
  expUseOK (((75 : Rat) / (128 : Rat))),
  -- exp.domain0064
  expUseOK (((153 : Rat) / (256 : Rat))),
  -- exp.domain0066
  expUseOK (((121 : Rat) / (200 : Rat))),
  -- exp.domain0068
  expUseOK (((39 : Rat) / (64 : Rat))),
  -- exp.domain0070
  expUseOK (((159 : Rat) / (256 : Rat))),
  -- exp.domain0072
  expUseOK (((63 : Rat) / (100 : Rat))),
  -- exp.domain0074
  expUseOK (((81 : Rat) / (128 : Rat))),
  -- exp.domain0076
  expUseOK (((51 : Rat) / (80 : Rat))),
  -- exp.domain0078
  expUseOK (((165 : Rat) / (256 : Rat))),
  -- exp.domain0080
  expUseOK (((21 : Rat) / (32 : Rat))),
  -- exp.domain0082
  expUseOK (((171 : Rat) / (256 : Rat))),
  -- exp.domain0084
  expUseOK (((87 : Rat) / (128 : Rat))),
  -- exp.domain0086
  expUseOK (((273 : Rat) / (400 : Rat))),
  -- exp.domain0088
  expUseOK (((11 : Rat) / (16 : Rat))),
  -- exp.domain0090
  expUseOK (((69 : Rat) / (100 : Rat))),
  -- exp.domain0092
  expUseOK (((177 : Rat) / (256 : Rat))),
  -- exp.domain0094
  expUseOK (((45 : Rat) / (64 : Rat))),
  -- exp.domain0096
  expUseOK (((183 : Rat) / (256 : Rat))),
  -- exp.domain0098
  expUseOK (((93 : Rat) / (128 : Rat))),
  -- exp.domain0100
  expUseOK (((147 : Rat) / (200 : Rat))),
  -- exp.domain0102
  expUseOK (((189 : Rat) / (256 : Rat))),
  -- exp.domain0104
  expUseOK (((299 : Rat) / (400 : Rat))),
  -- exp.domain0106
  expUseOK (((3 : Rat) / (4 : Rat))),
  -- exp.domain0108
  expUseOK (((121 : Rat) / (160 : Rat))),
  -- exp.domain0110
  expUseOK (((195 : Rat) / (256 : Rat))),
  -- exp.domain0112
  expUseOK (((153 : Rat) / (200 : Rat))),
  -- exp.domain0114
  expUseOK (((99 : Rat) / (128 : Rat))),
  -- exp.domain0116
  expUseOK (((201 : Rat) / (256 : Rat))),
  -- exp.domain0118
  expUseOK (((63 : Rat) / (80 : Rat))),
  -- exp.domain0120
  expUseOK (((2541 : Rat) / (3200 : Rat))),
  -- exp.domain0122
  expUseOK (((51 : Rat) / (64 : Rat))),
  -- exp.domain0124
  expUseOK (((161 : Rat) / (200 : Rat))),
  -- exp.domain0126
  expUseOK (((207 : Rat) / (256 : Rat))),
  -- exp.domain0128
  expUseOK (((5203 : Rat) / (6400 : Rat))),
  -- exp.domain0130
  expUseOK (((105 : Rat) / (128 : Rat))),
  -- exp.domain0132
  expUseOK (((33 : Rat) / (40 : Rat))),
  -- exp.domain0134
  expUseOK (((663 : Rat) / (800 : Rat))),
  -- exp.domain0136
  expUseOK (((1331 : Rat) / (1600 : Rat))),
  -- exp.domain0138
  expUseOK (((213 : Rat) / (256 : Rat))),
  -- exp.domain0140
  expUseOK (((21 : Rat) / (25 : Rat)))
]
theorem checked : records.all id = true := by decide +kernel
theorem record_count : records.length = 64 := by decide +kernel
end Erdos993Lean.ExactComparisons.F3All.Validity024
