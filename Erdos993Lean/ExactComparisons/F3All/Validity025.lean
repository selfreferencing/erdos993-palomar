module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Validity025

def records : List Bool := [
  -- exp.domain0142
  expUseOK (((27 : Rat) / (32 : Rat))),
  -- exp.domain0144
  expUseOK (((1089 : Rat) / (1280 : Rat))),
  -- exp.domain0146
  expUseOK (((219 : Rat) / (256 : Rat))),
  -- exp.domain0148
  expUseOK (((55 : Rat) / (64 : Rat))),
  -- exp.domain0150
  expUseOK (((11011 : Rat) / (12800 : Rat))),
  -- exp.domain0152
  expUseOK (((111 : Rat) / (128 : Rat))),
  -- exp.domain0154
  expUseOK (((2783 : Rat) / (3200 : Rat))),
  -- exp.domain0156
  expUseOK (((225 : Rat) / (256 : Rat))),
  -- exp.domain0158
  expUseOK (((11253 : Rat) / (12800 : Rat))),
  -- exp.domain0160
  expUseOK (((5687 : Rat) / (6400 : Rat))),
  -- exp.domain0162
  expUseOK (((57 : Rat) / (64 : Rat))),
  -- exp.domain0164
  expUseOK (((357 : Rat) / (400 : Rat))),
  -- exp.domain0166
  expUseOK (((143 : Rat) / (160 : Rat))),
  -- exp.domain0168
  expUseOK (((363 : Rat) / (400 : Rat))),
  -- exp.domain0170
  expUseOK (((117 : Rat) / (128 : Rat))),
  -- exp.domain0172
  expUseOK (((23 : Rat) / (25 : Rat))),
  -- exp.domain0174
  expUseOK (((5929 : Rat) / (6400 : Rat))),
  -- exp.domain0176
  expUseOK (((15 : Rat) / (16 : Rat))),
  -- exp.domain0178
  expUseOK (((121 : Rat) / (128 : Rat))),
  -- exp.domain0180
  expUseOK (((123 : Rat) / (128 : Rat))),
  -- exp.domain0182
  expUseOK (((77 : Rat) / (80 : Rat))),
  -- exp.domain0184
  expUseOK (((1573 : Rat) / (1600 : Rat))),
  -- exp.domain0186
  expUseOK (((63 : Rat) / (64 : Rat))),
  -- exp.domain0188
  expUseOK (((129 : Rat) / (128 : Rat))),
  -- exp.domain0190
  expUseOK (((51 : Rat) / (50 : Rat))),
  -- exp.domain0192
  expUseOK (((3267 : Rat) / (3200 : Rat))),
  -- exp.domain0194
  expUseOK (((33 : Rat) / (32 : Rat))),
  -- exp.domain0196
  expUseOK (((135 : Rat) / (128 : Rat))),
  -- exp.domain0198
  expUseOK (((847 : Rat) / (800 : Rat))),
  -- exp.domain0200
  expUseOK (((69 : Rat) / (64 : Rat))),
  -- exp.domain0202
  expUseOK (((11 : Rat) / (10 : Rat))),
  -- exp.domain0204
  expUseOK (((141 : Rat) / (128 : Rat))),
  -- exp.domain0206
  expUseOK (((9 : Rat) / (8 : Rat))),
  -- exp.domain0208
  expUseOK (((147 : Rat) / (128 : Rat))),
  -- exp.domain0210
  expUseOK (((75 : Rat) / (64 : Rat))),
  -- exp.domain0212
  expUseOK (((153 : Rat) / (128 : Rat))),
  -- exp.domain0214
  expUseOK (((121 : Rat) / (100 : Rat))),
  -- exp.domain0216
  expUseOK (((39 : Rat) / (32 : Rat))),
  -- exp.domain0218
  expUseOK (((159 : Rat) / (128 : Rat))),
  -- exp.domain0220
  expUseOK (((81 : Rat) / (64 : Rat))),
  -- exp.domain0222
  expUseOK (((165 : Rat) / (128 : Rat))),
  -- exp.domain0224
  expUseOK (((21 : Rat) / (16 : Rat))),
  -- exp.domain0226
  expUseOK (((171 : Rat) / (128 : Rat))),
  -- exp.domain0228
  expUseOK (((87 : Rat) / (64 : Rat))),
  -- exp.domain0230
  expUseOK (((177 : Rat) / (128 : Rat))),
  -- exp.domain0232
  expUseOK (((45 : Rat) / (32 : Rat))),
  -- exp.domain0234
  expUseOK (((183 : Rat) / (128 : Rat))),
  -- exp.domain0236
  expUseOK (((93 : Rat) / (64 : Rat))),
  -- exp.domain0238
  expUseOK (((189 : Rat) / (128 : Rat))),
  -- exp.domain0240
  expUseOK (((3 : Rat) / (2 : Rat))),
  -- exp.domain0242
  expUseOK (((195 : Rat) / (128 : Rat))),
  -- exp.domain0244
  expUseOK (((99 : Rat) / (64 : Rat))),
  -- exp.domain0246
  expUseOK (((201 : Rat) / (128 : Rat))),
  -- exp.domain0248
  expUseOK (((51 : Rat) / (32 : Rat))),
  -- exp.domain0250
  expUseOK (((105 : Rat) / (64 : Rat))),
  -- exp.domain0252
  expUseOK (((27 : Rat) / (16 : Rat))),
  -- exp.domain0254
  expUseOK (((111 : Rat) / (64 : Rat))),
  -- exp.domain0256
  expUseOK (((57 : Rat) / (32 : Rat))),
  -- exp.domain0258
  expUseOK (((117 : Rat) / (64 : Rat))),
  -- exp.domain0260
  expUseOK (((15 : Rat) / (8 : Rat))),
  -- exp.domain0262
  expUseOK (((123 : Rat) / (64 : Rat))),
  -- exp.domain0264
  expUseOK (((63 : Rat) / (32 : Rat))),
  -- exp.domain0266
  expUseOK (((129 : Rat) / (64 : Rat))),
  -- exp.domain0268
  expUseOK (((33 : Rat) / (16 : Rat)))
]
theorem checked : records.all id = true := by decide +kernel
theorem record_count : records.length = 64 := by decide +kernel
end Erdos993Lean.ExactComparisons.F3All.Validity025
