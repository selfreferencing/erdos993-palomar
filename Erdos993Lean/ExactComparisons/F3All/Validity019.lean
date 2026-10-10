module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Validity019

def records : List Bool := [
  -- log.domain0211
  logUseOK (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((18577253 : Rat) / (5000000 : Rat))))),
  -- log.domain0212
  logUseOK (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((4867199 : Rat) / (1250000 : Rat))))),
  -- log.domain0213
  logUseOK (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((9734397 : Rat) / (2500000 : Rat))))),
  -- log.domain0214
  logUseOK (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((20403123 : Rat) / (5000000 : Rat))))),
  -- log.domain0215
  logUseOK (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((20403121 : Rat) / (5000000 : Rat))))),
  -- log.domain0216
  logUseOK (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((42764579 : Rat) / (10000000 : Rat))))),
  -- log.domain0217
  logUseOK (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((21382287 : Rat) / (5000000 : Rat))))),
  -- log.domain0218
  logUseOK (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((22408447 : Rat) / (5000000 : Rat))))),
  -- log.domain0219
  logUseOK (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((44816889 : Rat) / (10000000 : Rat))))),
  -- log.domain0220
  logUseOK (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((23483851 : Rat) / (5000000 : Rat))))),
  -- log.domain0221
  logUseOK (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((46967697 : Rat) / (10000000 : Rat))))),
  -- log.domain0222
  logUseOK (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((4922173 : Rat) / (1000000 : Rat))))),
  -- log.domain0223
  logUseOK (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((12305431 : Rat) / (2500000 : Rat))))),
  -- log.domain0224
  logUseOK (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((6757437 : Rat) / (1250000 : Rat))))),
  -- log.domain0225
  logUseOK (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((1689359 : Rat) / (312500 : Rat))))),
  -- log.domain0226
  logUseOK (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((59372743 : Rat) / (10000000 : Rat))))),
  -- log.domain0227
  logUseOK (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((14843183 : Rat) / (2500000 : Rat))))),
  -- log.domain0228
  logUseOK (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((32604103 : Rat) / (5000000 : Rat))))),
  -- log.domain0229
  logUseOK (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((6520819 : Rat) / (1000000 : Rat))))),
  -- log.domain0230
  logUseOK (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((71617209 : Rat) / (10000000 : Rat))))),
  -- log.domain0231
  logUseOK (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((35808593 : Rat) / (5000000 : Rat))))),
  -- log.domain0232
  logUseOK (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((629249 : Rat) / (80000 : Rat))))),
  -- log.domain0233
  logUseOK (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((78656091 : Rat) / (10000000 : Rat))))),
  -- log.domain0234
  logUseOK (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((23719357 : Rat) / (2500000 : Rat))))),
  -- log.domain0235
  logUseOK (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((94877357 : Rat) / (10000000 : Rat))))),
  -- log.domain0236
  logUseOK (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((27609207 : Rat) / (2000000 : Rat))))),
  -- log.domain0237
  logUseOK (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((6902287 : Rat) / (500000 : Rat))))),
  -- log.domain0238
  logUseOK (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((100428229 : Rat) / (5000000 : Rat))))),
  -- log.domain0239
  logUseOK (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((40171073 : Rat) / (2000000 : Rat))))),
  -- log.domain0240
  logUseOK (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((3637479 : Rat) / (2500000 : Rat))))),
  -- log.domain0241
  logUseOK (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((14549913 : Rat) / (10000000 : Rat))))),
  -- log.domain0242
  logUseOK (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((15219617 : Rat) / (10000000 : Rat))))),
  -- log.domain0243
  logUseOK (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((7609807 : Rat) / (5000000 : Rat))))),
  -- log.domain0244
  logUseOK (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((15248181 : Rat) / (10000000 : Rat))))),
  -- log.domain0245
  logUseOK (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((7624089 : Rat) / (5000000 : Rat))))),
  -- log.domain0246
  logUseOK (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((3994989 : Rat) / (2500000 : Rat))))),
  -- log.domain0247
  logUseOK (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((15979953 : Rat) / (10000000 : Rat))))),
  -- log.domain0248
  logUseOK (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((1635891 : Rat) / (1000000 : Rat))))),
  -- log.domain0249
  logUseOK (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((16358907 : Rat) / (10000000 : Rat))))),
  -- log.domain0250
  logUseOK (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((334937 : Rat) / (200000 : Rat))))),
  -- log.domain0251
  logUseOK (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((16746847 : Rat) / (10000000 : Rat))))),
  -- log.domain0252
  logUseOK (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((1714399 : Rat) / (1000000 : Rat))))),
  -- log.domain0253
  logUseOK (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((17143987 : Rat) / (10000000 : Rat))))),
  -- log.domain0254
  logUseOK (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((4387637 : Rat) / (2500000 : Rat))))),
  -- log.domain0255
  logUseOK (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((3510109 : Rat) / (2000000 : Rat))))),
  -- log.domain0256
  logUseOK (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((17966747 : Rat) / (10000000 : Rat))))),
  -- log.domain0257
  logUseOK (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((2245843 : Rat) / (1250000 : Rat))))),
  -- log.domain0258
  logUseOK (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((1149551 : Rat) / (625000 : Rat))))),
  -- log.domain0259
  logUseOK (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((18392813 : Rat) / (10000000 : Rat))))),
  -- log.domain0260
  logUseOK (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((18776107 : Rat) / (10000000 : Rat))))),
  -- log.domain0261
  logUseOK (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((2347013 : Rat) / (1250000 : Rat))))),
  -- log.domain0262
  logUseOK (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((18828989 : Rat) / (10000000 : Rat))))),
  -- log.domain0263
  logUseOK (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((9414493 : Rat) / (5000000 : Rat))))),
  -- log.domain0264
  logUseOK (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((9637753 : Rat) / (5000000 : Rat))))),
  -- log.domain0265
  logUseOK (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((19275503 : Rat) / (10000000 : Rat))))),
  -- log.domain0266
  logUseOK (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((19732611 : Rat) / (10000000 : Rat))))),
  -- log.domain0267
  logUseOK (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((154161 : Rat) / (78125 : Rat))))),
  -- log.domain0268
  logUseOK (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((4947047 : Rat) / (2500000 : Rat))))),
  -- log.domain0269
  logUseOK (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((3957637 : Rat) / (2000000 : Rat))))),
  -- log.domain0270
  logUseOK (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((20200557 : Rat) / (10000000 : Rat))))),
  -- log.domain0271
  logUseOK (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((10100277 : Rat) / (5000000 : Rat))))),
  -- log.domain0272
  logUseOK (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((20679599 : Rat) / (10000000 : Rat))))),
  -- log.domain0273
  logUseOK (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((5169899 : Rat) / (2500000 : Rat))))),
  -- log.domain0274
  logUseOK (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((20854821 : Rat) / (10000000 : Rat)))))
]
theorem checked : records.all id = true := by decide +kernel
theorem record_count : records.length = 64 := by decide +kernel
end Erdos993Lean.ExactComparisons.F3All.Validity019
