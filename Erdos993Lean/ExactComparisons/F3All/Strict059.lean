module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict059

def records : List Comparison := [
  -- C037.den; C037: D=21/10, v=7/3, y in [5687/6400,363/400], type C: d0 > 977428/1000000 > 0; C_balance > 186/1000000 > 0.
  Comparison.ofRats ((977428 : Rat)/1000000) ((faceDen c037)) .lt,
  -- C037.balance; C037: D=21/10, v=7/3, y in [5687/6400,363/400], type C: d0 > 977428/1000000 > 0; C_balance > 186/1000000 > 0.
  Comparison.ofRats ((186 : Rat)/1000000) ((faceBalance c037)) .lt,
  -- C038.den; C038: D=21/10, v=7/3, y in [363/400,5929/6400], type C: d0 > 972577/1000000 > 0; C_balance > 1351/1000000 > 0.
  Comparison.ofRats ((972577 : Rat)/1000000) ((faceDen c038)) .lt,
  -- C038.balance; C038: D=21/10, v=7/3, y in [363/400,5929/6400], type C: d0 > 972577/1000000 > 0; C_balance > 1351/1000000 > 0.
  Comparison.ofRats ((1351 : Rat)/1000000) ((faceBalance c038)) .lt,
  -- C039.den; C039: D=21/10, v=7/3, y in [5929/6400,121/128], type C: d0 > 967787/1000000 > 0; C_balance > 3155/1000000 > 0.
  Comparison.ofRats ((967787 : Rat)/1000000) ((faceDen c039)) .lt,
  -- C039.balance; C039: D=21/10, v=7/3, y in [5929/6400,121/128], type C: d0 > 967787/1000000 > 0; C_balance > 3155/1000000 > 0.
  Comparison.ofRats ((3155 : Rat)/1000000) ((faceBalance c039)) .lt,
  -- C040.den; C040: D=21/10, v=7/3, y in [121/128,1573/1600], type C: d0 > 958102/1000000 > 0; C_balance > 1185/1000000 > 0.
  Comparison.ofRats ((958102 : Rat)/1000000) ((faceDen c040)) .lt,
  -- C040.balance; C040: D=21/10, v=7/3, y in [121/128,1573/1600], type C: d0 > 958102/1000000 > 0; C_balance > 1185/1000000 > 0.
  Comparison.ofRats ((1185 : Rat)/1000000) ((faceBalance c040)) .lt,
  -- C041.den; C041: D=21/10, v=7/3, y in [1573/1600,3267/3200], type C: d0 > 949016/1000000 > 0; C_balance > 7981/1000000 > 0.
  Comparison.ofRats ((949016 : Rat)/1000000) ((faceDen c041)) .lt,
  -- C041.balance; C041: D=21/10, v=7/3, y in [1573/1600,3267/3200], type C: d0 > 949016/1000000 > 0; C_balance > 7981/1000000 > 0.
  Comparison.ofRats ((7981 : Rat)/1000000) ((faceBalance c041)) .lt,
  -- C042.den; C042: D=21/10, v=7/3, y in [3267/3200,847/800], type C: d0 > 940268/1000000 > 0; C_balance > 17109/1000000 > 0.
  Comparison.ofRats ((940268 : Rat)/1000000) ((faceDen c042)) .lt,
  -- C042.balance; C042: D=21/10, v=7/3, y in [3267/3200,847/800], type C: d0 > 940268/1000000 > 0; C_balance > 17109/1000000 > 0.
  Comparison.ofRats ((17109 : Rat)/1000000) ((faceBalance c042)) .lt,
  -- C043.den; C043: D=21/10, v=7/3, y in [847/800,121/100], type C: d0 > 903496/1000000 > 0; C_balance > 2508/1000000 > 0.
  Comparison.ofRats ((903496 : Rat)/1000000) ((faceDen c043)) .lt,
  -- C043.balance; C043: D=21/10, v=7/3, y in [847/800,121/100], type C: d0 > 903496/1000000 > 0; C_balance > 2508/1000000 > 0.
  Comparison.ofRats ((2508 : Rat)/1000000) ((faceBalance c043)) .lt,
  -- A001.den; A001: D=6/5, lambda in [1/3,3/5], y in [0,3/32], m=0: delta > 1074344/1000000 > 0; B_balance > 197190/1000000 > 0.
  Comparison.ofRats ((1074344 : Rat)/1000000) ((cellDelta a001)) .lt,
  -- A001.balance; A001: D=6/5, lambda in [1/3,3/5], y in [0,3/32], m=0: delta > 1074344/1000000 > 0; B_balance > 197190/1000000 > 0.
  Comparison.ofRats ((197190 : Rat)/1000000) ((cellBalance a001)) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict059
