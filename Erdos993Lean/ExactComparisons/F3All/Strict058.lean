module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict058

def records : List Comparison := [
  -- C027.ell; C027: D=21/10, v=7/3, y in [121/400,121/200], type L: ell_star > 68249/1000000 > 0.
  Comparison.ofRats ((68249 : Rat)/1000000) ((faceEll c027)) .lt,
  -- C028.ell; C028: D=21/10, v=7/3, y in [121/200,121/160], type L: ell_star > 23056/1000000 > 0.
  Comparison.ofRats ((23056 : Rat)/1000000) ((faceEll c028)) .lt,
  -- C029.ell; C029: D=21/10, v=7/3, y in [121/160,2541/3200], type L: ell_star > 14480/1000000 > 0.
  Comparison.ofRats ((14480 : Rat)/1000000) ((faceEll c029)) .lt,
  -- C030.ell; C030: D=21/10, v=7/3, y in [2541/3200,5203/6400], type L: ell_star > 4850/1000000 > 0.
  Comparison.ofRats ((4850 : Rat)/1000000) ((faceEll c030)) .lt,
  -- C031.den; C031: D=21/10, v=7/3, y in [5203/6400,1331/1600], type C: d0 > 997337/1000000 > 0; C_balance > 2248/1000000 > 0.
  Comparison.ofRats ((997337 : Rat)/1000000) ((faceDen c031)) .lt,
  -- C031.balance; C031: D=21/10, v=7/3, y in [5203/6400,1331/1600], type C: d0 > 997337/1000000 > 0; C_balance > 2248/1000000 > 0.
  Comparison.ofRats ((2248 : Rat)/1000000) ((faceBalance c031)) .lt,
  -- C032.den; C032: D=21/10, v=7/3, y in [1331/1600,1089/1280], type C: d0 > 992292/1000000 > 0; C_balance > 688/1000000 > 0.
  Comparison.ofRats ((992292 : Rat)/1000000) ((faceDen c032)) .lt,
  -- C032.balance; C032: D=21/10, v=7/3, y in [1331/1600,1089/1280], type C: d0 > 992292/1000000 > 0; C_balance > 688/1000000 > 0.
  Comparison.ofRats ((688 : Rat)/1000000) ((faceBalance c032)) .lt,
  -- C033.den; C033: D=21/10, v=7/3, y in [1089/1280,11011/12800], type C: d0 > 989861/1000000 > 0; C_balance > 2095/1000000 > 0.
  Comparison.ofRats ((989861 : Rat)/1000000) ((faceDen c033)) .lt,
  -- C033.balance; C033: D=21/10, v=7/3, y in [1089/1280,11011/12800], type C: d0 > 989861/1000000 > 0; C_balance > 2095/1000000 > 0.
  Comparison.ofRats ((2095 : Rat)/1000000) ((faceBalance c033)) .lt,
  -- C034.den; C034: D=21/10, v=7/3, y in [11011/12800,2783/3200], type C: d0 > 987365/1000000 > 0; C_balance > 1920/1000000 > 0.
  Comparison.ofRats ((987365 : Rat)/1000000) ((faceDen c034)) .lt,
  -- C034.balance; C034: D=21/10, v=7/3, y in [11011/12800,2783/3200], type C: d0 > 987365/1000000 > 0; C_balance > 1920/1000000 > 0.
  Comparison.ofRats ((1920 : Rat)/1000000) ((faceBalance c034)) .lt,
  -- C035.den; C035: D=21/10, v=7/3, y in [2783/3200,11253/12800], type C: d0 > 984881/1000000 > 0; C_balance > 1914/1000000 > 0.
  Comparison.ofRats ((984881 : Rat)/1000000) ((faceDen c035)) .lt,
  -- C035.balance; C035: D=21/10, v=7/3, y in [2783/3200,11253/12800], type C: d0 > 984881/1000000 > 0; C_balance > 1914/1000000 > 0.
  Comparison.ofRats ((1914 : Rat)/1000000) ((faceBalance c035)) .lt,
  -- C036.den; C036: D=21/10, v=7/3, y in [11253/12800,5687/6400], type C: d0 > 982409/1000000 > 0; C_balance > 2076/1000000 > 0.
  Comparison.ofRats ((982409 : Rat)/1000000) ((faceDen c036)) .lt,
  -- C036.balance; C036: D=21/10, v=7/3, y in [11253/12800,5687/6400], type C: d0 > 982409/1000000 > 0; C_balance > 2076/1000000 > 0.
  Comparison.ofRats ((2076 : Rat)/1000000) ((faceBalance c036)) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict058
