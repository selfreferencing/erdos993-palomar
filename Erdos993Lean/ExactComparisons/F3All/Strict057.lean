module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict057

def records : List Comparison := [
  -- C017.den; C017: D=8/5, v=7/4, y in [357/400,51/50], type C: d0 > 920782/1000000 > 0; C_balance > 7825/1000000 > 0.
  Comparison.ofRats ((920782 : Rat)/1000000) ((faceDen c017)) .lt,
  -- C017.balance; C017: D=8/5, v=7/4, y in [357/400,51/50], type C: d0 > 920782/1000000 > 0; C_balance > 7825/1000000 > 0.
  Comparison.ofRats ((7825 : Rat)/1000000) ((faceBalance c017)) .lt,
  -- C018.ell; C018: D=9/5, v=2, y in [0,11/20], type L: ell_star > 2534/1000000 > 0.
  Comparison.ofRats ((2534 : Rat)/1000000) ((faceEll c018)) .lt,
  -- C019.ell; C019: D=9/5, v=2, y in [11/20,11/16], type L: ell_star > 72401/1000000 > 0.
  Comparison.ofRats ((72401 : Rat)/1000000) ((faceEll c019)) .lt,
  -- C020.ell; C020: D=9/5, v=2, y in [11/16,121/160], type L: ell_star > 35988/1000000 > 0.
  Comparison.ofRats ((35988 : Rat)/1000000) ((faceEll c020)) .lt,
  -- C021.den; C021: D=9/5, v=2, y in [121/160,33/40], type C: d0 > 996211/1000000 > 0; C_balance > 1403/1000000 > 0.
  Comparison.ofRats ((996211 : Rat)/1000000) ((faceDen c021)) .lt,
  -- C021.balance; C021: D=9/5, v=2, y in [121/160,33/40], type C: d0 > 996211/1000000 > 0; C_balance > 1403/1000000 > 0.
  Comparison.ofRats ((1403 : Rat)/1000000) ((faceBalance c021)) .lt,
  -- C022.den; C022: D=9/5, v=2, y in [33/40,55/64], type C: d0 > 986547/1000000 > 0; C_balance > 7930/1000000 > 0.
  Comparison.ofRats ((986547 : Rat)/1000000) ((faceDen c022)) .lt,
  -- C022.balance; C022: D=9/5, v=2, y in [33/40,55/64], type C: d0 > 986547/1000000 > 0; C_balance > 7930/1000000 > 0.
  Comparison.ofRats ((7930 : Rat)/1000000) ((faceBalance c022)) .lt,
  -- C023.den; C023: D=9/5, v=2, y in [55/64,143/160], type C: d0 > 976078/1000000 > 0; C_balance > 10225/1000000 > 0.
  Comparison.ofRats ((976078 : Rat)/1000000) ((faceDen c023)) .lt,
  -- C023.balance; C023: D=9/5, v=2, y in [55/64,143/160], type C: d0 > 976078/1000000 > 0; C_balance > 10225/1000000 > 0.
  Comparison.ofRats ((10225 : Rat)/1000000) ((faceBalance c023)) .lt,
  -- C024.den; C024: D=9/5, v=2, y in [143/160,77/80], type C: d0 > 954849/1000000 > 0; C_balance > 6286/1000000 > 0.
  Comparison.ofRats ((954849 : Rat)/1000000) ((faceDen c024)) .lt,
  -- C024.balance; C024: D=9/5, v=2, y in [143/160,77/80], type C: d0 > 954849/1000000 > 0; C_balance > 6286/1000000 > 0.
  Comparison.ofRats ((6286 : Rat)/1000000) ((faceBalance c024)) .lt,
  -- C025.den; C025: D=9/5, v=2, y in [77/80,11/10], type C: d0 > 914201/1000000 > 0; C_balance > 4657/1000000 > 0.
  Comparison.ofRats ((914201 : Rat)/1000000) ((faceDen c025)) .lt,
  -- C025.balance; C025: D=9/5, v=2, y in [77/80,11/10], type C: d0 > 914201/1000000 > 0; C_balance > 4657/1000000 > 0.
  Comparison.ofRats ((4657 : Rat)/1000000) ((faceBalance c025)) .lt,
  -- C026.ell; C026: D=21/10, v=7/3, y in [0,121/400], type L: ell_star > 232032/1000000 > 0.
  Comparison.ofRats ((232032 : Rat)/1000000) ((faceEll c026)) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict057
