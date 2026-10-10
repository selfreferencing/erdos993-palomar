module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict056

def records : List Comparison := [
  -- C006.den; C006: D=6/5, v=263/200, y in [63/80,21/25], type C: d0 > 935570/1000000 > 0; C_balance > 11894/1000000 > 0.
  Comparison.ofRats ((935570 : Rat)/1000000) ((faceDen c006)) .lt,
  -- C006.balance; C006: D=6/5, v=263/200, y in [63/80,21/25], type C: d0 > 935570/1000000 > 0; C_balance > 11894/1000000 > 0.
  Comparison.ofRats ((11894 : Rat)/1000000) ((faceBalance c006)) .lt,
  -- C007.ell; C007: D=7/5, v=3/2, y in [0,23/50], type L: ell_star > 159172/1000000 > 0.
  Comparison.ofRats ((159172 : Rat)/1000000) ((faceEll c007)) .lt,
  -- C008.ell; C008: D=7/5, v=3/2, y in [23/50,69/100], type L: ell_star > 34603/1000000 > 0.
  Comparison.ofRats ((34603 : Rat)/1000000) ((faceEll c008)) .lt,
  -- C009.ell; C009: D=7/5, v=3/2, y in [69/100,299/400], type L: ell_star > 9801/1000000 > 0.
  Comparison.ofRats ((9801 : Rat)/1000000) ((faceEll c009)) .lt,
  -- C010.den; C010: D=7/5, v=3/2, y in [299/400,161/200], type C: d0 > 986024/1000000 > 0; C_balance > 13142/1000000 > 0.
  Comparison.ofRats ((986024 : Rat)/1000000) ((faceDen c010)) .lt,
  -- C010.balance; C010: D=7/5, v=3/2, y in [299/400,161/200], type C: d0 > 986024/1000000 > 0; C_balance > 13142/1000000 > 0.
  Comparison.ofRats ((13142 : Rat)/1000000) ((faceBalance c010)) .lt,
  -- C011.den; C011: D=7/5, v=3/2, y in [161/200,23/25], type C: d0 > 951207/1000000 > 0; C_balance > 5465/1000000 > 0.
  Comparison.ofRats ((951207 : Rat)/1000000) ((faceDen c011)) .lt,
  -- C011.balance; C011: D=7/5, v=3/2, y in [161/200,23/25], type C: d0 > 951207/1000000 > 0; C_balance > 5465/1000000 > 0.
  Comparison.ofRats ((5465 : Rat)/1000000) ((faceBalance c011)) .lt,
  -- C012.ell; C012: D=8/5, v=7/4, y in [0,51/100], type L: ell_star > 72713/1000000 > 0.
  Comparison.ofRats ((72713 : Rat)/1000000) ((faceEll c012)) .lt,
  -- C013.ell; C013: D=8/5, v=7/4, y in [51/100,51/80], type L: ell_star > 113077/1000000 > 0.
  Comparison.ofRats ((113077 : Rat)/1000000) ((faceEll c013)) .lt,
  -- C014.ell; C014: D=8/5, v=7/4, y in [51/80,153/200], type L: ell_star > 17255/1000000 > 0.
  Comparison.ofRats ((17255 : Rat)/1000000) ((faceEll c014)) .lt,
  -- C015.den; C015: D=8/5, v=7/4, y in [153/200,663/800], type C: d0 > 988756/1000000 > 0; C_balance > 7355/1000000 > 0.
  Comparison.ofRats ((988756 : Rat)/1000000) ((faceDen c015)) .lt,
  -- C015.balance; C015: D=8/5, v=7/4, y in [153/200,663/800], type C: d0 > 988756/1000000 > 0; C_balance > 7355/1000000 > 0.
  Comparison.ofRats ((7355 : Rat)/1000000) ((faceBalance c015)) .lt,
  -- C016.den; C016: D=8/5, v=7/4, y in [663/800,357/400], type C: d0 > 966190/1000000 > 0; C_balance > 12043/1000000 > 0.
  Comparison.ofRats ((966190 : Rat)/1000000) ((faceDen c016)) .lt,
  -- C016.balance; C016: D=8/5, v=7/4, y in [663/800,357/400], type C: d0 > 966190/1000000 > 0; C_balance > 12043/1000000 > 0.
  Comparison.ofRats ((12043 : Rat)/1000000) ((faceBalance c016)) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict056
