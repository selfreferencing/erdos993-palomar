module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.PositiveOutput001

def records : List Comparison := [
  -- C001.positive_g; C001: D=6/5, v=263/200, y in [0,21/50], type L: ell_star > 208674/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((208674 : Rat)) .lt,
  -- C002.positive_g; C002: D=6/5, v=263/200, y in [21/50,63/100], type L: ell_star > 31406/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((31406 : Rat)) .lt,
  -- C003.positive_g; C003: D=6/5, v=263/200, y in [63/100,273/400], type C: d0 > 997182/1000000 > 0; C_balance > 4069/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((4069 : Rat)) .lt,
  -- C003.positive_gp; C003: D=6/5, v=263/200, y in [63/100,273/400], type C: d0 > 997182/1000000 > 0; C_balance > 4069/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((997182 : Rat)) .lt,
  -- C004.positive_g; C004: D=6/5, v=263/200, y in [273/400,147/200], type C: d0 > 976324/1000000 > 0; C_balance > 791/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((791 : Rat)) .lt,
  -- C004.positive_gp; C004: D=6/5, v=263/200, y in [273/400,147/200], type C: d0 > 976324/1000000 > 0; C_balance > 791/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((976324 : Rat)) .lt,
  -- C005.positive_g; C005: D=6/5, v=263/200, y in [147/200,63/80], type C: d0 > 955748/1000000 > 0; C_balance > 3588/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((3588 : Rat)) .lt,
  -- C005.positive_gp; C005: D=6/5, v=263/200, y in [147/200,63/80], type C: d0 > 955748/1000000 > 0; C_balance > 3588/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((955748 : Rat)) .lt,
  -- C006.positive_g; C006: D=6/5, v=263/200, y in [63/80,21/25], type C: d0 > 935570/1000000 > 0; C_balance > 11894/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((11894 : Rat)) .lt,
  -- C006.positive_gp; C006: D=6/5, v=263/200, y in [63/80,21/25], type C: d0 > 935570/1000000 > 0; C_balance > 11894/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((935570 : Rat)) .lt,
  -- C007.positive_g; C007: D=7/5, v=3/2, y in [0,23/50], type L: ell_star > 159172/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((159172 : Rat)) .lt,
  -- C008.positive_g; C008: D=7/5, v=3/2, y in [23/50,69/100], type L: ell_star > 34603/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((34603 : Rat)) .lt,
  -- C009.positive_g; C009: D=7/5, v=3/2, y in [69/100,299/400], type L: ell_star > 9801/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((9801 : Rat)) .lt,
  -- C010.positive_g; C010: D=7/5, v=3/2, y in [299/400,161/200], type C: d0 > 986024/1000000 > 0; C_balance > 13142/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((13142 : Rat)) .lt,
  -- C010.positive_gp; C010: D=7/5, v=3/2, y in [299/400,161/200], type C: d0 > 986024/1000000 > 0; C_balance > 13142/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((986024 : Rat)) .lt,
  -- C011.positive_g; C011: D=7/5, v=3/2, y in [161/200,23/25], type C: d0 > 951207/1000000 > 0; C_balance > 5465/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((5465 : Rat)) .lt,
  -- C011.positive_gp; C011: D=7/5, v=3/2, y in [161/200,23/25], type C: d0 > 951207/1000000 > 0; C_balance > 5465/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((951207 : Rat)) .lt,
  -- C012.positive_g; C012: D=8/5, v=7/4, y in [0,51/100], type L: ell_star > 72713/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((72713 : Rat)) .lt,
  -- C013.positive_g; C013: D=8/5, v=7/4, y in [51/100,51/80], type L: ell_star > 113077/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((113077 : Rat)) .lt,
  -- C014.positive_g; C014: D=8/5, v=7/4, y in [51/80,153/200], type L: ell_star > 17255/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((17255 : Rat)) .lt,
  -- C015.positive_g; C015: D=8/5, v=7/4, y in [153/200,663/800], type C: d0 > 988756/1000000 > 0; C_balance > 7355/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((7355 : Rat)) .lt,
  -- C015.positive_gp; C015: D=8/5, v=7/4, y in [153/200,663/800], type C: d0 > 988756/1000000 > 0; C_balance > 7355/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((988756 : Rat)) .lt,
  -- C016.positive_g; C016: D=8/5, v=7/4, y in [663/800,357/400], type C: d0 > 966190/1000000 > 0; C_balance > 12043/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((12043 : Rat)) .lt,
  -- C016.positive_gp; C016: D=8/5, v=7/4, y in [663/800,357/400], type C: d0 > 966190/1000000 > 0; C_balance > 12043/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((966190 : Rat)) .lt,
  -- C017.positive_g; C017: D=8/5, v=7/4, y in [357/400,51/50], type C: d0 > 920782/1000000 > 0; C_balance > 7825/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((7825 : Rat)) .lt,
  -- C017.positive_gp; C017: D=8/5, v=7/4, y in [357/400,51/50], type C: d0 > 920782/1000000 > 0; C_balance > 7825/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((920782 : Rat)) .lt,
  -- C018.positive_g; C018: D=9/5, v=2, y in [0,11/20], type L: ell_star > 2534/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((2534 : Rat)) .lt,
  -- C019.positive_g; C019: D=9/5, v=2, y in [11/20,11/16], type L: ell_star > 72401/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((72401 : Rat)) .lt,
  -- C020.positive_g; C020: D=9/5, v=2, y in [11/16,121/160], type L: ell_star > 35988/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((35988 : Rat)) .lt,
  -- C021.positive_g; C021: D=9/5, v=2, y in [121/160,33/40], type C: d0 > 996211/1000000 > 0; C_balance > 1403/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((1403 : Rat)) .lt,
  -- C021.positive_gp; C021: D=9/5, v=2, y in [121/160,33/40], type C: d0 > 996211/1000000 > 0; C_balance > 1403/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((996211 : Rat)) .lt,
  -- C022.positive_g; C022: D=9/5, v=2, y in [33/40,55/64], type C: d0 > 986547/1000000 > 0; C_balance > 7930/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((7930 : Rat)) .lt,
  -- C022.positive_gp; C022: D=9/5, v=2, y in [33/40,55/64], type C: d0 > 986547/1000000 > 0; C_balance > 7930/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((986547 : Rat)) .lt,
  -- C023.positive_g; C023: D=9/5, v=2, y in [55/64,143/160], type C: d0 > 976078/1000000 > 0; C_balance > 10225/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((10225 : Rat)) .lt,
  -- C023.positive_gp; C023: D=9/5, v=2, y in [55/64,143/160], type C: d0 > 976078/1000000 > 0; C_balance > 10225/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((976078 : Rat)) .lt,
  -- C024.positive_g; C024: D=9/5, v=2, y in [143/160,77/80], type C: d0 > 954849/1000000 > 0; C_balance > 6286/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((6286 : Rat)) .lt,
  -- C024.positive_gp; C024: D=9/5, v=2, y in [143/160,77/80], type C: d0 > 954849/1000000 > 0; C_balance > 6286/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((954849 : Rat)) .lt,
  -- C025.positive_g; C025: D=9/5, v=2, y in [77/80,11/10], type C: d0 > 914201/1000000 > 0; C_balance > 4657/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((4657 : Rat)) .lt,
  -- C025.positive_gp; C025: D=9/5, v=2, y in [77/80,11/10], type C: d0 > 914201/1000000 > 0; C_balance > 4657/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((914201 : Rat)) .lt,
  -- C026.positive_g; C026: D=21/10, v=7/3, y in [0,121/400], type L: ell_star > 232032/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((232032 : Rat)) .lt,
  -- C027.positive_g; C027: D=21/10, v=7/3, y in [121/400,121/200], type L: ell_star > 68249/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((68249 : Rat)) .lt,
  -- C028.positive_g; C028: D=21/10, v=7/3, y in [121/200,121/160], type L: ell_star > 23056/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((23056 : Rat)) .lt,
  -- C029.positive_g; C029: D=21/10, v=7/3, y in [121/160,2541/3200], type L: ell_star > 14480/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((14480 : Rat)) .lt,
  -- C030.positive_g; C030: D=21/10, v=7/3, y in [2541/3200,5203/6400], type L: ell_star > 4850/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((4850 : Rat)) .lt,
  -- C031.positive_g; C031: D=21/10, v=7/3, y in [5203/6400,1331/1600], type C: d0 > 997337/1000000 > 0; C_balance > 2248/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((2248 : Rat)) .lt,
  -- C031.positive_gp; C031: D=21/10, v=7/3, y in [5203/6400,1331/1600], type C: d0 > 997337/1000000 > 0; C_balance > 2248/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((997337 : Rat)) .lt,
  -- C032.positive_g; C032: D=21/10, v=7/3, y in [1331/1600,1089/1280], type C: d0 > 992292/1000000 > 0; C_balance > 688/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((688 : Rat)) .lt,
  -- C032.positive_gp; C032: D=21/10, v=7/3, y in [1331/1600,1089/1280], type C: d0 > 992292/1000000 > 0; C_balance > 688/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((992292 : Rat)) .lt,
  -- C033.positive_g; C033: D=21/10, v=7/3, y in [1089/1280,11011/12800], type C: d0 > 989861/1000000 > 0; C_balance > 2095/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((2095 : Rat)) .lt,
  -- C033.positive_gp; C033: D=21/10, v=7/3, y in [1089/1280,11011/12800], type C: d0 > 989861/1000000 > 0; C_balance > 2095/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((989861 : Rat)) .lt,
  -- C034.positive_g; C034: D=21/10, v=7/3, y in [11011/12800,2783/3200], type C: d0 > 987365/1000000 > 0; C_balance > 1920/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((1920 : Rat)) .lt,
  -- C034.positive_gp; C034: D=21/10, v=7/3, y in [11011/12800,2783/3200], type C: d0 > 987365/1000000 > 0; C_balance > 1920/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((987365 : Rat)) .lt,
  -- C035.positive_g; C035: D=21/10, v=7/3, y in [2783/3200,11253/12800], type C: d0 > 984881/1000000 > 0; C_balance > 1914/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((1914 : Rat)) .lt,
  -- C035.positive_gp; C035: D=21/10, v=7/3, y in [2783/3200,11253/12800], type C: d0 > 984881/1000000 > 0; C_balance > 1914/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((984881 : Rat)) .lt,
  -- C036.positive_g; C036: D=21/10, v=7/3, y in [11253/12800,5687/6400], type C: d0 > 982409/1000000 > 0; C_balance > 2076/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((2076 : Rat)) .lt,
  -- C036.positive_gp; C036: D=21/10, v=7/3, y in [11253/12800,5687/6400], type C: d0 > 982409/1000000 > 0; C_balance > 2076/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((982409 : Rat)) .lt,
  -- C037.positive_g; C037: D=21/10, v=7/3, y in [5687/6400,363/400], type C: d0 > 977428/1000000 > 0; C_balance > 186/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((186 : Rat)) .lt,
  -- C037.positive_gp; C037: D=21/10, v=7/3, y in [5687/6400,363/400], type C: d0 > 977428/1000000 > 0; C_balance > 186/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((977428 : Rat)) .lt,
  -- C038.positive_g; C038: D=21/10, v=7/3, y in [363/400,5929/6400], type C: d0 > 972577/1000000 > 0; C_balance > 1351/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((1351 : Rat)) .lt,
  -- C038.positive_gp; C038: D=21/10, v=7/3, y in [363/400,5929/6400], type C: d0 > 972577/1000000 > 0; C_balance > 1351/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((972577 : Rat)) .lt,
  -- C039.positive_g; C039: D=21/10, v=7/3, y in [5929/6400,121/128], type C: d0 > 967787/1000000 > 0; C_balance > 3155/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((3155 : Rat)) .lt,
  -- C039.positive_gp; C039: D=21/10, v=7/3, y in [5929/6400,121/128], type C: d0 > 967787/1000000 > 0; C_balance > 3155/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((967787 : Rat)) .lt,
  -- C040.positive_g; C040: D=21/10, v=7/3, y in [121/128,1573/1600], type C: d0 > 958102/1000000 > 0; C_balance > 1185/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((1185 : Rat)) .lt,
  -- C040.positive_gp; C040: D=21/10, v=7/3, y in [121/128,1573/1600], type C: d0 > 958102/1000000 > 0; C_balance > 1185/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((958102 : Rat)) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 64 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.PositiveOutput001
