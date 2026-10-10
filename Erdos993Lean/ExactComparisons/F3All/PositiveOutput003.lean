module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.PositiveOutput003

def records : List Comparison := [
  -- A030.positive_gp; A030: D=6/5, lambda in [3/5,7/8], y in [3/2,27/16], m=49/100: delta > 519694/1000000 > 0; B_balance > 841159/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((519694 : Rat)) .lt,
  -- A030.positive_g; A030: D=6/5, lambda in [3/5,7/8], y in [3/2,27/16], m=49/100: delta > 519694/1000000 > 0; B_balance > 841159/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((841159 : Rat)) .lt,
  -- A031.positive_gp; A031: D=6/5, lambda in [3/5,7/8], y in [27/16,15/8], m=49/100: delta > 577227/1000000 > 0; B_balance > 1812656/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((577227 : Rat)) .lt,
  -- A031.positive_g; A031: D=6/5, lambda in [3/5,7/8], y in [27/16,15/8], m=49/100: delta > 577227/1000000 > 0; B_balance > 1812656/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((1812656 : Rat)) .lt,
  -- A032.positive_gp; A032: D=6/5, lambda in [3/5,7/8], y in [15/8,9/4], m=49/100: delta > 467613/1000000 > 0; B_balance > 1819255/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((467613 : Rat)) .lt,
  -- A032.positive_g; A032: D=6/5, lambda in [3/5,7/8], y in [15/8,9/4], m=49/100: delta > 467613/1000000 > 0; B_balance > 1819255/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((1819255 : Rat)) .lt,
  -- A033.positive_gp; A033: D=6/5, lambda in [3/5,7/8], y in [9/4,3], m=49/100: delta > 468270/1000000 > 0; B_balance > 3823214/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((468270 : Rat)) .lt,
  -- A033.positive_g; A033: D=6/5, lambda in [3/5,7/8], y in [9/4,3], m=49/100: delta > 468270/1000000 > 0; B_balance > 3823214/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((3823214 : Rat)) .lt,
  -- A034.positive_gp; A034: D=6/5, lambda in [7/8,28/25], y in [0,3/16], m=0: delta > 945668/1000000 > 0; B_balance > 207139/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((945668 : Rat)) .lt,
  -- A034.positive_g; A034: D=6/5, lambda in [7/8,28/25], y in [0,3/16], m=0: delta > 945668/1000000 > 0; B_balance > 207139/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((207139 : Rat)) .lt,
  -- A035.positive_gp; A035: D=6/5, lambda in [7/8,28/25], y in [3/16,9/32], m=1/3: delta > 932470/1000000 > 0; B_balance > 97185/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((932470 : Rat)) .lt,
  -- A035.positive_g; A035: D=6/5, lambda in [7/8,28/25], y in [3/16,9/32], m=1/3: delta > 932470/1000000 > 0; B_balance > 97185/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((97185 : Rat)) .lt,
  -- A036.positive_gp; A036: D=6/5, lambda in [7/8,28/25], y in [9/32,3/8], m=1/3: delta > 890731/1000000 > 0; B_balance > 16977/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((890731 : Rat)) .lt,
  -- A036.positive_g; A036: D=6/5, lambda in [7/8,28/25], y in [9/32,3/8], m=1/3: delta > 890731/1000000 > 0; B_balance > 16977/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((16977 : Rat)) .lt,
  -- A037.positive_gp; A037: D=6/5, lambda in [7/8,28/25], y in [3/8,27/64], m=2/5: delta > 888230/1000000 > 0; B_balance > 7288/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((888230 : Rat)) .lt,
  -- A037.positive_g; A037: D=6/5, lambda in [7/8,28/25], y in [3/8,27/64], m=2/5: delta > 888230/1000000 > 0; B_balance > 7288/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((7288 : Rat)) .lt,
  -- A038.positive_gp; A038: D=6/5, lambda in [7/8,28/25], y in [27/64,15/32], m=49/100: delta > 867907/1000000 > 0; B_balance > 1263/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((867907 : Rat)) .lt,
  -- A038.positive_g; A038: D=6/5, lambda in [7/8,28/25], y in [27/64,15/32], m=49/100: delta > 867907/1000000 > 0; B_balance > 1263/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((1263 : Rat)) .lt,
  -- A039.positive_gp; A039: D=6/5, lambda in [7/8,28/25], y in [15/32,33/64], m=49/100: delta > 847603/1000000 > 0; B_balance > 4559/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((847603 : Rat)) .lt,
  -- A039.positive_g; A039: D=6/5, lambda in [7/8,28/25], y in [15/32,33/64], m=49/100: delta > 847603/1000000 > 0; B_balance > 4559/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((4559 : Rat)) .lt,
  -- A040.positive_gp; A040: D=6/5, lambda in [7/8,28/25], y in [33/64,9/16], m=49/100: delta > 827390/1000000 > 0; B_balance > 8695/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((827390 : Rat)) .lt,
  -- A040.positive_g; A040: D=6/5, lambda in [7/8,28/25], y in [33/64,9/16], m=49/100: delta > 827390/1000000 > 0; B_balance > 8695/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((8695 : Rat)) .lt,
  -- A041.positive_gp; A041: D=6/5, lambda in [7/8,28/25], y in [9/16,39/64], m=49/100: delta > 807340/1000000 > 0; B_balance > 13723/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((807340 : Rat)) .lt,
  -- A041.positive_g; A041: D=6/5, lambda in [7/8,28/25], y in [9/16,39/64], m=49/100: delta > 807340/1000000 > 0; B_balance > 13723/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((13723 : Rat)) .lt,
  -- A042.positive_gp; A042: D=6/5, lambda in [7/8,28/25], y in [39/64,21/32], m=49/100: delta > 787532/1000000 > 0; B_balance > 20021/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((787532 : Rat)) .lt,
  -- A042.positive_g; A042: D=6/5, lambda in [7/8,28/25], y in [39/64,21/32], m=49/100: delta > 787532/1000000 > 0; B_balance > 20021/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((20021 : Rat)) .lt,
  -- A043.positive_gp; A043: D=6/5, lambda in [7/8,28/25], y in [21/32,45/64], m=49/100: delta > 768046/1000000 > 0; B_balance > 27576/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((768046 : Rat)) .lt,
  -- A043.positive_g; A043: D=6/5, lambda in [7/8,28/25], y in [21/32,45/64], m=49/100: delta > 768046/1000000 > 0; B_balance > 27576/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((27576 : Rat)) .lt,
  -- A044.positive_gp; A044: D=6/5, lambda in [7/8,28/25], y in [45/64,3/4], m=49/100: delta > 748967/1000000 > 0; B_balance > 36275/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((748967 : Rat)) .lt,
  -- A044.positive_g; A044: D=6/5, lambda in [7/8,28/25], y in [45/64,3/4], m=49/100: delta > 748967/1000000 > 0; B_balance > 36275/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((36275 : Rat)) .lt,
  -- A045.positive_gp; A045: D=6/5, lambda in [7/8,28/25], y in [3/4,51/64], m=49/100: delta > 730381/1000000 > 0; B_balance > 46255/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((730381 : Rat)) .lt,
  -- A045.positive_g; A045: D=6/5, lambda in [7/8,28/25], y in [3/4,51/64], m=49/100: delta > 730381/1000000 > 0; B_balance > 46255/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((46255 : Rat)) .lt,
  -- A046.positive_gp; A046: D=6/5, lambda in [7/8,28/25], y in [51/64,27/32], m=49/100: delta > 712378/1000000 > 0; B_balance > 57685/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((712378 : Rat)) .lt,
  -- A046.positive_g; A046: D=6/5, lambda in [7/8,28/25], y in [51/64,27/32], m=49/100: delta > 712378/1000000 > 0; B_balance > 57685/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((57685 : Rat)) .lt,
  -- A047.positive_gp; A047: D=6/5, lambda in [7/8,28/25], y in [27/32,15/16], m=49/100: delta > 647307/1000000 > 0; B_balance > 6605/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((647307 : Rat)) .lt,
  -- A047.positive_g; A047: D=6/5, lambda in [7/8,28/25], y in [27/32,15/16], m=49/100: delta > 647307/1000000 > 0; B_balance > 6605/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((6605 : Rat)) .lt,
  -- A048.positive_gp; A048: D=6/5, lambda in [7/8,28/25], y in [15/16,33/32], m=49/100: delta > 613854/1000000 > 0; B_balance > 23088/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((613854 : Rat)) .lt,
  -- A048.positive_g; A048: D=6/5, lambda in [7/8,28/25], y in [15/16,33/32], m=49/100: delta > 613854/1000000 > 0; B_balance > 23088/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((23088 : Rat)) .lt,
  -- A049.positive_gp; A049: D=6/5, lambda in [7/8,28/25], y in [33/32,9/8], m=49/100: delta > 584429/1000000 > 0; B_balance > 47842/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((584429 : Rat)) .lt,
  -- A049.positive_g; A049: D=6/5, lambda in [7/8,28/25], y in [33/32,9/8], m=49/100: delta > 584429/1000000 > 0; B_balance > 47842/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((47842 : Rat)) .lt,
  -- A050.positive_gp; A050: D=6/5, lambda in [7/8,28/25], y in [9/8,39/32], m=49/100: delta > 557086/1000000 > 0; B_balance > 73491/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((557086 : Rat)) .lt,
  -- A050.positive_g; A050: D=6/5, lambda in [7/8,28/25], y in [9/8,39/32], m=49/100: delta > 557086/1000000 > 0; B_balance > 73491/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((73491 : Rat)) .lt,
  -- A051.positive_gp; A051: D=6/5, lambda in [7/8,28/25], y in [39/32,21/16], m=49/100: delta > 534598/1000000 > 0; B_balance > 112250/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((534598 : Rat)) .lt,
  -- A051.positive_g; A051: D=6/5, lambda in [7/8,28/25], y in [39/32,21/16], m=49/100: delta > 534598/1000000 > 0; B_balance > 112250/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((112250 : Rat)) .lt,
  -- A052.positive_gp; A052: D=6/5, lambda in [7/8,28/25], y in [21/16,45/32], m=49/100: delta > 518421/1000000 > 0; B_balance > 176032/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((518421 : Rat)) .lt,
  -- A052.positive_g; A052: D=6/5, lambda in [7/8,28/25], y in [21/16,45/32], m=49/100: delta > 518421/1000000 > 0; B_balance > 176032/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((176032 : Rat)) .lt,
  -- A053.positive_gp; A053: D=6/5, lambda in [7/8,28/25], y in [45/32,3/2], m=49/100: delta > 509617/1000000 > 0; B_balance > 278803/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((509617 : Rat)) .lt,
  -- A053.positive_g; A053: D=6/5, lambda in [7/8,28/25], y in [45/32,3/2], m=49/100: delta > 509617/1000000 > 0; B_balance > 278803/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((278803 : Rat)) .lt,
  -- A054.positive_gp; A054: D=6/5, lambda in [7/8,28/25], y in [3/2,51/32], m=49/100: delta > 509320/1000000 > 0; B_balance > 437939/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((509320 : Rat)) .lt,
  -- A054.positive_g; A054: D=6/5, lambda in [7/8,28/25], y in [3/2,51/32], m=49/100: delta > 509320/1000000 > 0; B_balance > 437939/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((437939 : Rat)) .lt,
  -- A055.positive_gp; A055: D=6/5, lambda in [7/8,28/25], y in [51/32,27/16], m=49/100: delta > 518739/1000000 > 0; B_balance > 672658/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((518739 : Rat)) .lt,
  -- A055.positive_g; A055: D=6/5, lambda in [7/8,28/25], y in [51/32,27/16], m=49/100: delta > 518739/1000000 > 0; B_balance > 672658/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((672658 : Rat)) .lt,
  -- A056.positive_gp; A056: D=6/5, lambda in [7/8,28/25], y in [27/16,15/8], m=49/100: delta > 423452/1000000 > 0; B_balance > 273588/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((423452 : Rat)) .lt,
  -- A056.positive_g; A056: D=6/5, lambda in [7/8,28/25], y in [27/16,15/8], m=49/100: delta > 423452/1000000 > 0; B_balance > 273588/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((273588 : Rat)) .lt,
  -- A057.positive_gp; A057: D=6/5, lambda in [7/8,28/25], y in [15/8,33/16], m=49/100: delta > 501668/1000000 > 0; B_balance > 1345567/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((501668 : Rat)) .lt,
  -- A057.positive_g; A057: D=6/5, lambda in [7/8,28/25], y in [15/8,33/16], m=49/100: delta > 501668/1000000 > 0; B_balance > 1345567/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((1345567 : Rat)) .lt,
  -- A058.positive_gp; A058: D=6/5, lambda in [7/8,28/25], y in [33/16,9/4], m=49/100: delta > 642464/1000000 > 0; B_balance > 2991888/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((642464 : Rat)) .lt,
  -- A058.positive_g; A058: D=6/5, lambda in [7/8,28/25], y in [33/16,9/4], m=49/100: delta > 642464/1000000 > 0; B_balance > 2991888/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((2991888 : Rat)) .lt,
  -- A059.positive_gp; A059: D=6/5, lambda in [7/8,28/25], y in [9/4,21/8], m=49/100: delta > 624240/1000000 > 0; B_balance > 4017490/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((624240 : Rat)) .lt,
  -- A059.positive_g; A059: D=6/5, lambda in [7/8,28/25], y in [9/4,21/8], m=49/100: delta > 624240/1000000 > 0; B_balance > 4017490/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((4017490 : Rat)) .lt,
  -- A060.positive_gp; A060: D=6/5, lambda in [7/8,28/25], y in [21/8,3], m=49/100: delta > 1361431/1000000 > 0; B_balance > 10741904/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((1361431 : Rat)) .lt,
  -- A060.positive_g; A060: D=6/5, lambda in [7/8,28/25], y in [21/8,3], m=49/100: delta > 1361431/1000000 > 0; B_balance > 10741904/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((10741904 : Rat)) .lt,
  -- A061.positive_gp; A061: D=6/5, lambda in [28/25,263/200], y in [0,3/8], m=1/3: delta > 785168/1000000 > 0; B_balance > 24875/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((785168 : Rat)) .lt,
  -- A061.positive_g; A061: D=6/5, lambda in [28/25,263/200], y in [0,3/8], m=1/3: delta > 785168/1000000 > 0; B_balance > 24875/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((24875 : Rat)) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 64 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.PositiveOutput003
