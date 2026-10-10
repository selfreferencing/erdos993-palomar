module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.PositiveOutput006

def records : List Comparison := [
  -- A126.positive_gp; A126: D=8/5, lambda in [3/2,7/4], y in [3/4,15/16], m=49/100: delta > 616476/1000000 > 0; B_balance > 49185/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((616476 : Rat)) .lt,
  -- A126.positive_g; A126: D=8/5, lambda in [3/2,7/4], y in [3/4,15/16], m=49/100: delta > 616476/1000000 > 0; B_balance > 49185/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((49185 : Rat)) .lt,
  -- A127.positive_gp; A127: D=8/5, lambda in [3/2,7/4], y in [15/16,9/8], m=49/100: delta > 546430/1000000 > 0; B_balance > 68700/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((546430 : Rat)) .lt,
  -- A127.positive_g; A127: D=8/5, lambda in [3/2,7/4], y in [15/16,9/8], m=49/100: delta > 546430/1000000 > 0; B_balance > 68700/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((68700 : Rat)) .lt,
  -- A128.positive_gp; A128: D=8/5, lambda in [3/2,7/4], y in [9/8,21/16], m=49/100: delta > 486214/1000000 > 0; B_balance > 90358/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((486214 : Rat)) .lt,
  -- A128.positive_g; A128: D=8/5, lambda in [3/2,7/4], y in [9/8,21/16], m=49/100: delta > 486214/1000000 > 0; B_balance > 90358/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((90358 : Rat)) .lt,
  -- A129.positive_gp; A129: D=8/5, lambda in [3/2,7/4], y in [21/16,3/2], m=49/100: delta > 442314/1000000 > 0; B_balance > 128432/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((442314 : Rat)) .lt,
  -- A129.positive_g; A129: D=8/5, lambda in [3/2,7/4], y in [21/16,3/2], m=49/100: delta > 442314/1000000 > 0; B_balance > 128432/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((128432 : Rat)) .lt,
  -- A130.positive_gp; A130: D=8/5, lambda in [3/2,7/4], y in [3/2,27/16], m=49/100: delta > 422005/1000000 > 0; B_balance > 227787/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((422005 : Rat)) .lt,
  -- A130.positive_g; A130: D=8/5, lambda in [3/2,7/4], y in [3/2,27/16], m=49/100: delta > 422005/1000000 > 0; B_balance > 227787/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((227787 : Rat)) .lt,
  -- A131.positive_gp; A131: D=8/5, lambda in [3/2,7/4], y in [27/16,15/8], m=49/100: delta > 433630/1000000 > 0; B_balance > 474688/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((433630 : Rat)) .lt,
  -- A131.positive_g; A131: D=8/5, lambda in [3/2,7/4], y in [27/16,15/8], m=49/100: delta > 433630/1000000 > 0; B_balance > 474688/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((474688 : Rat)) .lt,
  -- A132.positive_gp; A132: D=8/5, lambda in [3/2,7/4], y in [15/8,33/16], m=49/100: delta > 486734/1000000 > 0; B_balance > 970117/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((486734 : Rat)) .lt,
  -- A132.positive_g; A132: D=8/5, lambda in [3/2,7/4], y in [15/8,33/16], m=49/100: delta > 486734/1000000 > 0; B_balance > 970117/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((970117 : Rat)) .lt,
  -- A133.positive_gp; A133: D=8/5, lambda in [3/2,7/4], y in [33/16,9/4], m=49/100: delta > 592286/1000000 > 0; B_balance > 1778312/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((592286 : Rat)) .lt,
  -- A133.positive_g; A133: D=8/5, lambda in [3/2,7/4], y in [33/16,9/4], m=49/100: delta > 592286/1000000 > 0; B_balance > 1778312/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((1778312 : Rat)) .lt,
  -- A134.positive_gp; A134: D=8/5, lambda in [3/2,7/4], y in [9/4,21/8], m=49/100: delta > 542322/1000000 > 0; B_balance > 2213078/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((542322 : Rat)) .lt,
  -- A134.positive_g; A134: D=8/5, lambda in [3/2,7/4], y in [9/4,21/8], m=49/100: delta > 542322/1000000 > 0; B_balance > 2213078/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((2213078 : Rat)) .lt,
  -- A135.positive_gp; A135: D=8/5, lambda in [3/2,7/4], y in [21/8,3], m=49/100: delta > 1141838/1000000 > 0; B_balance > 5960044/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((1141838 : Rat)) .lt,
  -- A135.positive_g; A135: D=8/5, lambda in [3/2,7/4], y in [21/8,3], m=49/100: delta > 1141838/1000000 > 0; B_balance > 5960044/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((5960044 : Rat)) .lt,
  -- A136.positive_gp; A136: D=9/5, lambda in [7/4,2], y in [0,3/8], m=1/3: delta > 777969/1000000 > 0; B_balance > 162481/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((777969 : Rat)) .lt,
  -- A136.positive_g; A136: D=9/5, lambda in [7/4,2], y in [0,3/8], m=1/3: delta > 777969/1000000 > 0; B_balance > 162481/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((162481 : Rat)) .lt,
  -- A137.positive_gp; A137: D=9/5, lambda in [7/4,2], y in [3/8,9/16], m=1/3: delta > 757675/1000000 > 0; B_balance > 100187/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((757675 : Rat)) .lt,
  -- A137.positive_g; A137: D=9/5, lambda in [7/4,2], y in [3/8,9/16], m=1/3: delta > 757675/1000000 > 0; B_balance > 100187/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((100187 : Rat)) .lt,
  -- A138.positive_gp; A138: D=9/5, lambda in [7/4,2], y in [9/16,3/4], m=9/20: delta > 687717/1000000 > 0; B_balance > 48845/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((687717 : Rat)) .lt,
  -- A138.positive_g; A138: D=9/5, lambda in [7/4,2], y in [9/16,3/4], m=9/20: delta > 687717/1000000 > 0; B_balance > 48845/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((48845 : Rat)) .lt,
  -- A139.positive_gp; A139: D=9/5, lambda in [7/4,2], y in [3/4,15/16], m=49/100: delta > 617489/1000000 > 0; B_balance > 71100/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((617489 : Rat)) .lt,
  -- A139.positive_g; A139: D=9/5, lambda in [7/4,2], y in [3/4,15/16], m=49/100: delta > 617489/1000000 > 0; B_balance > 71100/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((71100 : Rat)) .lt,
  -- A140.positive_gp; A140: D=9/5, lambda in [7/4,2], y in [15/16,9/8], m=49/100: delta > 550535/1000000 > 0; B_balance > 100412/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((550535 : Rat)) .lt,
  -- A140.positive_g; A140: D=9/5, lambda in [7/4,2], y in [15/16,9/8], m=49/100: delta > 550535/1000000 > 0; B_balance > 100412/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((100412 : Rat)) .lt,
  -- A141.positive_gp; A141: D=9/5, lambda in [7/4,2], y in [9/8,21/16], m=49/100: delta > 492344/1000000 > 0; B_balance > 135920/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((492344 : Rat)) .lt,
  -- A141.positive_g; A141: D=9/5, lambda in [7/4,2], y in [9/8,21/16], m=49/100: delta > 492344/1000000 > 0; B_balance > 135920/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((135920 : Rat)) .lt,
  -- A142.positive_gp; A142: D=9/5, lambda in [7/4,2], y in [21/16,3/2], m=49/100: delta > 448823/1000000 > 0; B_balance > 186645/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((448823 : Rat)) .lt,
  -- A142.positive_g; A142: D=9/5, lambda in [7/4,2], y in [21/16,3/2], m=49/100: delta > 448823/1000000 > 0; B_balance > 186645/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((186645 : Rat)) .lt,
  -- A143.positive_gp; A143: D=9/5, lambda in [7/4,2], y in [3/2,27/16], m=49/100: delta > 426888/1000000 > 0; B_balance > 283665/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((426888 : Rat)) .lt,
  -- A143.positive_g; A143: D=9/5, lambda in [7/4,2], y in [3/2,27/16], m=49/100: delta > 426888/1000000 > 0; B_balance > 283665/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((283665 : Rat)) .lt,
  -- A144.positive_gp; A144: D=9/5, lambda in [7/4,2], y in [27/16,15/8], m=49/100: delta > 434520/1000000 > 0; B_balance > 490149/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((434520 : Rat)) .lt,
  -- A144.positive_g; A144: D=9/5, lambda in [7/4,2], y in [27/16,15/8], m=49/100: delta > 434520/1000000 > 0; B_balance > 490149/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((490149 : Rat)) .lt,
  -- A145.positive_gp; A145: D=9/5, lambda in [7/4,2], y in [15/8,33/16], m=49/100: delta > 480889/1000000 > 0; B_balance > 887820/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((480889 : Rat)) .lt,
  -- A145.positive_g; A145: D=9/5, lambda in [7/4,2], y in [15/8,33/16], m=49/100: delta > 480889/1000000 > 0; B_balance > 887820/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((887820 : Rat)) .lt,
  -- A146.positive_gp; A146: D=9/5, lambda in [7/4,2], y in [33/16,9/4], m=49/100: delta > 576538/1000000 > 0; B_balance > 1539352/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((576538 : Rat)) .lt,
  -- A146.positive_g; A146: D=9/5, lambda in [7/4,2], y in [33/16,9/4], m=49/100: delta > 576538/1000000 > 0; B_balance > 1539352/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((1539352 : Rat)) .lt,
  -- A147.positive_gp; A147: D=9/5, lambda in [7/4,2], y in [9/4,21/8], m=49/100: delta > 518593/1000000 > 0; B_balance > 1872336/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((518593 : Rat)) .lt,
  -- A147.positive_g; A147: D=9/5, lambda in [7/4,2], y in [9/4,21/8], m=49/100: delta > 518593/1000000 > 0; B_balance > 1872336/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((1872336 : Rat)) .lt,
  -- A148.positive_gp; A148: D=9/5, lambda in [7/4,2], y in [21/8,3], m=49/100: delta > 1077056/1000000 > 0; B_balance > 4993081/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((1077056 : Rat)) .lt,
  -- A148.positive_g; A148: D=9/5, lambda in [7/4,2], y in [21/8,3], m=49/100: delta > 1077056/1000000 > 0; B_balance > 4993081/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((4993081 : Rat)) .lt,
  -- A149.positive_gp; A149: D=21/10, lambda in [2,7/3], y in [0,3/8], m=0: delta > 762007/1000000 > 0; B_balance > 187702/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((762007 : Rat)) .lt,
  -- A149.positive_g; A149: D=21/10, lambda in [2,7/3], y in [0,3/8], m=0: delta > 762007/1000000 > 0; B_balance > 187702/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((187702 : Rat)) .lt,
  -- A150.positive_gp; A150: D=21/10, lambda in [2,7/3], y in [3/8,3/4], m=2/5: delta > 612091/1000000 > 0; B_balance > 29637/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((612091 : Rat)) .lt,
  -- A150.positive_g; A150: D=21/10, lambda in [2,7/3], y in [3/8,3/4], m=2/5: delta > 612091/1000000 > 0; B_balance > 29637/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((29637 : Rat)) .lt,
  -- A151.positive_gp; A151: D=21/10, lambda in [2,7/3], y in [3/4,9/8], m=49/100: delta > 451196/1000000 > 0; B_balance > 5967/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((451196 : Rat)) .lt,
  -- A151.positive_g; A151: D=21/10, lambda in [2,7/3], y in [3/4,9/8], m=49/100: delta > 451196/1000000 > 0; B_balance > 5967/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((5967 : Rat)) .lt,
  -- A152.positive_gp; A152: D=21/10, lambda in [2,7/3], y in [9/8,21/16], m=49/100: delta > 488183/1000000 > 0; B_balance > 152603/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((488183 : Rat)) .lt,
  -- A152.positive_g; A152: D=21/10, lambda in [2,7/3], y in [9/8,21/16], m=49/100: delta > 488183/1000000 > 0; B_balance > 152603/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((152603 : Rat)) .lt,
  -- A153.positive_gp; A153: D=21/10, lambda in [2,7/3], y in [21/16,3/2], m=49/100: delta > 444172/1000000 > 0; B_balance > 202684/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((444172 : Rat)) .lt,
  -- A153.positive_g; A153: D=21/10, lambda in [2,7/3], y in [21/16,3/2], m=49/100: delta > 444172/1000000 > 0; B_balance > 202684/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((202684 : Rat)) .lt,
  -- A154.positive_gp; A154: D=21/10, lambda in [2,7/3], y in [3/2,27/16], m=49/100: delta > 419493/1000000 > 0; B_balance > 284530/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((419493 : Rat)) .lt,
  -- A154.positive_g; A154: D=21/10, lambda in [2,7/3], y in [3/2,27/16], m=49/100: delta > 419493/1000000 > 0; B_balance > 284530/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((284530 : Rat)) .lt,
  -- A155.positive_gp; A155: D=21/10, lambda in [2,7/3], y in [27/16,15/8], m=49/100: delta > 421680/1000000 > 0; B_balance > 444171/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((421680 : Rat)) .lt,
  -- A155.positive_g; A155: D=21/10, lambda in [2,7/3], y in [27/16,15/8], m=49/100: delta > 421680/1000000 > 0; B_balance > 444171/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((444171 : Rat)) .lt,
  -- A156.positive_gp; A156: D=21/10, lambda in [2,7/3], y in [15/8,33/16], m=49/100: delta > 459434/1000000 > 0; B_balance > 748301/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((459434 : Rat)) .lt,
  -- A156.positive_g; A156: D=21/10, lambda in [2,7/3], y in [15/8,33/16], m=49/100: delta > 459434/1000000 > 0; B_balance > 748301/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((748301 : Rat)) .lt,
  -- A157.positive_gp; A157: D=21/10, lambda in [2,7/3], y in [33/16,9/4], m=49/100: delta > 542783/1000000 > 0; B_balance > 1256418/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((542783 : Rat)) .lt,
  -- A157.positive_g; A157: D=21/10, lambda in [2,7/3], y in [33/16,9/4], m=49/100: delta > 542783/1000000 > 0; B_balance > 1256418/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((1256418 : Rat)) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 64 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.PositiveOutput006
