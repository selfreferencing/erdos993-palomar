module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.PositiveOutput002

def records : List Comparison := [
  -- C041.positive_g; C041: D=21/10, v=7/3, y in [1573/1600,3267/3200], type C: d0 > 949016/1000000 > 0; C_balance > 7981/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((7981 : Rat)) .lt,
  -- C041.positive_gp; C041: D=21/10, v=7/3, y in [1573/1600,3267/3200], type C: d0 > 949016/1000000 > 0; C_balance > 7981/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((949016 : Rat)) .lt,
  -- C042.positive_g; C042: D=21/10, v=7/3, y in [3267/3200,847/800], type C: d0 > 940268/1000000 > 0; C_balance > 17109/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((17109 : Rat)) .lt,
  -- C042.positive_gp; C042: D=21/10, v=7/3, y in [3267/3200,847/800], type C: d0 > 940268/1000000 > 0; C_balance > 17109/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((940268 : Rat)) .lt,
  -- C043.positive_g; C043: D=21/10, v=7/3, y in [847/800,121/100], type C: d0 > 903496/1000000 > 0; C_balance > 2508/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((2508 : Rat)) .lt,
  -- C043.positive_gp; C043: D=21/10, v=7/3, y in [847/800,121/100], type C: d0 > 903496/1000000 > 0; C_balance > 2508/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((903496 : Rat)) .lt,
  -- A001.positive_gp; A001: D=6/5, lambda in [1/3,3/5], y in [0,3/32], m=0: delta > 1074344/1000000 > 0; B_balance > 197190/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((1074344 : Rat)) .lt,
  -- A001.positive_g; A001: D=6/5, lambda in [1/3,3/5], y in [0,3/32], m=0: delta > 1074344/1000000 > 0; B_balance > 197190/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((197190 : Rat)) .lt,
  -- A002.positive_gp; A002: D=6/5, lambda in [1/3,3/5], y in [3/32,3/16], m=1/3: delta > 1033475/1000000 > 0; B_balance > 9028/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((1033475 : Rat)) .lt,
  -- A002.positive_g; A002: D=6/5, lambda in [1/3,3/5], y in [3/32,3/16], m=1/3: delta > 1033475/1000000 > 0; B_balance > 9028/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((9028 : Rat)) .lt,
  -- A003.positive_gp; A003: D=6/5, lambda in [1/3,3/5], y in [3/16,15/64], m=49/100: delta > 1031270/1000000 > 0; B_balance > 13252/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((1031270 : Rat)) .lt,
  -- A003.positive_g; A003: D=6/5, lambda in [1/3,3/5], y in [3/16,15/64], m=49/100: delta > 1031270/1000000 > 0; B_balance > 13252/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((13252 : Rat)) .lt,
  -- A004.positive_gp; A004: D=6/5, lambda in [1/3,3/5], y in [15/64,9/32], m=49/100: delta > 1012119/1000000 > 0; B_balance > 23985/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((1012119 : Rat)) .lt,
  -- A004.positive_g; A004: D=6/5, lambda in [1/3,3/5], y in [15/64,9/32], m=49/100: delta > 1012119/1000000 > 0; B_balance > 23985/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((23985 : Rat)) .lt,
  -- A005.positive_gp; A005: D=6/5, lambda in [1/3,3/5], y in [9/32,3/8], m=49/100: delta > 954116/1000000 > 0; B_balance > 10608/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((954116 : Rat)) .lt,
  -- A005.positive_g; A005: D=6/5, lambda in [1/3,3/5], y in [9/32,3/8], m=49/100: delta > 954116/1000000 > 0; B_balance > 10608/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((10608 : Rat)) .lt,
  -- A006.positive_gp; A006: D=6/5, lambda in [1/3,3/5], y in [3/8,15/32], m=49/100: delta > 916701/1000000 > 0; B_balance > 43795/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((916701 : Rat)) .lt,
  -- A006.positive_g; A006: D=6/5, lambda in [1/3,3/5], y in [3/8,15/32], m=49/100: delta > 916701/1000000 > 0; B_balance > 43795/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((43795 : Rat)) .lt,
  -- A007.positive_gp; A007: D=6/5, lambda in [1/3,3/5], y in [15/32,9/16], m=49/100: delta > 881557/1000000 > 0; B_balance > 91807/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((881557 : Rat)) .lt,
  -- A007.positive_g; A007: D=6/5, lambda in [1/3,3/5], y in [15/32,9/16], m=49/100: delta > 881557/1000000 > 0; B_balance > 91807/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((91807 : Rat)) .lt,
  -- A008.positive_gp; A008: D=6/5, lambda in [1/3,3/5], y in [9/16,3/4], m=49/100: delta > 764244/1000000 > 0; B_balance > 34482/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((764244 : Rat)) .lt,
  -- A008.positive_g; A008: D=6/5, lambda in [1/3,3/5], y in [9/16,3/4], m=49/100: delta > 764244/1000000 > 0; B_balance > 34482/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((34482 : Rat)) .lt,
  -- A009.positive_gp; A009: D=6/5, lambda in [1/3,3/5], y in [3/4,15/16], m=49/100: delta > 707087/1000000 > 0; B_balance > 186431/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((707087 : Rat)) .lt,
  -- A009.positive_g; A009: D=6/5, lambda in [1/3,3/5], y in [3/4,15/16], m=49/100: delta > 707087/1000000 > 0; B_balance > 186431/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((186431 : Rat)) .lt,
  -- A010.positive_gp; A010: D=6/5, lambda in [1/3,3/5], y in [15/16,9/8], m=49/100: delta > 660453/1000000 > 0; B_balance > 411161/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((660453 : Rat)) .lt,
  -- A010.positive_g; A010: D=6/5, lambda in [1/3,3/5], y in [15/16,9/8], m=49/100: delta > 660453/1000000 > 0; B_balance > 411161/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((411161 : Rat)) .lt,
  -- A011.positive_gp; A011: D=6/5, lambda in [1/3,3/5], y in [9/8,21/16], m=49/100: delta > 637637/1000000 > 0; B_balance > 815835/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((637637 : Rat)) .lt,
  -- A011.positive_g; A011: D=6/5, lambda in [1/3,3/5], y in [9/8,21/16], m=49/100: delta > 637637/1000000 > 0; B_balance > 815835/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((815835 : Rat)) .lt,
  -- A012.positive_gp; A012: D=6/5, lambda in [1/3,3/5], y in [21/16,3/2], m=49/100: delta > 646131/1000000 > 0; B_balance > 1522942/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((646131 : Rat)) .lt,
  -- A012.positive_g; A012: D=6/5, lambda in [1/3,3/5], y in [21/16,3/2], m=49/100: delta > 646131/1000000 > 0; B_balance > 1522942/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((1522942 : Rat)) .lt,
  -- A013.positive_gp; A013: D=6/5, lambda in [1/3,3/5], y in [3/2,15/8], m=49/100: delta > 490783/1000000 > 0; B_balance > 1312916/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((490783 : Rat)) .lt,
  -- A013.positive_g; A013: D=6/5, lambda in [1/3,3/5], y in [3/2,15/8], m=49/100: delta > 490783/1000000 > 0; B_balance > 1312916/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((1312916 : Rat)) .lt,
  -- A014.positive_gp; A014: D=6/5, lambda in [1/3,3/5], y in [15/8,9/4], m=49/100: delta > 746242/1000000 > 0; B_balance > 5916806/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((746242 : Rat)) .lt,
  -- A014.positive_g; A014: D=6/5, lambda in [1/3,3/5], y in [15/8,9/4], m=49/100: delta > 746242/1000000 > 0; B_balance > 5916806/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((5916806 : Rat)) .lt,
  -- A015.positive_gp; A015: D=6/5, lambda in [1/3,3/5], y in [9/4,3], m=49/100: delta > 895931/1000000 > 0; B_balance > 11479831/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((895931 : Rat)) .lt,
  -- A015.positive_g; A015: D=6/5, lambda in [1/3,3/5], y in [9/4,3], m=49/100: delta > 895931/1000000 > 0; B_balance > 11479831/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((11479831 : Rat)) .lt,
  -- A016.positive_gp; A016: D=6/5, lambda in [3/5,7/8], y in [0,3/16], m=1/3: delta > 970364/1000000 > 0; B_balance > 111405/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((970364 : Rat)) .lt,
  -- A016.positive_g; A016: D=6/5, lambda in [3/5,7/8], y in [0,3/16], m=1/3: delta > 970364/1000000 > 0; B_balance > 111405/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((111405 : Rat)) .lt,
  -- A017.positive_gp; A017: D=6/5, lambda in [3/5,7/8], y in [3/16,9/32], m=1/3: delta > 958963/1000000 > 0; B_balance > 30673/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((958963 : Rat)) .lt,
  -- A017.positive_g; A017: D=6/5, lambda in [3/5,7/8], y in [3/16,9/32], m=1/3: delta > 958963/1000000 > 0; B_balance > 30673/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((30673 : Rat)) .lt,
  -- A018.positive_gp; A018: D=6/5, lambda in [3/5,7/8], y in [9/32,21/64], m=2/5: delta > 956608/1000000 > 0; B_balance > 15362/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((956608 : Rat)) .lt,
  -- A018.positive_g; A018: D=6/5, lambda in [3/5,7/8], y in [9/32,21/64], m=2/5: delta > 956608/1000000 > 0; B_balance > 15362/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((15362 : Rat)) .lt,
  -- A019.positive_gp; A019: D=6/5, lambda in [3/5,7/8], y in [21/64,3/8], m=49/100: delta > 936981/1000000 > 0; B_balance > 13269/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((936981 : Rat)) .lt,
  -- A019.positive_g; A019: D=6/5, lambda in [3/5,7/8], y in [21/64,3/8], m=49/100: delta > 936981/1000000 > 0; B_balance > 13269/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((13269 : Rat)) .lt,
  -- A020.positive_gp; A020: D=6/5, lambda in [3/5,7/8], y in [3/8,27/64], m=49/100: delta > 917480/1000000 > 0; B_balance > 20441/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((917480 : Rat)) .lt,
  -- A020.positive_g; A020: D=6/5, lambda in [3/5,7/8], y in [3/8,27/64], m=49/100: delta > 917480/1000000 > 0; B_balance > 20441/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((20441 : Rat)) .lt,
  -- A021.positive_gp; A021: D=6/5, lambda in [3/5,7/8], y in [27/64,15/32], m=49/100: delta > 898175/1000000 > 0; B_balance > 29334/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((898175 : Rat)) .lt,
  -- A021.positive_g; A021: D=6/5, lambda in [3/5,7/8], y in [27/64,15/32], m=49/100: delta > 898175/1000000 > 0; B_balance > 29334/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((29334 : Rat)) .lt,
  -- A022.positive_gp; A022: D=6/5, lambda in [3/5,7/8], y in [15/32,9/16], m=49/100: delta > 837498/1000000 > 0; B_balance > 11407/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((837498 : Rat)) .lt,
  -- A022.positive_g; A022: D=6/5, lambda in [3/5,7/8], y in [15/32,9/16], m=49/100: delta > 837498/1000000 > 0; B_balance > 11407/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((11407 : Rat)) .lt,
  -- A023.positive_gp; A023: D=6/5, lambda in [3/5,7/8], y in [9/16,21/32], m=49/100: delta > 799230/1000000 > 0; B_balance > 33024/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((799230 : Rat)) .lt,
  -- A023.positive_g; A023: D=6/5, lambda in [3/5,7/8], y in [9/16,21/32], m=49/100: delta > 799230/1000000 > 0; B_balance > 33024/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((33024 : Rat)) .lt,
  -- A024.positive_gp; A024: D=6/5, lambda in [3/5,7/8], y in [21/32,3/4], m=49/100: delta > 763114/1000000 > 0; B_balance > 63330/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((763114 : Rat)) .lt,
  -- A024.positive_g; A024: D=6/5, lambda in [3/5,7/8], y in [21/32,3/4], m=49/100: delta > 763114/1000000 > 0; B_balance > 63330/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((63330 : Rat)) .lt,
  -- A025.positive_gp; A025: D=6/5, lambda in [3/5,7/8], y in [3/4,27/32], m=49/100: delta > 729834/1000000 > 0; B_balance > 104635/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((729834 : Rat)) .lt,
  -- A025.positive_g; A025: D=6/5, lambda in [3/5,7/8], y in [3/4,27/32], m=49/100: delta > 729834/1000000 > 0; B_balance > 104635/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((104635 : Rat)) .lt,
  -- A026.positive_gp; A026: D=6/5, lambda in [3/5,7/8], y in [27/32,15/16], m=49/100: delta > 700115/1000000 > 0; B_balance > 160183/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((700115 : Rat)) .lt,
  -- A026.positive_g; A026: D=6/5, lambda in [3/5,7/8], y in [27/32,15/16], m=49/100: delta > 700115/1000000 > 0; B_balance > 160183/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((160183 : Rat)) .lt,
  -- A027.positive_gp; A027: D=6/5, lambda in [3/5,7/8], y in [15/16,9/8], m=49/100: delta > 575004/1000000 > 0; B_balance > 2898/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((575004 : Rat)) .lt,
  -- A027.positive_g; A027: D=6/5, lambda in [3/5,7/8], y in [15/16,9/8], m=49/100: delta > 575004/1000000 > 0; B_balance > 2898/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((2898 : Rat)) .lt,
  -- A028.positive_gp; A028: D=6/5, lambda in [3/5,7/8], y in [9/8,21/16], m=49/100: delta > 527502/1000000 > 0; B_balance > 88839/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((527502 : Rat)) .lt,
  -- A028.positive_g; A028: D=6/5, lambda in [3/5,7/8], y in [9/8,21/16], m=49/100: delta > 527502/1000000 > 0; B_balance > 88839/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((88839 : Rat)) .lt,
  -- A029.positive_gp; A029: D=6/5, lambda in [3/5,7/8], y in [21/16,3/2], m=49/100: delta > 506285/1000000 > 0; B_balance > 319408/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((506285 : Rat)) .lt,
  -- A029.positive_g; A029: D=6/5, lambda in [3/5,7/8], y in [21/16,3/2], m=49/100: delta > 506285/1000000 > 0; B_balance > 319408/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((319408 : Rat)) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 64 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.PositiveOutput002
