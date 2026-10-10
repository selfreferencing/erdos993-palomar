module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Normalization001

def records : List Comparison := [
  -- E001.normalization; E001: 10479909/10000000 < E_minus(3/64); E_plus(3/64) < 10479912/10000000.
  Comparison.ofRats ((1 : Rat)) (e001.lo) .le,
  -- E002.normalization; E002: 10982850/10000000 < E_minus(3/32); E_plus(3/32) < 10982853/10000000.
  Comparison.ofRats ((1 : Rat)) (e002.lo) .le,
  -- E003.normalization; E003: 11509928/10000000 < E_minus(9/64); E_plus(9/64) < 11509931/10000000.
  Comparison.ofRats ((1 : Rat)) (e003.lo) .le,
  -- E004.normalization; E004: 12062301/10000000 < E_minus(3/16); E_plus(3/16) < 12062304/10000000.
  Comparison.ofRats ((1 : Rat)) (e004.lo) .le,
  -- E005.normalization; E005: 12348350/10000000 < E_minus(27/128); E_plus(27/128) < 12348353/10000000.
  Comparison.ofRats ((1 : Rat)) (e005.lo) .le,
  -- E006.normalization; E006: 12641183/10000000 < E_minus(15/64); E_plus(15/64) < 12641186/10000000.
  Comparison.ofRats ((1 : Rat)) (e006.lo) .le,
  -- E007.normalization; E007: 12940960/10000000 < E_minus(33/128); E_plus(33/128) < 12940963/10000000.
  Comparison.ofRats ((1 : Rat)) (e007.lo) .le,
  -- E008.normalization; E008: 13247846/10000000 < E_minus(9/32); E_plus(9/32) < 13247849/10000000.
  Comparison.ofRats ((1 : Rat)) (e008.lo) .le,
  -- E009.normalization; E009: 13532375/10000000 < E_minus(121/400); E_plus(121/400) < 13532378/10000000.
  Comparison.ofRats ((1 : Rat)) (e009.lo) .le,
  -- E010.normalization; E010: 13562010/10000000 < E_minus(39/128); E_plus(39/128) < 13562013/10000000.
  Comparison.ofRats ((1 : Rat)) (e010.lo) .le,
  -- E011.normalization; E011: 13883624/10000000 < E_minus(21/64); E_plus(21/64) < 13883627/10000000.
  Comparison.ofRats ((1 : Rat)) (e011.lo) .le,
  -- E012.normalization; E012: 14212864/10000000 < E_minus(45/128); E_plus(45/128) < 14212867/10000000.
  Comparison.ofRats ((1 : Rat)) (e012.lo) .le,
  -- E013.normalization; E013: 14549913/10000000 < E_minus(3/8); E_plus(3/8) < 14549916/10000000.
  Comparison.ofRats ((1 : Rat)) (e013.lo) .le,
  -- E014.normalization; E014: 14894954/10000000 < E_minus(51/128); E_plus(51/128) < 14894957/10000000.
  Comparison.ofRats ((1 : Rat)) (e014.lo) .le,
  -- E015.normalization; E015: 15219614/10000000 < E_minus(21/50); E_plus(21/50) < 15219617/10000000.
  Comparison.ofRats ((1 : Rat)) (e015.lo) .le,
  -- E016.normalization; E016: 15248178/10000000 < E_minus(27/64); E_plus(27/64) < 15248181/10000000.
  Comparison.ofRats ((1 : Rat)) (e016.lo) .le,
  -- E017.normalization; E017: 15609778/10000000 < E_minus(57/128); E_plus(57/128) < 15609781/10000000.
  Comparison.ofRats ((1 : Rat)) (e017.lo) .le,
  -- E018.normalization; E018: 15840738/10000000 < E_minus(23/50); E_plus(23/50) < 15840741/10000000.
  Comparison.ofRats ((1 : Rat)) (e018.lo) .le,
  -- E019.normalization; E019: 15979953/10000000 < E_minus(15/32); E_plus(15/32) < 15979956/10000000.
  Comparison.ofRats ((1 : Rat)) (e019.lo) .le,
  -- E020.normalization; E020: 16168320/10000000 < E_minus(123/256); E_plus(123/256) < 16168323/10000000.
  Comparison.ofRats ((1 : Rat)) (e020.lo) .le,
  -- E021.normalization; E021: 16358907/10000000 < E_minus(63/128); E_plus(63/128) < 16358910/10000000.
  Comparison.ofRats ((1 : Rat)) (e021.lo) .le,
  -- E022.normalization; E022: 16551740/10000000 < E_minus(129/256); E_plus(129/256) < 16551743/10000000.
  Comparison.ofRats ((1 : Rat)) (e022.lo) .le,
  -- E023.normalization; E023: 16652910/10000000 < E_minus(51/100); E_plus(51/100) < 16652913/10000000.
  Comparison.ofRats ((1 : Rat)) (e023.lo) .le,
  -- E024.normalization; E024: 16746847/10000000 < E_minus(33/64); E_plus(33/64) < 16746850/10000000.
  Comparison.ofRats ((1 : Rat)) (e024.lo) .le,
  -- E025.normalization; E025: 16944254/10000000 < E_minus(135/256); E_plus(135/256) < 16944257/10000000.
  Comparison.ofRats ((1 : Rat)) (e025.lo) .le,
  -- E026.normalization; E026: 17143987/10000000 < E_minus(69/128); E_plus(69/128) < 17143990/10000000.
  Comparison.ofRats ((1 : Rat)) (e026.lo) .le,
  -- E027.normalization; E027: 17332529/10000000 < E_minus(11/20); E_plus(11/20) < 17332532/10000000.
  Comparison.ofRats ((1 : Rat)) (e027.lo) .le,
  -- E028.normalization; E028: 17346075/10000000 < E_minus(141/256); E_plus(141/256) < 17346078/10000000.
  Comparison.ofRats ((1 : Rat)) (e028.lo) .le,
  -- E029.normalization; E029: 17550545/10000000 < E_minus(9/16); E_plus(9/16) < 17550548/10000000.
  Comparison.ofRats ((1 : Rat)) (e029.lo) .le,
  -- E030.normalization; E030: 17757425/10000000 < E_minus(147/256); E_plus(147/256) < 17757428/10000000.
  Comparison.ofRats ((1 : Rat)) (e030.lo) .le,
  -- E031.normalization; E031: 17966744/10000000 < E_minus(75/128); E_plus(75/128) < 17966747/10000000.
  Comparison.ofRats ((1 : Rat)) (e031.lo) .le,
  -- E032.normalization; E032: 18178531/10000000 < E_minus(153/256); E_plus(153/256) < 18178534/10000000.
  Comparison.ofRats ((1 : Rat)) (e032.lo) .le,
  -- E033.normalization; E033: 18312521/10000000 < E_minus(121/200); E_plus(121/200) < 18312524/10000000.
  Comparison.ofRats ((1 : Rat)) (e033.lo) .le,
  -- E034.normalization; E034: 18392813/10000000 < E_minus(39/64); E_plus(39/64) < 18392816/10000000.
  Comparison.ofRats ((1 : Rat)) (e034.lo) .le,
  -- E035.normalization; E035: 18609622/10000000 < E_minus(159/256); E_plus(159/256) < 18609625/10000000.
  Comparison.ofRats ((1 : Rat)) (e035.lo) .le,
  -- E036.normalization; E036: 18776104/10000000 < E_minus(63/100); E_plus(63/100) < 18776107/10000000.
  Comparison.ofRats ((1 : Rat)) (e036.lo) .le,
  -- E037.normalization; E037: 18828986/10000000 < E_minus(81/128); E_plus(81/128) < 18828989/10000000.
  Comparison.ofRats ((1 : Rat)) (e037.lo) .le,
  -- E038.normalization; E038: 18917454/10000000 < E_minus(51/80); E_plus(51/80) < 18917457/10000000.
  Comparison.ofRats ((1 : Rat)) (e038.lo) .le,
  -- E039.normalization; E039: 19050937/10000000 < E_minus(165/256); E_plus(165/256) < 19050940/10000000.
  Comparison.ofRats ((1 : Rat)) (e039.lo) .le,
  -- E040.normalization; E040: 19275503/10000000 < E_minus(21/32); E_plus(21/32) < 19275506/10000000.
  Comparison.ofRats ((1 : Rat)) (e040.lo) .le,
  -- E041.normalization; E041: 19502717/10000000 < E_minus(171/256); E_plus(171/256) < 19502720/10000000.
  Comparison.ofRats ((1 : Rat)) (e041.lo) .le,
  -- E042.normalization; E042: 19732608/10000000 < E_minus(87/128); E_plus(87/128) < 19732611/10000000.
  Comparison.ofRats ((1 : Rat)) (e042.lo) .le,
  -- E043.normalization; E043: 19788185/10000000 < E_minus(273/400); E_plus(273/400) < 19788188/10000000.
  Comparison.ofRats ((1 : Rat)) (e043.lo) .le,
  -- E044.normalization; E044: 19887373/10000000 < E_minus(11/16); E_plus(11/16) < 19887376/10000000.
  Comparison.ofRats ((1 : Rat)) (e044.lo) .le,
  -- E045.normalization; E045: 19937154/10000000 < E_minus(69/100); E_plus(69/100) < 19937157/10000000.
  Comparison.ofRats ((1 : Rat)) (e045.lo) .le,
  -- E046.normalization; E046: 19965210/10000000 < E_minus(177/256); E_plus(177/256) < 19965213/10000000.
  Comparison.ofRats ((1 : Rat)) (e046.lo) .le,
  -- E047.normalization; E047: 20200554/10000000 < E_minus(45/64); E_plus(45/64) < 20200557/10000000.
  Comparison.ofRats ((1 : Rat)) (e047.lo) .le,
  -- E048.normalization; E048: 20438672/10000000 < E_minus(183/256); E_plus(183/256) < 20438675/10000000.
  Comparison.ofRats ((1 : Rat)) (e048.lo) .le,
  -- E049.normalization; E049: 20679596/10000000 < E_minus(93/128); E_plus(93/128) < 20679599/10000000.
  Comparison.ofRats ((1 : Rat)) (e049.lo) .le,
  -- E050.normalization; E050: 20854818/10000000 < E_minus(147/200); E_plus(147/200) < 20854821/10000000.
  Comparison.ofRats ((1 : Rat)) (e050.lo) .le,
  -- E051.normalization; E051: 20923361/10000000 < E_minus(189/256); E_plus(189/256) < 20923364/10000000.
  Comparison.ofRats ((1 : Rat)) (e051.lo) .le,
  -- E052.normalization; E052: 21117140/10000000 < E_minus(299/400); E_plus(299/400) < 21117143/10000000.
  Comparison.ofRats ((1 : Rat)) (e052.lo) .le,
  -- E053.normalization; E053: 21169999/10000000 < E_minus(3/4); E_plus(3/4) < 21170002/10000000.
  Comparison.ofRats ((1 : Rat)) (e053.lo) .le,
  -- E054.normalization; E054: 21302726/10000000 < E_minus(121/160); E_plus(121/160) < 21302729/10000000.
  Comparison.ofRats ((1 : Rat)) (e054.lo) .le,
  -- E055.normalization; E055: 21419544/10000000 < E_minus(195/256); E_plus(195/256) < 21419547/10000000.
  Comparison.ofRats ((1 : Rat)) (e055.lo) .le,
  -- E056.normalization; E056: 21489942/10000000 < E_minus(153/200); E_plus(153/200) < 21489945/10000000.
  Comparison.ofRats ((1 : Rat)) (e056.lo) .le,
  -- E057.normalization; E057: 21672031/10000000 < E_minus(99/128); E_plus(99/128) < 21672034/10000000.
  Comparison.ofRats ((1 : Rat)) (e057.lo) .le,
  -- E058.normalization; E058: 21927494/10000000 < E_minus(201/256); E_plus(201/256) < 21927497/10000000.
  Comparison.ofRats ((1 : Rat)) (e058.lo) .le,
  -- E059.normalization; E059: 21978947/10000000 < E_minus(63/80); E_plus(63/80) < 21978950/10000000.
  Comparison.ofRats ((1 : Rat)) (e059.lo) .le,
  -- E060.normalization; E060: 22123658/10000000 < E_minus(2541/3200); E_plus(2541/3200) < 22123661/10000000.
  Comparison.ofRats ((1 : Rat)) (e060.lo) .le,
  -- E061.normalization; E061: 22185968/10000000 < E_minus(51/64); E_plus(51/64) < 22185971/10000000.
  Comparison.ofRats ((1 : Rat)) (e061.lo) .le,
  -- E062.normalization; E062: 22366963/10000000 < E_minus(161/200); E_plus(161/200) < 22366967/10000000.
  Comparison.ofRats ((1 : Rat)) (e062.lo) .le,
  -- E063.normalization; E063: 22447489/10000000 < E_minus(207/256); E_plus(207/256) < 22447492/10000000.
  Comparison.ofRats ((1 : Rat)) (e063.lo) .le,
  -- E064.normalization; E064: 22545912/10000000 < E_minus(5203/6400); E_plus(5203/6400) < 22545915/10000000.
  Comparison.ofRats ((1 : Rat)) (e064.lo) .le
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 64 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Normalization001
