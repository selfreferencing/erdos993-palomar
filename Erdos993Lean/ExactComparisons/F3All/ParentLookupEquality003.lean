module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality003

def records : List Comparison := [
  -- P033.lower.lambda; P033: lambda=3/5, y=15/8: 880226/10000000 < L_minus(1+(3/5)/(32604103/5000000)); L_plus(1+(3/5)/(6520819/1000000)) < 880229/10000000.
  Comparison.ofRats (((3 : Rat) / (5 : Rat))) (p033.lam) .eq,
  -- P033.lower.exp; P033: lambda=3/5, y=15/8: 880226/10000000 < L_minus(1+(3/5)/(32604103/5000000)); L_plus(1+(3/5)/(6520819/1000000)) < 880229/10000000.
  Comparison.ofRats (((32604103 : Rat) / (5000000 : Rat))) (e130.hi) .eq,
  -- P033.upper.lambda; P033: lambda=3/5, y=15/8: 880226/10000000 < L_minus(1+(3/5)/(32604103/5000000)); L_plus(1+(3/5)/(6520819/1000000)) < 880229/10000000.
  Comparison.ofRats (((3 : Rat) / (5 : Rat))) (p033.lam) .eq,
  -- P033.upper.exp; P033: lambda=3/5, y=15/8: 880226/10000000 < L_minus(1+(3/5)/(32604103/5000000)); L_plus(1+(3/5)/(6520819/1000000)) < 880229/10000000.
  Comparison.ofRats (((6520819 : Rat) / (1000000 : Rat))) (e130.lo) .eq,
  -- P034.lower.lambda; P034: lambda=3/5, y=9/4: 613202/10000000 < L_minus(1+(3/5)/(23719357/2500000)); L_plus(1+(3/5)/(94877357/10000000)) < 613206/10000000.
  Comparison.ofRats (((3 : Rat) / (5 : Rat))) (p034.lam) .eq,
  -- P034.lower.exp; P034: lambda=3/5, y=9/4: 613202/10000000 < L_minus(1+(3/5)/(23719357/2500000)); L_plus(1+(3/5)/(94877357/10000000)) < 613206/10000000.
  Comparison.ofRats (((23719357 : Rat) / (2500000 : Rat))) (e136.hi) .eq,
  -- P034.upper.lambda; P034: lambda=3/5, y=9/4: 613202/10000000 < L_minus(1+(3/5)/(23719357/2500000)); L_plus(1+(3/5)/(94877357/10000000)) < 613206/10000000.
  Comparison.ofRats (((3 : Rat) / (5 : Rat))) (p034.lam) .eq,
  -- P034.upper.exp; P034: lambda=3/5, y=9/4: 613202/10000000 < L_minus(1+(3/5)/(23719357/2500000)); L_plus(1+(3/5)/(94877357/10000000)) < 613206/10000000.
  Comparison.ofRats (((94877357 : Rat) / (10000000 : Rat))) (e136.lo) .eq,
  -- P035.lower.lambda; P035: lambda=3/5, y=3: 294344/10000000 < L_minus(1+(3/5)/(100428229/5000000)); L_plus(1+(3/5)/(40171073/2000000)) < 294349/10000000.
  Comparison.ofRats (((3 : Rat) / (5 : Rat))) (p035.lam) .eq,
  -- P035.lower.exp; P035: lambda=3/5, y=3: 294344/10000000 < L_minus(1+(3/5)/(100428229/5000000)); L_plus(1+(3/5)/(40171073/2000000)) < 294349/10000000.
  Comparison.ofRats (((100428229 : Rat) / (5000000 : Rat))) (e140.hi) .eq,
  -- P035.upper.lambda; P035: lambda=3/5, y=3: 294344/10000000 < L_minus(1+(3/5)/(100428229/5000000)); L_plus(1+(3/5)/(40171073/2000000)) < 294349/10000000.
  Comparison.ofRats (((3 : Rat) / (5 : Rat))) (p035.lam) .eq,
  -- P035.upper.exp; P035: lambda=3/5, y=3: 294344/10000000 < L_minus(1+(3/5)/(100428229/5000000)); L_plus(1+(3/5)/(40171073/2000000)) < 294349/10000000.
  Comparison.ofRats (((40171073 : Rat) / (2000000 : Rat))) (e140.lo) .eq,
  -- P036.lower.lambda; P036: lambda=7/8, y=3/16: 5454589/10000000 < L_minus(1+(7/8)/(376947/312500)); L_plus(1+(7/8)/(12062301/10000000)) < 5454595/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p036.lam) .eq,
  -- P036.lower.exp; P036: lambda=7/8, y=3/16: 5454589/10000000 < L_minus(1+(7/8)/(376947/312500)); L_plus(1+(7/8)/(12062301/10000000)) < 5454595/10000000.
  Comparison.ofRats (((376947 : Rat) / (312500 : Rat))) (e004.hi) .eq,
  -- P036.upper.lambda; P036: lambda=7/8, y=3/16: 5454589/10000000 < L_minus(1+(7/8)/(376947/312500)); L_plus(1+(7/8)/(12062301/10000000)) < 5454595/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p036.lam) .eq,
  -- P036.upper.exp; P036: lambda=7/8, y=3/16: 5454589/10000000 < L_minus(1+(7/8)/(376947/312500)); L_plus(1+(7/8)/(12062301/10000000)) < 5454595/10000000.
  Comparison.ofRats (((12062301 : Rat) / (10000000 : Rat))) (e004.lo) .eq,
  -- P037.lower.lambda; P037: lambda=7/8, y=9/32: 5071092/10000000 < L_minus(1+(7/8)/(13247849/10000000)); L_plus(1+(7/8)/(6623923/5000000)) < 5071098/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p037.lam) .eq,
  -- P037.lower.exp; P037: lambda=7/8, y=9/32: 5071092/10000000 < L_minus(1+(7/8)/(13247849/10000000)); L_plus(1+(7/8)/(6623923/5000000)) < 5071098/10000000.
  Comparison.ofRats (((13247849 : Rat) / (10000000 : Rat))) (e008.hi) .eq,
  -- P037.upper.lambda; P037: lambda=7/8, y=9/32: 5071092/10000000 < L_minus(1+(7/8)/(13247849/10000000)); L_plus(1+(7/8)/(6623923/5000000)) < 5071098/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p037.lam) .eq,
  -- P037.upper.exp; P037: lambda=7/8, y=9/32: 5071092/10000000 < L_minus(1+(7/8)/(13247849/10000000)); L_plus(1+(7/8)/(6623923/5000000)) < 5071098/10000000.
  Comparison.ofRats (((6623923 : Rat) / (5000000 : Rat))) (e008.lo) .eq,
  -- P038.lower.lambda; P038: lambda=7/8, y=21/64: 4887262/10000000 < L_minus(1+(7/8)/(13883627/10000000)); L_plus(1+(7/8)/(1735453/1250000)) < 4887268/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p038.lam) .eq,
  -- P038.lower.exp; P038: lambda=7/8, y=21/64: 4887262/10000000 < L_minus(1+(7/8)/(13883627/10000000)); L_plus(1+(7/8)/(1735453/1250000)) < 4887268/10000000.
  Comparison.ofRats (((13883627 : Rat) / (10000000 : Rat))) (e011.hi) .eq,
  -- P038.upper.lambda; P038: lambda=7/8, y=21/64: 4887262/10000000 < L_minus(1+(7/8)/(13883627/10000000)); L_plus(1+(7/8)/(1735453/1250000)) < 4887268/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p038.lam) .eq,
  -- P038.upper.exp; P038: lambda=7/8, y=21/64: 4887262/10000000 < L_minus(1+(7/8)/(13883627/10000000)); L_plus(1+(7/8)/(1735453/1250000)) < 4887268/10000000.
  Comparison.ofRats (((1735453 : Rat) / (1250000 : Rat))) (e011.lo) .eq,
  -- P039.lower.lambda; P039: lambda=7/8, y=3/8: 4708643/10000000 < L_minus(1+(7/8)/(3637479/2500000)); L_plus(1+(7/8)/(14549913/10000000)) < 4708649/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p039.lam) .eq,
  -- P039.lower.exp; P039: lambda=7/8, y=3/8: 4708643/10000000 < L_minus(1+(7/8)/(3637479/2500000)); L_plus(1+(7/8)/(14549913/10000000)) < 4708649/10000000.
  Comparison.ofRats (((3637479 : Rat) / (2500000 : Rat))) (e013.hi) .eq,
  -- P039.upper.lambda; P039: lambda=7/8, y=3/8: 4708643/10000000 < L_minus(1+(7/8)/(3637479/2500000)); L_plus(1+(7/8)/(14549913/10000000)) < 4708649/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p039.lam) .eq,
  -- P039.upper.exp; P039: lambda=7/8, y=3/8: 4708643/10000000 < L_minus(1+(7/8)/(3637479/2500000)); L_plus(1+(7/8)/(14549913/10000000)) < 4708649/10000000.
  Comparison.ofRats (((14549913 : Rat) / (10000000 : Rat))) (e013.lo) .eq,
  -- P040.lower.lambda; P040: lambda=7/8, y=27/64: 4535176/10000000 < L_minus(1+(7/8)/(15248181/10000000)); L_plus(1+(7/8)/(7624089/5000000)) < 4535181/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p040.lam) .eq,
  -- P040.lower.exp; P040: lambda=7/8, y=27/64: 4535176/10000000 < L_minus(1+(7/8)/(15248181/10000000)); L_plus(1+(7/8)/(7624089/5000000)) < 4535181/10000000.
  Comparison.ofRats (((15248181 : Rat) / (10000000 : Rat))) (e016.hi) .eq,
  -- P040.upper.lambda; P040: lambda=7/8, y=27/64: 4535176/10000000 < L_minus(1+(7/8)/(15248181/10000000)); L_plus(1+(7/8)/(7624089/5000000)) < 4535181/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p040.lam) .eq,
  -- P040.upper.exp; P040: lambda=7/8, y=27/64: 4535176/10000000 < L_minus(1+(7/8)/(15248181/10000000)); L_plus(1+(7/8)/(7624089/5000000)) < 4535181/10000000.
  Comparison.ofRats (((7624089 : Rat) / (5000000 : Rat))) (e016.lo) .eq,
  -- P041.lower.lambda; P041: lambda=7/8, y=15/32: 4366799/10000000 < L_minus(1+(7/8)/(3994989/2500000)); L_plus(1+(7/8)/(15979953/10000000)) < 4366804/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p041.lam) .eq,
  -- P041.lower.exp; P041: lambda=7/8, y=15/32: 4366799/10000000 < L_minus(1+(7/8)/(3994989/2500000)); L_plus(1+(7/8)/(15979953/10000000)) < 4366804/10000000.
  Comparison.ofRats (((3994989 : Rat) / (2500000 : Rat))) (e019.hi) .eq,
  -- P041.upper.lambda; P041: lambda=7/8, y=15/32: 4366799/10000000 < L_minus(1+(7/8)/(3994989/2500000)); L_plus(1+(7/8)/(15979953/10000000)) < 4366804/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p041.lam) .eq,
  -- P041.upper.exp; P041: lambda=7/8, y=15/32: 4366799/10000000 < L_minus(1+(7/8)/(3994989/2500000)); L_plus(1+(7/8)/(15979953/10000000)) < 4366804/10000000.
  Comparison.ofRats (((15979953 : Rat) / (10000000 : Rat))) (e019.lo) .eq,
  -- P042.lower.lambda; P042: lambda=7/8, y=33/64: 4203445/10000000 < L_minus(1+(7/8)/(334937/200000)); L_plus(1+(7/8)/(16746847/10000000)) < 4203450/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p042.lam) .eq,
  -- P042.lower.exp; P042: lambda=7/8, y=33/64: 4203445/10000000 < L_minus(1+(7/8)/(334937/200000)); L_plus(1+(7/8)/(16746847/10000000)) < 4203450/10000000.
  Comparison.ofRats (((334937 : Rat) / (200000 : Rat))) (e024.hi) .eq,
  -- P042.upper.lambda; P042: lambda=7/8, y=33/64: 4203445/10000000 < L_minus(1+(7/8)/(334937/200000)); L_plus(1+(7/8)/(16746847/10000000)) < 4203450/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p042.lam) .eq,
  -- P042.upper.exp; P042: lambda=7/8, y=33/64: 4203445/10000000 < L_minus(1+(7/8)/(334937/200000)); L_plus(1+(7/8)/(16746847/10000000)) < 4203450/10000000.
  Comparison.ofRats (((16746847 : Rat) / (10000000 : Rat))) (e024.lo) .eq,
  -- P043.lower.lambda; P043: lambda=7/8, y=9/16: 4045043/10000000 < L_minus(1+(7/8)/(4387637/2500000)); L_plus(1+(7/8)/(3510109/2000000)) < 4045049/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p043.lam) .eq,
  -- P043.lower.exp; P043: lambda=7/8, y=9/16: 4045043/10000000 < L_minus(1+(7/8)/(4387637/2500000)); L_plus(1+(7/8)/(3510109/2000000)) < 4045049/10000000.
  Comparison.ofRats (((4387637 : Rat) / (2500000 : Rat))) (e029.hi) .eq,
  -- P043.upper.lambda; P043: lambda=7/8, y=9/16: 4045043/10000000 < L_minus(1+(7/8)/(4387637/2500000)); L_plus(1+(7/8)/(3510109/2000000)) < 4045049/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p043.lam) .eq,
  -- P043.upper.exp; P043: lambda=7/8, y=9/16: 4045043/10000000 < L_minus(1+(7/8)/(4387637/2500000)); L_plus(1+(7/8)/(3510109/2000000)) < 4045049/10000000.
  Comparison.ofRats (((3510109 : Rat) / (2000000 : Rat))) (e029.lo) .eq,
  -- P044.lower.lambda; P044: lambda=7/8, y=39/64: 3891519/10000000 < L_minus(1+(7/8)/(1149551/625000)); L_plus(1+(7/8)/(18392813/10000000)) < 3891525/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p044.lam) .eq,
  -- P044.lower.exp; P044: lambda=7/8, y=39/64: 3891519/10000000 < L_minus(1+(7/8)/(1149551/625000)); L_plus(1+(7/8)/(18392813/10000000)) < 3891525/10000000.
  Comparison.ofRats (((1149551 : Rat) / (625000 : Rat))) (e034.hi) .eq,
  -- P044.upper.lambda; P044: lambda=7/8, y=39/64: 3891519/10000000 < L_minus(1+(7/8)/(1149551/625000)); L_plus(1+(7/8)/(18392813/10000000)) < 3891525/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p044.lam) .eq,
  -- P044.upper.exp; P044: lambda=7/8, y=39/64: 3891519/10000000 < L_minus(1+(7/8)/(1149551/625000)); L_plus(1+(7/8)/(18392813/10000000)) < 3891525/10000000.
  Comparison.ofRats (((18392813 : Rat) / (10000000 : Rat))) (e034.lo) .eq,
  -- P045.lower.lambda; P045: lambda=7/8, y=21/32: 3742795/10000000 < L_minus(1+(7/8)/(9637753/5000000)); L_plus(1+(7/8)/(19275503/10000000)) < 3742801/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p045.lam) .eq,
  -- P045.lower.exp; P045: lambda=7/8, y=21/32: 3742795/10000000 < L_minus(1+(7/8)/(9637753/5000000)); L_plus(1+(7/8)/(19275503/10000000)) < 3742801/10000000.
  Comparison.ofRats (((9637753 : Rat) / (5000000 : Rat))) (e040.hi) .eq,
  -- P045.upper.lambda; P045: lambda=7/8, y=21/32: 3742795/10000000 < L_minus(1+(7/8)/(9637753/5000000)); L_plus(1+(7/8)/(19275503/10000000)) < 3742801/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p045.lam) .eq,
  -- P045.upper.exp; P045: lambda=7/8, y=21/32: 3742795/10000000 < L_minus(1+(7/8)/(9637753/5000000)); L_plus(1+(7/8)/(19275503/10000000)) < 3742801/10000000.
  Comparison.ofRats (((19275503 : Rat) / (10000000 : Rat))) (e040.lo) .eq,
  -- P046.lower.lambda; P046: lambda=7/8, y=45/64: 3598790/10000000 < L_minus(1+(7/8)/(20200557/10000000)); L_plus(1+(7/8)/(10100277/5000000)) < 3598795/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p046.lam) .eq,
  -- P046.lower.exp; P046: lambda=7/8, y=45/64: 3598790/10000000 < L_minus(1+(7/8)/(20200557/10000000)); L_plus(1+(7/8)/(10100277/5000000)) < 3598795/10000000.
  Comparison.ofRats (((20200557 : Rat) / (10000000 : Rat))) (e047.hi) .eq,
  -- P046.upper.lambda; P046: lambda=7/8, y=45/64: 3598790/10000000 < L_minus(1+(7/8)/(20200557/10000000)); L_plus(1+(7/8)/(10100277/5000000)) < 3598795/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p046.lam) .eq,
  -- P046.upper.exp; P046: lambda=7/8, y=45/64: 3598790/10000000 < L_minus(1+(7/8)/(20200557/10000000)); L_plus(1+(7/8)/(10100277/5000000)) < 3598795/10000000.
  Comparison.ofRats (((10100277 : Rat) / (5000000 : Rat))) (e047.lo) .eq,
  -- P047.lower.lambda; P047: lambda=7/8, y=3/4: 3459417/10000000 < L_minus(1+(7/8)/(10585001/5000000)); L_plus(1+(7/8)/(21169999/10000000)) < 3459423/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p047.lam) .eq,
  -- P047.lower.exp; P047: lambda=7/8, y=3/4: 3459417/10000000 < L_minus(1+(7/8)/(10585001/5000000)); L_plus(1+(7/8)/(21169999/10000000)) < 3459423/10000000.
  Comparison.ofRats (((10585001 : Rat) / (5000000 : Rat))) (e053.hi) .eq,
  -- P047.upper.lambda; P047: lambda=7/8, y=3/4: 3459417/10000000 < L_minus(1+(7/8)/(10585001/5000000)); L_plus(1+(7/8)/(21169999/10000000)) < 3459423/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p047.lam) .eq,
  -- P047.upper.exp; P047: lambda=7/8, y=3/4: 3459417/10000000 < L_minus(1+(7/8)/(10585001/5000000)); L_plus(1+(7/8)/(21169999/10000000)) < 3459423/10000000.
  Comparison.ofRats (((21169999 : Rat) / (10000000 : Rat))) (e053.lo) .eq,
  -- P048.lower.lambda; P048: lambda=7/8, y=51/64: 3324592/10000000 < L_minus(1+(7/8)/(22185971/10000000)); L_plus(1+(7/8)/(1386623/625000)) < 3324597/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p048.lam) .eq,
  -- P048.lower.exp; P048: lambda=7/8, y=51/64: 3324592/10000000 < L_minus(1+(7/8)/(22185971/10000000)); L_plus(1+(7/8)/(1386623/625000)) < 3324597/10000000.
  Comparison.ofRats (((22185971 : Rat) / (10000000 : Rat))) (e061.hi) .eq,
  -- P048.upper.lambda; P048: lambda=7/8, y=51/64: 3324592/10000000 < L_minus(1+(7/8)/(22185971/10000000)); L_plus(1+(7/8)/(1386623/625000)) < 3324597/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p048.lam) .eq,
  -- P048.upper.exp; P048: lambda=7/8, y=51/64: 3324592/10000000 < L_minus(1+(7/8)/(22185971/10000000)); L_plus(1+(7/8)/(1386623/625000)) < 3324597/10000000.
  Comparison.ofRats (((1386623 : Rat) / (625000 : Rat))) (e061.lo) .eq
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 64 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality003
