module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Normalization005

def records : List Comparison := [
  -- P108.normalization; P108: lambda=28/25, y=21/8: 780088/10000000 < L_minus(1+(28/25)/(27609207/2000000)); L_plus(1+(28/25)/(6902287/500000)) < 780093/10000000.
  Comparison.ofRats ((0 : Rat)) (p108.lo) .lt,
  -- P109.normalization; P109: lambda=28/25, y=3: 542619/10000000 < L_minus(1+(28/25)/(100428229/5000000)); L_plus(1+(28/25)/(40171073/2000000)) < 542625/10000000.
  Comparison.ofRats ((0 : Rat)) (p109.lo) .lt,
  -- P110.normalization; P110: lambda=263/200, y=3/8: 6438438/10000000 < L_minus(1+(263/200)/(3637479/2500000)); L_plus(1+(263/200)/(14549913/10000000)) < 6438445/10000000.
  Comparison.ofRats ((0 : Rat)) (p110.lo) .lt,
  -- P111.normalization; P111: lambda=263/200, y=21/50: 6227333/10000000 < L_minus(1+(263/200)/(15219617/10000000)); L_plus(1+(263/200)/(7609807/5000000)) < 6227339/10000000.
  Comparison.ofRats ((0 : Rat)) (p111.lo) .lt,
  -- P112.normalization; P112: lambda=263/200, y=27/64: 6218646/10000000 < L_minus(1+(263/200)/(15248181/10000000)); L_plus(1+(263/200)/(7624089/5000000)) < 6218652/10000000.
  Comparison.ofRats ((0 : Rat)) (p112.lo) .lt,
  -- P113.normalization; P113: lambda=263/200, y=15/32: 6004316/10000000 < L_minus(1+(263/200)/(3994989/2500000)); L_plus(1+(263/200)/(15979953/10000000)) < 6004322/10000000.
  Comparison.ofRats ((0 : Rat)) (p113.lo) .lt,
  -- P114.normalization; P114: lambda=263/200, y=63/128: 5899193/10000000 < L_minus(1+(263/200)/(1635891/1000000)); L_plus(1+(263/200)/(16358907/10000000)) < 5899199/10000000.
  Comparison.ofRats ((0 : Rat)) (p114.lo) .lt,
  -- P115.normalization; P115: lambda=263/200, y=33/64: 5795427/10000000 < L_minus(1+(263/200)/(334937/200000)); L_plus(1+(263/200)/(16746847/10000000)) < 5795433/10000000.
  Comparison.ofRats ((0 : Rat)) (p115.lo) .lt,
  -- P116.normalization; P116: lambda=263/200, y=69/128: 5693014/10000000 < L_minus(1+(263/200)/(1714399/1000000)); L_plus(1+(263/200)/(17143987/10000000)) < 5693020/10000000.
  Comparison.ofRats ((0 : Rat)) (p116.lo) .lt,
  -- P117.normalization; P117: lambda=263/200, y=9/16: 5591951/10000000 < L_minus(1+(263/200)/(4387637/2500000)); L_plus(1+(263/200)/(3510109/2000000)) < 5591956/10000000.
  Comparison.ofRats ((0 : Rat)) (p117.lo) .lt,
  -- P118.normalization; P118: lambda=263/200, y=75/128: 5492232/10000000 < L_minus(1+(263/200)/(17966747/10000000)); L_plus(1+(263/200)/(2245843/1250000)) < 5492238/10000000.
  Comparison.ofRats ((0 : Rat)) (p118.lo) .lt,
  -- P119.normalization; P119: lambda=263/200, y=39/64: 5393854/10000000 < L_minus(1+(263/200)/(1149551/625000)); L_plus(1+(263/200)/(18392813/10000000)) < 5393860/10000000.
  Comparison.ofRats ((0 : Rat)) (p119.lo) .lt,
  -- P120.normalization; P120: lambda=263/200, y=63/100: 5308387/10000000 < L_minus(1+(263/200)/(18776107/10000000)); L_plus(1+(263/200)/(2347013/1250000)) < 5308392/10000000.
  Comparison.ofRats ((0 : Rat)) (p120.lo) .lt,
  -- P121.normalization; P121: lambda=263/200, y=81/128: 5296812/10000000 < L_minus(1+(263/200)/(18828989/10000000)); L_plus(1+(263/200)/(9414493/5000000)) < 5296818/10000000.
  Comparison.ofRats ((0 : Rat)) (p121.lo) .lt,
  -- P122.normalization; P122: lambda=263/200, y=21/32: 5201099/10000000 < L_minus(1+(263/200)/(9637753/5000000)); L_plus(1+(263/200)/(19275503/10000000)) < 5201105/10000000.
  Comparison.ofRats ((0 : Rat)) (p122.lo) .lt,
  -- P123.normalization; P123: lambda=263/200, y=87/128: 5106711/10000000 < L_minus(1+(263/200)/(19732611/10000000)); L_plus(1+(263/200)/(154161/78125)) < 5106716/10000000.
  Comparison.ofRats ((0 : Rat)) (p123.lo) .lt,
  -- P124.normalization; P124: lambda=263/200, y=273/400: 5095473/10000000 < L_minus(1+(263/200)/(4947047/2500000)); L_plus(1+(263/200)/(3957637/2000000)) < 5095478/10000000.
  Comparison.ofRats ((0 : Rat)) (p124.lo) .lt,
  -- P125.normalization; P125: lambda=263/200, y=45/64: 5013640/10000000 < L_minus(1+(263/200)/(20200557/10000000)); L_plus(1+(263/200)/(10100277/5000000)) < 5013646/10000000.
  Comparison.ofRats ((0 : Rat)) (p125.lo) .lt,
  -- P126.normalization; P126: lambda=263/200, y=93/128: 4921882/10000000 < L_minus(1+(263/200)/(20679599/10000000)); L_plus(1+(263/200)/(5169899/2500000)) < 4921888/10000000.
  Comparison.ofRats ((0 : Rat)) (p126.lo) .lt,
  -- P127.normalization; P127: lambda=263/200, y=147/200: 4889169/10000000 < L_minus(1+(263/200)/(20854821/10000000)); L_plus(1+(263/200)/(10427409/5000000)) < 4889175/10000000.
  Comparison.ofRats ((0 : Rat)) (p127.lo) .lt,
  -- P128.normalization; P128: lambda=263/200, y=3/4: 4831429/10000000 < L_minus(1+(263/200)/(10585001/5000000)); L_plus(1+(263/200)/(21169999/10000000)) < 4831434/10000000.
  Comparison.ofRats ((0 : Rat)) (p128.lo) .lt,
  -- P129.normalization; P129: lambda=263/200, y=99/128: 4742274/10000000 < L_minus(1+(263/200)/(10836017/5000000)); L_plus(1+(263/200)/(21672031/10000000)) < 4742280/10000000.
  Comparison.ofRats ((0 : Rat)) (p129.lo) .lt,
  -- P130.normalization; P130: lambda=263/200, y=63/80: 4689401/10000000 < L_minus(1+(263/200)/(439579/200000)); L_plus(1+(263/200)/(21978947/10000000)) < 4689407/10000000.
  Comparison.ofRats ((0 : Rat)) (p130.lo) .lt,
  -- P131.normalization; P131: lambda=263/200, y=51/64: 4654410/10000000 < L_minus(1+(263/200)/(22185971/10000000)); L_plus(1+(263/200)/(1386623/625000)) < 4654416/10000000.
  Comparison.ofRats ((0 : Rat)) (p131.lo) .lt,
  -- P132.normalization; P132: lambda=263/200, y=105/128: 4567830/10000000 < L_minus(1+(263/200)/(709753/312500)); L_plus(1+(263/200)/(22712093/10000000)) < 4567836/10000000.
  Comparison.ofRats ((0 : Rat)) (p132.lo) .lt,
  -- P133.normalization; P133: lambda=263/200, y=21/25: 4496089/10000000 < L_minus(1+(263/200)/(23163671/10000000)); L_plus(1+(263/200)/(5790917/2500000)) < 4496094/10000000.
  Comparison.ofRats ((0 : Rat)) (p133.lo) .lt,
  -- P134.normalization; P134: lambda=263/200, y=27/32: 4482525/10000000 < L_minus(1+(263/200)/(11625349/5000000)); L_plus(1+(263/200)/(4650139/2000000)) < 4482531/10000000.
  Comparison.ofRats ((0 : Rat)) (p134.lo) .lt,
  -- P135.normalization; P135: lambda=263/200, y=111/128: 4398488/10000000 < L_minus(1+(263/200)/(23802073/10000000)); L_plus(1+(263/200)/(23802069/10000000)) < 4398494/10000000.
  Comparison.ofRats ((0 : Rat)) (p135.lo) .lt,
  -- P136.normalization; P136: lambda=263/200, y=57/64: 4315710/10000000 < L_minus(1+(263/200)/(12183261/5000000)); L_plus(1+(263/200)/(24366519/10000000)) < 4315716/10000000.
  Comparison.ofRats ((0 : Rat)) (p136.lo) .lt,
  -- P137.normalization; P137: lambda=263/200, y=15/16: 4153897/10000000 < L_minus(1+(263/200)/(3191987/1250000)); L_plus(1+(263/200)/(25535893/10000000)) < 4153902/10000000.
  Comparison.ofRats ((0 : Rat)) (p137.lo) .lt,
  -- P138.normalization; P138: lambda=263/200, y=63/64: 3997013/10000000 < L_minus(1+(263/200)/(26761389/10000000)); L_plus(1+(263/200)/(13380693/5000000)) < 3997018/10000000.
  Comparison.ofRats ((0 : Rat)) (p138.lo) .lt,
  -- P139.normalization; P139: lambda=263/200, y=33/32: 3844983/10000000 < L_minus(1+(263/200)/(5609139/2000000)); L_plus(1+(263/200)/(7011423/2500000)) < 3844988/10000000.
  Comparison.ofRats ((0 : Rat)) (p139.lo) .lt,
  -- P140.normalization; P140: lambda=263/200, y=69/64: 3697728/10000000 < L_minus(1+(263/200)/(7347909/2500000)); L_plus(1+(263/200)/(29391633/10000000)) < 3697734/10000000.
  Comparison.ofRats ((0 : Rat)) (p140.lo) .lt,
  -- P141.normalization; P141: lambda=263/200, y=9/8: 3555166/10000000 < L_minus(1+(263/200)/(3080217/1000000)); L_plus(1+(263/200)/(30802167/10000000)) < 3555171/10000000.
  Comparison.ofRats ((0 : Rat)) (p141.lo) .lt,
  -- P142.normalization; P142: lambda=263/200, y=75/64: 3417210/10000000 < L_minus(1+(263/200)/(32280397/10000000)); L_plus(1+(263/200)/(16140197/5000000)) < 3417215/10000000.
  Comparison.ofRats ((0 : Rat)) (p142.lo) .lt,
  -- P143.normalization; P143: lambda=263/200, y=39/32: 3283773/10000000 < L_minus(1+(263/200)/(16914783/5000000)); L_plus(1+(263/200)/(16914781/5000000)) < 3283778/10000000.
  Comparison.ofRats ((0 : Rat)) (p143.lo) .lt,
  -- P144.normalization; P144: lambda=263/200, y=81/64: 3154765/10000000 < L_minus(1+(263/200)/(35453081/10000000)); L_plus(1+(263/200)/(35453077/10000000)) < 3154770/10000000.
  Comparison.ofRats ((0 : Rat)) (p144.lo) .lt,
  -- P145.normalization; P145: lambda=263/200, y=21/16: 3030093/10000000 < L_minus(1+(263/200)/(37154509/10000000)); L_plus(1+(263/200)/(18577253/5000000)) < 3030098/10000000.
  Comparison.ofRats ((0 : Rat)) (p145.lo) .lt,
  -- P146.normalization; P146: lambda=263/200, y=87/64: 2909663/10000000 < L_minus(1+(263/200)/(4867199/1250000)); L_plus(1+(263/200)/(9734397/2500000)) < 2909668/10000000.
  Comparison.ofRats ((0 : Rat)) (p146.lo) .lt,
  -- P147.normalization; P147: lambda=263/200, y=45/32: 2793380/10000000 < L_minus(1+(263/200)/(20403123/5000000)); L_plus(1+(263/200)/(20403121/5000000)) < 2793385/10000000.
  Comparison.ofRats ((0 : Rat)) (p147.lo) .lt,
  -- P148.normalization; P148: lambda=263/200, y=93/64: 2681147/10000000 < L_minus(1+(263/200)/(42764579/10000000)); L_plus(1+(263/200)/(21382287/5000000)) < 2681152/10000000.
  Comparison.ofRats ((0 : Rat)) (p148.lo) .lt,
  -- P149.normalization; P149: lambda=263/200, y=3/2: 2572866/10000000 < L_minus(1+(263/200)/(22408447/5000000)); L_plus(1+(263/200)/(44816889/10000000)) < 2572871/10000000.
  Comparison.ofRats ((0 : Rat)) (p149.lo) .lt,
  -- P150.normalization; P150: lambda=263/200, y=99/64: 2468439/10000000 < L_minus(1+(263/200)/(23483851/5000000)); L_plus(1+(263/200)/(46967697/10000000)) < 2468444/10000000.
  Comparison.ofRats ((0 : Rat)) (p150.lo) .lt,
  -- P151.normalization; P151: lambda=263/200, y=51/32: 2367766/10000000 < L_minus(1+(263/200)/(4922173/1000000)); L_plus(1+(263/200)/(12305431/2500000)) < 2367772/10000000.
  Comparison.ofRats ((0 : Rat)) (p151.lo) .lt,
  -- P152.normalization; P152: lambda=263/200, y=27/16: 2177291/10000000 < L_minus(1+(263/200)/(6757437/1250000)); L_plus(1+(263/200)/(1689359/312500)) < 2177295/10000000.
  Comparison.ofRats ((0 : Rat)) (p152.lo) .lt,
  -- P153.normalization; P153: lambda=263/200, y=57/32: 2000648/10000000 < L_minus(1+(263/200)/(59372743/10000000)); L_plus(1+(263/200)/(14843183/2500000)) < 2000651/10000000.
  Comparison.ofRats ((0 : Rat)) (p153.lo) .lt,
  -- P154.normalization; P154: lambda=263/200, y=15/8: 1837052/10000000 < L_minus(1+(263/200)/(32604103/5000000)); L_plus(1+(263/200)/(6520819/1000000)) < 1837056/10000000.
  Comparison.ofRats ((0 : Rat)) (p154.lo) .lt,
  -- P155.normalization; P155: lambda=263/200, y=63/32: 1685732/10000000 < L_minus(1+(263/200)/(71617209/10000000)); L_plus(1+(263/200)/(35808593/5000000)) < 1685736/10000000.
  Comparison.ofRats ((0 : Rat)) (p155.lo) .lt,
  -- P156.normalization; P156: lambda=263/200, y=33/16: 1545934/10000000 < L_minus(1+(263/200)/(629249/80000)); L_plus(1+(263/200)/(78656091/10000000)) < 1545937/10000000.
  Comparison.ofRats ((0 : Rat)) (p156.lo) .lt,
  -- P157.normalization; P157: lambda=263/200, y=9/4: 1297992/10000000 < L_minus(1+(263/200)/(23719357/2500000)); L_plus(1+(263/200)/(94877357/10000000)) < 1297996/10000000.
  Comparison.ofRats ((0 : Rat)) (p157.lo) .lt,
  -- P158.normalization; P158: lambda=263/200, y=21/8: 909899/10000000 < L_minus(1+(263/200)/(27609207/2000000)); L_plus(1+(263/200)/(6902287/500000)) < 909904/10000000.
  Comparison.ofRats ((0 : Rat)) (p158.lo) .lt,
  -- P159.normalization; P159: lambda=263/200, y=3: 634155/10000000 < L_minus(1+(263/200)/(100428229/5000000)); L_plus(1+(263/200)/(40171073/2000000)) < 634162/10000000.
  Comparison.ofRats ((0 : Rat)) (p159.lo) .lt,
  -- P160.normalization; P160: lambda=3/2, y=3/8: 7084951/10000000 < L_minus(1+(3/2)/(3637479/2500000)); L_plus(1+(3/2)/(14549913/10000000)) < 7084960/10000000.
  Comparison.ofRats ((0 : Rat)) (p160.lo) .lt,
  -- P161.normalization; P161: lambda=3/2, y=23/50: 6662510/10000000 < L_minus(1+(3/2)/(15840741/10000000)); L_plus(1+(3/2)/(7920369/5000000)) < 6662517/10000000.
  Comparison.ofRats ((0 : Rat)) (p161.lo) .lt,
  -- P162.normalization; P162: lambda=3/2, y=9/16: 6177087/10000000 < L_minus(1+(3/2)/(4387637/2500000)); L_plus(1+(3/2)/(3510109/2000000)) < 6177094/10000000.
  Comparison.ofRats ((0 : Rat)) (p162.lo) .lt,
  -- P163.normalization; P163: lambda=3/2, y=21/32: 5755956/10000000 < L_minus(1+(3/2)/(9637753/5000000)); L_plus(1+(3/2)/(19275503/10000000)) < 5755961/10000000.
  Comparison.ofRats ((0 : Rat)) (p163.lo) .lt,
  -- P164.normalization; P164: lambda=3/2, y=69/100: 5609655/10000000 < L_minus(1+(3/2)/(19937157/10000000)); L_plus(1+(3/2)/(9968577/5000000)) < 5609661/10000000.
  Comparison.ofRats ((0 : Rat)) (p164.lo) .lt,
  -- P165.normalization; P165: lambda=3/2, y=299/400: 5366822/10000000 < L_minus(1+(3/2)/(21117143/10000000)); L_plus(1+(3/2)/(1055857/500000)) < 5366828/10000000.
  Comparison.ofRats ((0 : Rat)) (p165.lo) .lt,
  -- P166.normalization; P166: lambda=3/2, y=3/4: 5356447/10000000 < L_minus(1+(3/2)/(10585001/5000000)); L_plus(1+(3/2)/(21169999/10000000)) < 5356452/10000000.
  Comparison.ofRats ((0 : Rat)) (p166.lo) .lt,
  -- P167.normalization; P167: lambda=3/2, y=161/200: 5132016/10000000 < L_minus(1+(3/2)/(22366967/10000000)); L_plus(1+(3/2)/(22366963/10000000)) < 5132022/10000000.
  Comparison.ofRats ((0 : Rat)) (p167.lo) .lt,
  -- P168.normalization; P168: lambda=3/2, y=27/32: 4978264/10000000 < L_minus(1+(3/2)/(11625349/5000000)); L_plus(1+(3/2)/(4650139/2000000)) < 4978269/10000000.
  Comparison.ofRats ((0 : Rat)) (p168.lo) .lt,
  -- P169.normalization; P169: lambda=3/2, y=23/25: 4686140/10000000 < L_minus(1+(3/2)/(5018581/2000000)); L_plus(1+(3/2)/(12546451/5000000)) < 4686145/10000000.
  Comparison.ofRats ((0 : Rat)) (p169.lo) .lt,
  -- P170.normalization; P170: lambda=3/2, y=15/16: 4621025/10000000 < L_minus(1+(3/2)/(3191987/1250000)); L_plus(1+(3/2)/(25535893/10000000)) < 4621030/10000000.
  Comparison.ofRats ((0 : Rat)) (p170.lo) .lt,
  -- P171.normalization; P171: lambda=3/2, y=33/32: 4284268/10000000 < L_minus(1+(3/2)/(5609139/2000000)); L_plus(1+(3/2)/(7011423/2500000)) < 4284274/10000000.
  Comparison.ofRats ((0 : Rat)) (p171.lo) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 64 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Normalization005
