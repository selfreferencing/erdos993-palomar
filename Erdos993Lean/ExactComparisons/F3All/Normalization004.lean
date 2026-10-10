module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Normalization004

def records : List Comparison := [
  -- P044.normalization; P044: lambda=7/8, y=39/64: 3891519/10000000 < L_minus(1+(7/8)/(1149551/625000)); L_plus(1+(7/8)/(18392813/10000000)) < 3891525/10000000.
  Comparison.ofRats ((0 : Rat)) (p044.lo) .lt,
  -- P045.normalization; P045: lambda=7/8, y=21/32: 3742795/10000000 < L_minus(1+(7/8)/(9637753/5000000)); L_plus(1+(7/8)/(19275503/10000000)) < 3742801/10000000.
  Comparison.ofRats ((0 : Rat)) (p045.lo) .lt,
  -- P046.normalization; P046: lambda=7/8, y=45/64: 3598790/10000000 < L_minus(1+(7/8)/(20200557/10000000)); L_plus(1+(7/8)/(10100277/5000000)) < 3598795/10000000.
  Comparison.ofRats ((0 : Rat)) (p046.lo) .lt,
  -- P047.normalization; P047: lambda=7/8, y=3/4: 3459417/10000000 < L_minus(1+(7/8)/(10585001/5000000)); L_plus(1+(7/8)/(21169999/10000000)) < 3459423/10000000.
  Comparison.ofRats ((0 : Rat)) (p047.lo) .lt,
  -- P048.normalization; P048: lambda=7/8, y=51/64: 3324592/10000000 < L_minus(1+(7/8)/(22185971/10000000)); L_plus(1+(7/8)/(1386623/625000)) < 3324597/10000000.
  Comparison.ofRats ((0 : Rat)) (p048.lo) .lt,
  -- P049.normalization; P049: lambda=7/8, y=27/32: 3194223/10000000 < L_minus(1+(7/8)/(11625349/5000000)); L_plus(1+(7/8)/(4650139/2000000)) < 3194228/10000000.
  Comparison.ofRats ((0 : Rat)) (p049.lo) .lt,
  -- P050.normalization; P050: lambda=7/8, y=15/16: 2946486/10000000 < L_minus(1+(7/8)/(3191987/1250000)); L_plus(1+(7/8)/(25535893/10000000)) < 2946492/10000000.
  Comparison.ofRats ((0 : Rat)) (p050.lo) .lt,
  -- P051.normalization; P051: lambda=7/8, y=33/32: 2715454/10000000 < L_minus(1+(7/8)/(5609139/2000000)); L_plus(1+(7/8)/(7011423/2500000)) < 2715459/10000000.
  Comparison.ofRats ((0 : Rat)) (p051.lo) .lt,
  -- P052.normalization; P052: lambda=7/8, y=9/8: 2500351/10000000 < L_minus(1+(7/8)/(3080217/1000000)); L_plus(1+(7/8)/(30802167/10000000)) < 2500356/10000000.
  Comparison.ofRats ((0 : Rat)) (p052.lo) .lt,
  -- P053.normalization; P053: lambda=7/8, y=39/32: 2300390/10000000 < L_minus(1+(7/8)/(16914783/5000000)); L_plus(1+(7/8)/(16914781/5000000)) < 2300395/10000000.
  Comparison.ofRats ((0 : Rat)) (p053.lo) .lt,
  -- P054.normalization; P054: lambda=7/8, y=21/16: 2114780/10000000 < L_minus(1+(7/8)/(37154509/10000000)); L_plus(1+(7/8)/(18577253/5000000)) < 2114784/10000000.
  Comparison.ofRats ((0 : Rat)) (p054.lo) .lt,
  -- P055.normalization; P055: lambda=7/8, y=45/32: 1942730/10000000 < L_minus(1+(7/8)/(20403123/5000000)); L_plus(1+(7/8)/(20403121/5000000)) < 1942733/10000000.
  Comparison.ofRats ((0 : Rat)) (p055.lo) .lt,
  -- P056.normalization; P056: lambda=7/8, y=3/2: 1783459/10000000 < L_minus(1+(7/8)/(22408447/5000000)); L_plus(1+(7/8)/(44816889/10000000)) < 1783462/10000000.
  Comparison.ofRats ((0 : Rat)) (p056.lo) .lt,
  -- P057.normalization; P057: lambda=7/8, y=51/32: 1636201/10000000 < L_minus(1+(7/8)/(4922173/1000000)); L_plus(1+(7/8)/(12305431/2500000)) < 1636205/10000000.
  Comparison.ofRats ((0 : Rat)) (p057.lo) .lt,
  -- P058.normalization; P058: lambda=7/8, y=27/16: 1500209/10000000 < L_minus(1+(7/8)/(6757437/1250000)); L_plus(1+(7/8)/(1689359/312500)) < 1500212/10000000.
  Comparison.ofRats ((0 : Rat)) (p058.lo) .lt,
  -- P059.normalization; P059: lambda=7/8, y=15/8: 1259147/10000000 < L_minus(1+(7/8)/(32604103/5000000)); L_plus(1+(7/8)/(6520819/1000000)) < 1259150/10000000.
  Comparison.ofRats ((0 : Rat)) (p059.lo) .lt,
  -- P060.normalization; P060: lambda=7/8, y=33/16: 1054797/10000000 < L_minus(1+(7/8)/(629249/80000)); L_plus(1+(7/8)/(78656091/10000000)) < 1054801/10000000.
  Comparison.ofRats ((0 : Rat)) (p060.lo) .lt,
  -- P061.normalization; P061: lambda=7/8, y=9/4: 882161/10000000 < L_minus(1+(7/8)/(23719357/2500000)); L_plus(1+(7/8)/(94877357/10000000)) < 882164/10000000.
  Comparison.ofRats ((0 : Rat)) (p061.lo) .lt,
  -- P062.normalization; P062: lambda=7/8, y=21/8: 614567/10000000 < L_minus(1+(7/8)/(27609207/2000000)); L_plus(1+(7/8)/(6902287/500000)) < 614572/10000000.
  Comparison.ofRats ((0 : Rat)) (p062.lo) .lt,
  -- P063.normalization; P063: lambda=7/8, y=3: 426411/10000000 < L_minus(1+(7/8)/(100428229/5000000)); L_plus(1+(7/8)/(40171073/2000000)) < 426416/10000000.
  Comparison.ofRats ((0 : Rat)) (p063.lo) .lt,
  -- P064.normalization; P064: lambda=28/25, y=3/16: 6567486/10000000 < L_minus(1+(28/25)/(376947/312500)); L_plus(1+(28/25)/(12062301/10000000)) < 6567493/10000000.
  Comparison.ofRats ((0 : Rat)) (p064.lo) .lt,
  -- P065.normalization; P065: lambda=28/25, y=9/32: 6127067/10000000 < L_minus(1+(28/25)/(13247849/10000000)); L_plus(1+(28/25)/(6623923/5000000)) < 6127074/10000000.
  Comparison.ofRats ((0 : Rat)) (p065.lo) .lt,
  -- P066.normalization; P066: lambda=28/25, y=3/8: 5708459/10000000 < L_minus(1+(28/25)/(3637479/2500000)); L_plus(1+(28/25)/(14549913/10000000)) < 5708465/10000000.
  Comparison.ofRats ((0 : Rat)) (p066.lo) .lt,
  -- P067.normalization; P067: lambda=28/25, y=27/64: 5507269/10000000 < L_minus(1+(28/25)/(15248181/10000000)); L_plus(1+(28/25)/(7624089/5000000)) < 5507275/10000000.
  Comparison.ofRats ((0 : Rat)) (p067.lo) .lt,
  -- P068.normalization; P068: lambda=28/25, y=15/32: 5311443/10000000 < L_minus(1+(28/25)/(3994989/2500000)); L_plus(1+(28/25)/(15979953/10000000)) < 5311449/10000000.
  Comparison.ofRats ((0 : Rat)) (p068.lo) .lt,
  -- P069.normalization; P069: lambda=28/25, y=63/128: 5215529/10000000 < L_minus(1+(28/25)/(1635891/1000000)); L_plus(1+(28/25)/(16358907/10000000)) < 5215535/10000000.
  Comparison.ofRats ((0 : Rat)) (p069.lo) .lt,
  -- P070.normalization; P070: lambda=28/25, y=33/64: 5120941/10000000 < L_minus(1+(28/25)/(334937/200000)); L_plus(1+(28/25)/(16746847/10000000)) < 5120946/10000000.
  Comparison.ofRats ((0 : Rat)) (p070.lo) .lt,
  -- P071.normalization; P071: lambda=28/25, y=69/128: 5027671/10000000 < L_minus(1+(28/25)/(1714399/1000000)); L_plus(1+(28/25)/(17143987/10000000)) < 5027677/10000000.
  Comparison.ofRats ((0 : Rat)) (p071.lo) .lt,
  -- P072.normalization; P072: lambda=28/25, y=9/16: 4935714/10000000 < L_minus(1+(28/25)/(4387637/2500000)); L_plus(1+(28/25)/(3510109/2000000)) < 4935720/10000000.
  Comparison.ofRats ((0 : Rat)) (p072.lo) .lt,
  -- P073.normalization; P073: lambda=28/25, y=75/128: 4845063/10000000 < L_minus(1+(28/25)/(17966747/10000000)); L_plus(1+(28/25)/(2245843/1250000)) < 4845069/10000000.
  Comparison.ofRats ((0 : Rat)) (p073.lo) .lt,
  -- P074.normalization; P074: lambda=28/25, y=39/64: 4755712/10000000 < L_minus(1+(28/25)/(1149551/625000)); L_plus(1+(28/25)/(18392813/10000000)) < 4755718/10000000.
  Comparison.ofRats ((0 : Rat)) (p074.lo) .lt,
  -- P075.normalization; P075: lambda=28/25, y=81/128: 4667653/10000000 < L_minus(1+(28/25)/(18828989/10000000)); L_plus(1+(28/25)/(9414493/5000000)) < 4667659/10000000.
  Comparison.ofRats ((0 : Rat)) (p075.lo) .lt,
  -- P076.normalization; P076: lambda=28/25, y=21/32: 4580879/10000000 < L_minus(1+(28/25)/(9637753/5000000)); L_plus(1+(28/25)/(19275503/10000000)) < 4580884/10000000.
  Comparison.ofRats ((0 : Rat)) (p076.lo) .lt,
  -- P077.normalization; P077: lambda=28/25, y=87/128: 4495381/10000000 < L_minus(1+(28/25)/(19732611/10000000)); L_plus(1+(28/25)/(154161/78125)) < 4495386/10000000.
  Comparison.ofRats ((0 : Rat)) (p077.lo) .lt,
  -- P078.normalization; P078: lambda=28/25, y=45/64: 4411152/10000000 < L_minus(1+(28/25)/(20200557/10000000)); L_plus(1+(28/25)/(10100277/5000000)) < 4411157/10000000.
  Comparison.ofRats ((0 : Rat)) (p078.lo) .lt,
  -- P079.normalization; P079: lambda=28/25, y=93/128: 4328184/10000000 < L_minus(1+(28/25)/(20679599/10000000)); L_plus(1+(28/25)/(5169899/2500000)) < 4328189/10000000.
  Comparison.ofRats ((0 : Rat)) (p079.lo) .lt,
  -- P080.normalization; P080: lambda=28/25, y=3/4: 4246467/10000000 < L_minus(1+(28/25)/(10585001/5000000)); L_plus(1+(28/25)/(21169999/10000000)) < 4246472/10000000.
  Comparison.ofRats ((0 : Rat)) (p080.lo) .lt,
  -- P081.normalization; P081: lambda=28/25, y=99/128: 4165993/10000000 < L_minus(1+(28/25)/(10836017/5000000)); L_plus(1+(28/25)/(21672031/10000000)) < 4165999/10000000.
  Comparison.ofRats ((0 : Rat)) (p081.lo) .lt,
  -- P082.normalization; P082: lambda=28/25, y=51/64: 4086754/10000000 < L_minus(1+(28/25)/(22185971/10000000)); L_plus(1+(28/25)/(1386623/625000)) < 4086759/10000000.
  Comparison.ofRats ((0 : Rat)) (p082.lo) .lt,
  -- P083.normalization; P083: lambda=28/25, y=105/128: 4008738/10000000 < L_minus(1+(28/25)/(709753/312500)); L_plus(1+(28/25)/(22712093/10000000)) < 4008744/10000000.
  Comparison.ofRats ((0 : Rat)) (p083.lo) .lt,
  -- P084.normalization; P084: lambda=28/25, y=27/32: 3931938/10000000 < L_minus(1+(28/25)/(11625349/5000000)); L_plus(1+(28/25)/(4650139/2000000)) < 3931943/10000000.
  Comparison.ofRats ((0 : Rat)) (p084.lo) .lt,
  -- P085.normalization; P085: lambda=28/25, y=111/128: 3856343/10000000 < L_minus(1+(28/25)/(23802073/10000000)); L_plus(1+(28/25)/(23802069/10000000)) < 3856349/10000000.
  Comparison.ofRats ((0 : Rat)) (p085.lo) .lt,
  -- P086.normalization; P086: lambda=28/25, y=57/64: 3781944/10000000 < L_minus(1+(28/25)/(12183261/5000000)); L_plus(1+(28/25)/(24366519/10000000)) < 3781949/10000000.
  Comparison.ofRats ((0 : Rat)) (p086.lo) .lt,
  -- P087.normalization; P087: lambda=28/25, y=15/16: 3636689/10000000 < L_minus(1+(28/25)/(3191987/1250000)); L_plus(1+(28/25)/(25535893/10000000)) < 3636695/10000000.
  Comparison.ofRats ((0 : Rat)) (p087.lo) .lt,
  -- P088.normalization; P088: lambda=28/25, y=63/64: 3496091/10000000 < L_minus(1+(28/25)/(26761389/10000000)); L_plus(1+(28/25)/(13380693/5000000)) < 3496097/10000000.
  Comparison.ofRats ((0 : Rat)) (p088.lo) .lt,
  -- P089.normalization; P089: lambda=28/25, y=33/32: 3360063/10000000 < L_minus(1+(28/25)/(5609139/2000000)); L_plus(1+(28/25)/(7011423/2500000)) < 3360068/10000000.
  Comparison.ofRats ((0 : Rat)) (p089.lo) .lt,
  -- P090.normalization; P090: lambda=28/25, y=69/64: 3228516/10000000 < L_minus(1+(28/25)/(7347909/2500000)); L_plus(1+(28/25)/(29391633/10000000)) < 3228521/10000000.
  Comparison.ofRats ((0 : Rat)) (p090.lo) .lt,
  -- P091.normalization; P091: lambda=28/25, y=9/8: 3101358/10000000 < L_minus(1+(28/25)/(3080217/1000000)); L_plus(1+(28/25)/(30802167/10000000)) < 3101364/10000000.
  Comparison.ofRats ((0 : Rat)) (p091.lo) .lt,
  -- P092.normalization; P092: lambda=28/25, y=75/64: 2978497/10000000 < L_minus(1+(28/25)/(32280397/10000000)); L_plus(1+(28/25)/(16140197/5000000)) < 2978503/10000000.
  Comparison.ofRats ((0 : Rat)) (p092.lo) .lt,
  -- P093.normalization; P093: lambda=28/25, y=39/32: 2859838/10000000 < L_minus(1+(28/25)/(16914783/5000000)); L_plus(1+(28/25)/(16914781/5000000)) < 2859844/10000000.
  Comparison.ofRats ((0 : Rat)) (p093.lo) .lt,
  -- P094.normalization; P094: lambda=28/25, y=81/64: 2745285/10000000 < L_minus(1+(28/25)/(35453081/10000000)); L_plus(1+(28/25)/(35453077/10000000)) < 2745290/10000000.
  Comparison.ofRats ((0 : Rat)) (p094.lo) .lt,
  -- P095.normalization; P095: lambda=28/25, y=21/16: 2634740/10000000 < L_minus(1+(28/25)/(37154509/10000000)); L_plus(1+(28/25)/(18577253/5000000)) < 2634746/10000000.
  Comparison.ofRats ((0 : Rat)) (p095.lo) .lt,
  -- P096.normalization; P096: lambda=28/25, y=87/64: 2528106/10000000 < L_minus(1+(28/25)/(4867199/1250000)); L_plus(1+(28/25)/(9734397/2500000)) < 2528111/10000000.
  Comparison.ofRats ((0 : Rat)) (p096.lo) .lt,
  -- P097.normalization; P097: lambda=28/25, y=45/32: 2425284/10000000 < L_minus(1+(28/25)/(20403123/5000000)); L_plus(1+(28/25)/(20403121/5000000)) < 2425289/10000000.
  Comparison.ofRats ((0 : Rat)) (p097.lo) .lt,
  -- P098.normalization; P098: lambda=28/25, y=93/64: 2326174/10000000 < L_minus(1+(28/25)/(42764579/10000000)); L_plus(1+(28/25)/(21382287/5000000)) < 2326179/10000000.
  Comparison.ofRats ((0 : Rat)) (p098.lo) .lt,
  -- P099.normalization; P099: lambda=28/25, y=3/2: 2230679/10000000 < L_minus(1+(28/25)/(22408447/5000000)); L_plus(1+(28/25)/(44816889/10000000)) < 2230683/10000000.
  Comparison.ofRats ((0 : Rat)) (p099.lo) .lt,
  -- P100.normalization; P100: lambda=28/25, y=99/64: 2138699/10000000 < L_minus(1+(28/25)/(23483851/5000000)); L_plus(1+(28/25)/(46967697/10000000)) < 2138702/10000000.
  Comparison.ofRats ((0 : Rat)) (p100.lo) .lt,
  -- P101.normalization; P101: lambda=28/25, y=51/32: 2050134/10000000 < L_minus(1+(28/25)/(4922173/1000000)); L_plus(1+(28/25)/(12305431/2500000)) < 2050138/10000000.
  Comparison.ofRats ((0 : Rat)) (p101.lo) .lt,
  -- P102.normalization; P102: lambda=28/25, y=27/16: 1882862/10000000 < L_minus(1+(28/25)/(6757437/1250000)); L_plus(1+(28/25)/(1689359/312500)) < 1882865/10000000.
  Comparison.ofRats ((0 : Rat)) (p102.lo) .lt,
  -- P103.normalization; P103: lambda=28/25, y=57/32: 1728086/10000000 < L_minus(1+(28/25)/(59372743/10000000)); L_plus(1+(28/25)/(14843183/2500000)) < 1728089/10000000.
  Comparison.ofRats ((0 : Rat)) (p103.lo) .lt,
  -- P104.normalization; P104: lambda=28/25, y=15/8: 1585046/10000000 < L_minus(1+(28/25)/(32604103/5000000)); L_plus(1+(28/25)/(6520819/1000000)) < 1585050/10000000.
  Comparison.ofRats ((0 : Rat)) (p104.lo) .lt,
  -- P105.normalization; P105: lambda=28/25, y=63/32: 1453003/10000000 < L_minus(1+(28/25)/(71617209/10000000)); L_plus(1+(28/25)/(35808593/5000000)) < 1453007/10000000.
  Comparison.ofRats ((0 : Rat)) (p105.lo) .lt,
  -- P106.normalization; P106: lambda=28/25, y=33/16: 1331241/10000000 < L_minus(1+(28/25)/(629249/80000)); L_plus(1+(28/25)/(78656091/10000000)) < 1331245/10000000.
  Comparison.ofRats ((0 : Rat)) (p106.lo) .lt,
  -- P107.normalization; P107: lambda=28/25, y=9/4: 1115833/10000000 < L_minus(1+(28/25)/(23719357/2500000)); L_plus(1+(28/25)/(94877357/10000000)) < 1115837/10000000.
  Comparison.ofRats ((0 : Rat)) (p107.lo) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 64 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Normalization004
