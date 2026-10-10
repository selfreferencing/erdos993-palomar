module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Normalization006

def records : List Comparison := [
  -- P172.normalization; P172: lambda=3/2, y=9/8: 3967460/10000000 < L_minus(1+(3/2)/(3080217/1000000)); L_plus(1+(3/2)/(30802167/10000000)) < 3967466/10000000.
  Comparison.ofRats ((0 : Rat)) (p172.lo) .lt,
  -- P173.normalization; P173: lambda=3/2, y=39/32: 3670005/10000000 < L_minus(1+(3/2)/(16914783/5000000)); L_plus(1+(3/2)/(16914781/5000000)) < 3670011/10000000.
  Comparison.ofRats ((0 : Rat)) (p173.lo) .lt,
  -- P174.normalization; P174: lambda=3/2, y=21/16: 3391252/10000000 < L_minus(1+(3/2)/(37154509/10000000)); L_plus(1+(3/2)/(18577253/5000000)) < 3391257/10000000.
  Comparison.ofRats ((0 : Rat)) (p174.lo) .lt,
  -- P175.normalization; P175: lambda=3/2, y=45/32: 3130503/10000000 < L_minus(1+(3/2)/(20403123/5000000)); L_plus(1+(3/2)/(20403121/5000000)) < 3130509/10000000.
  Comparison.ofRats ((0 : Rat)) (p175.lo) .lt,
  -- P176.normalization; P176: lambda=3/2, y=3/2: 2887027/10000000 < L_minus(1+(3/2)/(22408447/5000000)); L_plus(1+(3/2)/(44816889/10000000)) < 2887032/10000000.
  Comparison.ofRats ((0 : Rat)) (p176.lo) .lt,
  -- P177.normalization; P177: lambda=3/2, y=27/16: 2448829/10000000 < L_minus(1+(3/2)/(6757437/1250000)); L_plus(1+(3/2)/(1689359/312500)) < 2448834/10000000.
  Comparison.ofRats ((0 : Rat)) (p177.lo) .lt,
  -- P178.normalization; P178: lambda=3/2, y=15/8: 2070403/10000000 < L_minus(1+(3/2)/(32604103/5000000)); L_plus(1+(3/2)/(6520819/1000000)) < 2070407/10000000.
  Comparison.ofRats ((0 : Rat)) (p178.lo) .lt,
  -- P179.normalization; P179: lambda=3/2, y=33/16: 1745442/10000000 < L_minus(1+(3/2)/(629249/80000)); L_plus(1+(3/2)/(78656091/10000000)) < 1745445/10000000.
  Comparison.ofRats ((0 : Rat)) (p179.lo) .lt,
  -- P180.normalization; P180: lambda=3/2, y=9/4: 1467795/10000000 < L_minus(1+(3/2)/(23719357/2500000)); L_plus(1+(3/2)/(94877357/10000000)) < 1467799/10000000.
  Comparison.ofRats ((0 : Rat)) (p180.lo) .lt,
  -- P181.normalization; P181: lambda=3/2, y=21/8: 1031514/10000000 < L_minus(1+(3/2)/(27609207/2000000)); L_plus(1+(3/2)/(6902287/500000)) < 1031519/10000000.
  Comparison.ofRats ((0 : Rat)) (p181.lo) .lt,
  -- P182.normalization; P182: lambda=3/2, y=3: 720230/10000000 < L_minus(1+(3/2)/(100428229/5000000)); L_plus(1+(3/2)/(40171073/2000000)) < 720237/10000000.
  Comparison.ofRats ((0 : Rat)) (p182.lo) .lt,
  -- P183.normalization; P183: lambda=7/4, y=3/8: 7897087/10000000 < L_minus(1+(7/4)/(3637479/2500000)); L_plus(1+(7/4)/(14549913/10000000)) < 7897096/10000000.
  Comparison.ofRats ((0 : Rat)) (p183.lo) .lt,
  -- P184.normalization; P184: lambda=7/4, y=51/100: 7182621/10000000 < L_minus(1+(7/4)/(16652913/10000000)); L_plus(1+(7/4)/(1665291/1000000)) < 7182630/10000000.
  Comparison.ofRats ((0 : Rat)) (p184.lo) .lt,
  -- P185.normalization; P185: lambda=7/4, y=9/16: 6917055/10000000 < L_minus(1+(7/4)/(4387637/2500000)); L_plus(1+(7/4)/(3510109/2000000)) < 6917064/10000000.
  Comparison.ofRats ((0 : Rat)) (p185.lo) .lt,
  -- P186.normalization; P186: lambda=7/4, y=51/80: 6549627/10000000 < L_minus(1+(7/4)/(18917457/10000000)); L_plus(1+(7/4)/(9458727/5000000)) < 6549634/10000000.
  Comparison.ofRats ((0 : Rat)) (p186.lo) .lt,
  -- P187.normalization; P187: lambda=7/4, y=3/4: 6024787/10000000 < L_minus(1+(7/4)/(10585001/5000000)); L_plus(1+(7/4)/(21169999/10000000)) < 6024793/10000000.
  Comparison.ofRats ((0 : Rat)) (p187.lo) .lt,
  -- P188.normalization; P188: lambda=7/4, y=153/200: 5957184/10000000 < L_minus(1+(7/4)/(4297989/2000000)); L_plus(1+(7/4)/(10744971/5000000)) < 5957189/10000000.
  Comparison.ofRats ((0 : Rat)) (p188.lo) .lt,
  -- P189.normalization; P189: lambda=7/4, y=663/800: 5676067/10000000 < L_minus(1+(7/4)/(1145227/500000)); L_plus(1+(7/4)/(22904537/10000000)) < 5676073/10000000.
  Comparison.ofRats ((0 : Rat)) (p189.lo) .lt,
  -- P190.normalization; P190: lambda=7/4, y=357/400: 5404928/10000000 < L_minus(1+(7/4)/(6103063/2500000)); L_plus(1+(7/4)/(24412249/10000000)) < 5404934/10000000.
  Comparison.ofRats ((0 : Rat)) (p190.lo) .lt,
  -- P191.normalization; P191: lambda=7/4, y=15/16: 5219492/10000000 < L_minus(1+(7/4)/(3191987/1250000)); L_plus(1+(7/4)/(25535893/10000000)) < 5219497/10000000.
  Comparison.ofRats ((0 : Rat)) (p191.lo) .lt,
  -- P192.normalization; P192: lambda=7/4, y=51/50: 4892183/10000000 < L_minus(1+(7/4)/(27731949/10000000)); L_plus(1+(7/4)/(13865973/5000000)) < 4892188/10000000.
  Comparison.ofRats ((0 : Rat)) (p192.lo) .lt,
  -- P193.normalization; P193: lambda=7/4, y=9/8: 4498911/10000000 < L_minus(1+(7/4)/(3080217/1000000)); L_plus(1+(7/4)/(30802167/10000000)) < 4498916/10000000.
  Comparison.ofRats ((0 : Rat)) (p193.lo) .lt,
  -- P194.normalization; P194: lambda=7/4, y=21/16: 3859463/10000000 < L_minus(1+(7/4)/(37154509/10000000)); L_plus(1+(7/4)/(18577253/5000000)) < 3859468/10000000.
  Comparison.ofRats ((0 : Rat)) (p194.lo) .lt,
  -- P195.normalization; P195: lambda=7/4, y=3/2: 3296471/10000000 < L_minus(1+(7/4)/(22408447/5000000)); L_plus(1+(7/4)/(44816889/10000000)) < 3296476/10000000.
  Comparison.ofRats ((0 : Rat)) (p195.lo) .lt,
  -- P196.normalization; P196: lambda=7/4, y=27/16: 2804437/10000000 < L_minus(1+(7/4)/(6757437/1250000)); L_plus(1+(7/4)/(1689359/312500)) < 2804442/10000000.
  Comparison.ofRats ((0 : Rat)) (p196.lo) .lt,
  -- P197.normalization; P197: lambda=7/4, y=15/8: 2377332/10000000 < L_minus(1+(7/4)/(32604103/5000000)); L_plus(1+(7/4)/(6520819/1000000)) < 2377338/10000000.
  Comparison.ofRats ((0 : Rat)) (p197.lo) .lt,
  -- P198.normalization; P198: lambda=7/4, y=33/16: 2008875/10000000 < L_minus(1+(7/4)/(629249/80000)); L_plus(1+(7/4)/(78656091/10000000)) < 2008879/10000000.
  Comparison.ofRats ((0 : Rat)) (p198.lo) .lt,
  -- P199.normalization; P199: lambda=7/4, y=9/4: 1692771/10000000 < L_minus(1+(7/4)/(23719357/2500000)); L_plus(1+(7/4)/(94877357/10000000)) < 1692775/10000000.
  Comparison.ofRats ((0 : Rat)) (p199.lo) .lt,
  -- P200.normalization; P200: lambda=7/4, y=21/8: 1193544/10000000 < L_minus(1+(7/4)/(27609207/2000000)); L_plus(1+(7/4)/(6902287/500000)) < 1193549/10000000.
  Comparison.ofRats ((0 : Rat)) (p200.lo) .lt,
  -- P201.normalization; P201: lambda=7/4, y=3: 835382/10000000 < L_minus(1+(7/4)/(100428229/5000000)); L_plus(1+(7/4)/(40171073/2000000)) < 835389/10000000.
  Comparison.ofRats ((0 : Rat)) (p201.lo) .lt,
  -- P202.normalization; P202: lambda=2, y=3/8: 8648193/10000000 < L_minus(1+(2)/(3637479/2500000)); L_plus(1+(2)/(14549913/10000000)) < 8648202/10000000.
  Comparison.ofRats ((0 : Rat)) (p202.lo) .lt,
  -- P203.normalization; P203: lambda=2, y=11/20: 7672793/10000000 < L_minus(1+(2)/(4333133/2500000)); L_plus(1+(2)/(17332529/10000000)) < 7672802/10000000.
  Comparison.ofRats ((0 : Rat)) (p203.lo) .lt,
  -- P204.normalization; P204: lambda=2, y=9/16: 7606022/10000000 < L_minus(1+(2)/(4387637/2500000)); L_plus(1+(2)/(3510109/2000000)) < 7606031/10000000.
  Comparison.ofRats ((0 : Rat)) (p204.lo) .lt,
  -- P205.normalization; P205: lambda=2, y=11/16: 6959741/10000000 < L_minus(1+(2)/(1242961/625000)); L_plus(1+(2)/(19887373/10000000)) < 6959750/10000000.
  Comparison.ofRats ((0 : Rat)) (p205.lo) .lt,
  -- P206.normalization; P206: lambda=2, y=3/4: 6651243/10000000 < L_minus(1+(2)/(10585001/5000000)); L_plus(1+(2)/(21169999/10000000)) < 6651250/10000000.
  Comparison.ofRats ((0 : Rat)) (p206.lo) .lt,
  -- P207.normalization; P207: lambda=2, y=121/160: 6620930/10000000 < L_minus(1+(2)/(21302729/10000000)); L_plus(1+(2)/(10651363/5000000)) < 6620937/10000000.
  Comparison.ofRats ((0 : Rat)) (p207.lo) .lt,
  -- P208.normalization; P208: lambda=2, y=33/40: 6293920/10000000 < L_minus(1+(2)/(22818809/10000000)); L_plus(1+(2)/(11409403/5000000)) < 6293926/10000000.
  Comparison.ofRats ((0 : Rat)) (p208.lo) .lt,
  -- P209.normalization; P209: lambda=2, y=55/64: 6134829/10000000 < L_minus(1+(2)/(23616843/10000000)); L_plus(1+(2)/(590421/250000)) < 6134835/10000000.
  Comparison.ofRats ((0 : Rat)) (p209.lo) .lt,
  -- P210.normalization; P210: lambda=2, y=143/160: 5978672/10000000 < L_minus(1+(2)/(24442787/10000000)); L_plus(1+(2)/(763837/312500)) < 5978678/10000000.
  Comparison.ofRats ((0 : Rat)) (p210.lo) .lt,
  -- P211.normalization; P211: lambda=2, y=15/16: 5784155/10000000 < L_minus(1+(2)/(3191987/1250000)); L_plus(1+(2)/(25535893/10000000)) < 5784161/10000000.
  Comparison.ofRats ((0 : Rat)) (p211.lo) .lt,
  -- P212.normalization; P212: lambda=2, y=77/80: 5675121/10000000 < L_minus(1+(2)/(1309117/500000)); L_plus(1+(2)/(26182337/10000000)) < 5675126/10000000.
  Comparison.ofRats ((0 : Rat)) (p212.lo) .lt,
  -- P213.normalization; P213: lambda=2, y=11/10: 5102705/10000000 < L_minus(1+(2)/(15020831/5000000)); L_plus(1+(2)/(30041659/10000000)) < 5102710/10000000.
  Comparison.ofRats ((0 : Rat)) (p213.lo) .lt,
  -- P214.normalization; P214: lambda=2, y=9/8: 5003537/10000000 < L_minus(1+(2)/(3080217/1000000)); L_plus(1+(2)/(30802167/10000000)) < 5003542/10000000.
  Comparison.ofRats ((0 : Rat)) (p214.lo) .lt,
  -- P215.normalization; P215: lambda=2, y=21/16: 4306729/10000000 < L_minus(1+(2)/(37154509/10000000)); L_plus(1+(2)/(18577253/5000000)) < 4306734/10000000.
  Comparison.ofRats ((0 : Rat)) (p215.lo) .lt,
  -- P216.normalization; P216: lambda=2, y=3/2: 3689808/10000000 < L_minus(1+(2)/(22408447/5000000)); L_plus(1+(2)/(44816889/10000000)) < 3689813/10000000.
  Comparison.ofRats ((0 : Rat)) (p216.lo) .lt,
  -- P217.normalization; P217: lambda=2, y=27/16: 3147833/10000000 < L_minus(1+(2)/(6757437/1250000)); L_plus(1+(2)/(1689359/312500)) < 3147838/10000000.
  Comparison.ofRats ((0 : Rat)) (p217.lo) .lt,
  -- P218.normalization; P218: lambda=2, y=15/8: 2675121/10000000 < L_minus(1+(2)/(32604103/5000000)); L_plus(1+(2)/(6520819/1000000)) < 2675127/10000000.
  Comparison.ofRats ((0 : Rat)) (p218.lo) .lt,
  -- P219.normalization; P219: lambda=2, y=33/16: 2265545/10000000 < L_minus(1+(2)/(629249/80000)); L_plus(1+(2)/(78656091/10000000)) < 2265551/10000000.
  Comparison.ofRats ((0 : Rat)) (p219.lo) .lt,
  -- P220.normalization; P220: lambda=2, y=9/4: 1912797/10000000 < L_minus(1+(2)/(23719357/2500000)); L_plus(1+(2)/(94877357/10000000)) < 1912802/10000000.
  Comparison.ofRats ((0 : Rat)) (p220.lo) .lt,
  -- P221.normalization; P221: lambda=2, y=21/8: 1352990/10000000 < L_minus(1+(2)/(27609207/2000000)); L_plus(1+(2)/(6902287/500000)) < 1352996/10000000.
  Comparison.ofRats ((0 : Rat)) (p221.lo) .lt,
  -- P222.normalization; P222: lambda=2, y=3: 949223/10000000 < L_minus(1+(2)/(100428229/5000000)); L_plus(1+(2)/(40171073/2000000)) < 949231/10000000.
  Comparison.ofRats ((0 : Rat)) (p222.lo) .lt,
  -- P223.normalization; P223: lambda=7/3, y=121/400: 10021959/10000000 < L_minus(1+(7/3)/(6766189/5000000)); L_plus(1+(7/3)/(108259/80000)) < 10021971/10000000.
  Comparison.ofRats ((0 : Rat)) (p223.lo) .lt,
  -- P224.normalization; P224: lambda=7/3, y=3/8: 9569230/10000000 < L_minus(1+(7/3)/(3637479/2500000)); L_plus(1+(7/3)/(14549913/10000000)) < 9569242/10000000.
  Comparison.ofRats ((0 : Rat)) (p224.lo) .lt,
  -- P225.normalization; P225: lambda=7/3, y=121/200: 8216161/10000000 < L_minus(1+(7/3)/(4578131/2500000)); L_plus(1+(7/3)/(18312521/10000000)) < 8216170/10000000.
  Comparison.ofRats ((0 : Rat)) (p225.lo) .lt,
  -- P226.normalization; P226: lambda=7/3, y=3/4: 7429783/10000000 < L_minus(1+(7/3)/(10585001/5000000)); L_plus(1+(7/3)/(21169999/10000000)) < 7429792/10000000.
  Comparison.ofRats ((0 : Rat)) (p226.lo) .lt,
  -- P227.normalization; P227: lambda=7/3, y=121/160: 7397063/10000000 < L_minus(1+(7/3)/(21302729/10000000)); L_plus(1+(7/3)/(10651363/5000000)) < 7397072/10000000.
  Comparison.ofRats ((0 : Rat)) (p227.lo) .lt,
  -- P228.normalization; P228: lambda=7/3, y=2541/3200: 7201184/10000000 < L_minus(1+(7/3)/(22123661/10000000)); L_plus(1+(7/3)/(11061829/5000000)) < 7201193/10000000.
  Comparison.ofRats ((0 : Rat)) (p228.lo) .lt,
  -- P229.normalization; P229: lambda=7/3, y=5203/6400: 7104584/10000000 < L_minus(1+(7/3)/(4509183/2000000)); L_plus(1+(7/3)/(2818239/1250000)) < 7104592/10000000.
  Comparison.ofRats ((0 : Rat)) (p229.lo) .lt,
  -- P230.normalization; P230: lambda=7/3, y=1331/1600: 7008877/10000000 < L_minus(1+(7/3)/(22976229/10000000)); L_plus(1+(7/3)/(11488113/5000000)) < 7008885/10000000.
  Comparison.ofRats ((0 : Rat)) (p230.lo) .lt,
  -- P231.normalization; P231: lambda=7/3, y=1089/1280: 6914064/10000000 < L_minus(1+(7/3)/(5853689/2500000)); L_plus(1+(7/3)/(23414753/10000000)) < 6914073/10000000.
  Comparison.ofRats ((0 : Rat)) (p231.lo) .lt,
  -- P232.normalization; P232: lambda=7/3, y=11011/12800: 6866992/10000000 < L_minus(1+(7/3)/(5909287/2500000)); L_plus(1+(7/3)/(4727429/2000000)) < 6867001/10000000.
  Comparison.ofRats ((0 : Rat)) (p232.lo) .lt,
  -- P233.normalization; P233: lambda=7/3, y=2783/3200: 6820145/10000000 < L_minus(1+(7/3)/(5965413/2500000)); L_plus(1+(7/3)/(23861649/10000000)) < 6820153/10000000.
  Comparison.ofRats ((0 : Rat)) (p233.lo) .lt,
  -- P234.normalization; P234: lambda=7/3, y=11253/12800: 6773520/10000000 < L_minus(1+(7/3)/(24088289/10000000)); L_plus(1+(7/3)/(12044143/5000000)) < 6773528/10000000.
  Comparison.ofRats ((0 : Rat)) (p234.lo) .lt,
  -- P235.normalization; P235: lambda=7/3, y=5687/6400: 6727119/10000000 < L_minus(1+(7/3)/(12158539/5000000)); L_plus(1+(7/3)/(972683/400000)) < 6727127/10000000.
  Comparison.ofRats ((0 : Rat)) (p235.lo) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 64 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Normalization006
