module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality011

def records : List Comparison := [
  -- P161.lower.lambda; P161: lambda=3/2, y=23/50: 6662510/10000000 < L_minus(1+(3/2)/(15840741/10000000)); L_plus(1+(3/2)/(7920369/5000000)) < 6662517/10000000.
  Comparison.ofRats (((3 : Rat) / (2 : Rat))) (p161.lam) .eq,
  -- P161.lower.exp; P161: lambda=3/2, y=23/50: 6662510/10000000 < L_minus(1+(3/2)/(15840741/10000000)); L_plus(1+(3/2)/(7920369/5000000)) < 6662517/10000000.
  Comparison.ofRats (((15840741 : Rat) / (10000000 : Rat))) (e018.hi) .eq,
  -- P161.upper.lambda; P161: lambda=3/2, y=23/50: 6662510/10000000 < L_minus(1+(3/2)/(15840741/10000000)); L_plus(1+(3/2)/(7920369/5000000)) < 6662517/10000000.
  Comparison.ofRats (((3 : Rat) / (2 : Rat))) (p161.lam) .eq,
  -- P161.upper.exp; P161: lambda=3/2, y=23/50: 6662510/10000000 < L_minus(1+(3/2)/(15840741/10000000)); L_plus(1+(3/2)/(7920369/5000000)) < 6662517/10000000.
  Comparison.ofRats (((7920369 : Rat) / (5000000 : Rat))) (e018.lo) .eq,
  -- P162.lower.lambda; P162: lambda=3/2, y=9/16: 6177087/10000000 < L_minus(1+(3/2)/(4387637/2500000)); L_plus(1+(3/2)/(3510109/2000000)) < 6177094/10000000.
  Comparison.ofRats (((3 : Rat) / (2 : Rat))) (p162.lam) .eq,
  -- P162.lower.exp; P162: lambda=3/2, y=9/16: 6177087/10000000 < L_minus(1+(3/2)/(4387637/2500000)); L_plus(1+(3/2)/(3510109/2000000)) < 6177094/10000000.
  Comparison.ofRats (((4387637 : Rat) / (2500000 : Rat))) (e029.hi) .eq,
  -- P162.upper.lambda; P162: lambda=3/2, y=9/16: 6177087/10000000 < L_minus(1+(3/2)/(4387637/2500000)); L_plus(1+(3/2)/(3510109/2000000)) < 6177094/10000000.
  Comparison.ofRats (((3 : Rat) / (2 : Rat))) (p162.lam) .eq,
  -- P162.upper.exp; P162: lambda=3/2, y=9/16: 6177087/10000000 < L_minus(1+(3/2)/(4387637/2500000)); L_plus(1+(3/2)/(3510109/2000000)) < 6177094/10000000.
  Comparison.ofRats (((3510109 : Rat) / (2000000 : Rat))) (e029.lo) .eq,
  -- P163.lower.lambda; P163: lambda=3/2, y=21/32: 5755956/10000000 < L_minus(1+(3/2)/(9637753/5000000)); L_plus(1+(3/2)/(19275503/10000000)) < 5755961/10000000.
  Comparison.ofRats (((3 : Rat) / (2 : Rat))) (p163.lam) .eq,
  -- P163.lower.exp; P163: lambda=3/2, y=21/32: 5755956/10000000 < L_minus(1+(3/2)/(9637753/5000000)); L_plus(1+(3/2)/(19275503/10000000)) < 5755961/10000000.
  Comparison.ofRats (((9637753 : Rat) / (5000000 : Rat))) (e040.hi) .eq,
  -- P163.upper.lambda; P163: lambda=3/2, y=21/32: 5755956/10000000 < L_minus(1+(3/2)/(9637753/5000000)); L_plus(1+(3/2)/(19275503/10000000)) < 5755961/10000000.
  Comparison.ofRats (((3 : Rat) / (2 : Rat))) (p163.lam) .eq,
  -- P163.upper.exp; P163: lambda=3/2, y=21/32: 5755956/10000000 < L_minus(1+(3/2)/(9637753/5000000)); L_plus(1+(3/2)/(19275503/10000000)) < 5755961/10000000.
  Comparison.ofRats (((19275503 : Rat) / (10000000 : Rat))) (e040.lo) .eq,
  -- P164.lower.lambda; P164: lambda=3/2, y=69/100: 5609655/10000000 < L_minus(1+(3/2)/(19937157/10000000)); L_plus(1+(3/2)/(9968577/5000000)) < 5609661/10000000.
  Comparison.ofRats (((3 : Rat) / (2 : Rat))) (p164.lam) .eq,
  -- P164.lower.exp; P164: lambda=3/2, y=69/100: 5609655/10000000 < L_minus(1+(3/2)/(19937157/10000000)); L_plus(1+(3/2)/(9968577/5000000)) < 5609661/10000000.
  Comparison.ofRats (((19937157 : Rat) / (10000000 : Rat))) (e045.hi) .eq,
  -- P164.upper.lambda; P164: lambda=3/2, y=69/100: 5609655/10000000 < L_minus(1+(3/2)/(19937157/10000000)); L_plus(1+(3/2)/(9968577/5000000)) < 5609661/10000000.
  Comparison.ofRats (((3 : Rat) / (2 : Rat))) (p164.lam) .eq,
  -- P164.upper.exp; P164: lambda=3/2, y=69/100: 5609655/10000000 < L_minus(1+(3/2)/(19937157/10000000)); L_plus(1+(3/2)/(9968577/5000000)) < 5609661/10000000.
  Comparison.ofRats (((9968577 : Rat) / (5000000 : Rat))) (e045.lo) .eq,
  -- P165.lower.lambda; P165: lambda=3/2, y=299/400: 5366822/10000000 < L_minus(1+(3/2)/(21117143/10000000)); L_plus(1+(3/2)/(1055857/500000)) < 5366828/10000000.
  Comparison.ofRats (((3 : Rat) / (2 : Rat))) (p165.lam) .eq,
  -- P165.lower.exp; P165: lambda=3/2, y=299/400: 5366822/10000000 < L_minus(1+(3/2)/(21117143/10000000)); L_plus(1+(3/2)/(1055857/500000)) < 5366828/10000000.
  Comparison.ofRats (((21117143 : Rat) / (10000000 : Rat))) (e052.hi) .eq,
  -- P165.upper.lambda; P165: lambda=3/2, y=299/400: 5366822/10000000 < L_minus(1+(3/2)/(21117143/10000000)); L_plus(1+(3/2)/(1055857/500000)) < 5366828/10000000.
  Comparison.ofRats (((3 : Rat) / (2 : Rat))) (p165.lam) .eq,
  -- P165.upper.exp; P165: lambda=3/2, y=299/400: 5366822/10000000 < L_minus(1+(3/2)/(21117143/10000000)); L_plus(1+(3/2)/(1055857/500000)) < 5366828/10000000.
  Comparison.ofRats (((1055857 : Rat) / (500000 : Rat))) (e052.lo) .eq,
  -- P166.lower.lambda; P166: lambda=3/2, y=3/4: 5356447/10000000 < L_minus(1+(3/2)/(10585001/5000000)); L_plus(1+(3/2)/(21169999/10000000)) < 5356452/10000000.
  Comparison.ofRats (((3 : Rat) / (2 : Rat))) (p166.lam) .eq,
  -- P166.lower.exp; P166: lambda=3/2, y=3/4: 5356447/10000000 < L_minus(1+(3/2)/(10585001/5000000)); L_plus(1+(3/2)/(21169999/10000000)) < 5356452/10000000.
  Comparison.ofRats (((10585001 : Rat) / (5000000 : Rat))) (e053.hi) .eq,
  -- P166.upper.lambda; P166: lambda=3/2, y=3/4: 5356447/10000000 < L_minus(1+(3/2)/(10585001/5000000)); L_plus(1+(3/2)/(21169999/10000000)) < 5356452/10000000.
  Comparison.ofRats (((3 : Rat) / (2 : Rat))) (p166.lam) .eq,
  -- P166.upper.exp; P166: lambda=3/2, y=3/4: 5356447/10000000 < L_minus(1+(3/2)/(10585001/5000000)); L_plus(1+(3/2)/(21169999/10000000)) < 5356452/10000000.
  Comparison.ofRats (((21169999 : Rat) / (10000000 : Rat))) (e053.lo) .eq,
  -- P167.lower.lambda; P167: lambda=3/2, y=161/200: 5132016/10000000 < L_minus(1+(3/2)/(22366967/10000000)); L_plus(1+(3/2)/(22366963/10000000)) < 5132022/10000000.
  Comparison.ofRats (((3 : Rat) / (2 : Rat))) (p167.lam) .eq,
  -- P167.lower.exp; P167: lambda=3/2, y=161/200: 5132016/10000000 < L_minus(1+(3/2)/(22366967/10000000)); L_plus(1+(3/2)/(22366963/10000000)) < 5132022/10000000.
  Comparison.ofRats (((22366967 : Rat) / (10000000 : Rat))) (e062.hi) .eq,
  -- P167.upper.lambda; P167: lambda=3/2, y=161/200: 5132016/10000000 < L_minus(1+(3/2)/(22366967/10000000)); L_plus(1+(3/2)/(22366963/10000000)) < 5132022/10000000.
  Comparison.ofRats (((3 : Rat) / (2 : Rat))) (p167.lam) .eq,
  -- P167.upper.exp; P167: lambda=3/2, y=161/200: 5132016/10000000 < L_minus(1+(3/2)/(22366967/10000000)); L_plus(1+(3/2)/(22366963/10000000)) < 5132022/10000000.
  Comparison.ofRats (((22366963 : Rat) / (10000000 : Rat))) (e062.lo) .eq,
  -- P168.lower.lambda; P168: lambda=3/2, y=27/32: 4978264/10000000 < L_minus(1+(3/2)/(11625349/5000000)); L_plus(1+(3/2)/(4650139/2000000)) < 4978269/10000000.
  Comparison.ofRats (((3 : Rat) / (2 : Rat))) (p168.lam) .eq,
  -- P168.lower.exp; P168: lambda=3/2, y=27/32: 4978264/10000000 < L_minus(1+(3/2)/(11625349/5000000)); L_plus(1+(3/2)/(4650139/2000000)) < 4978269/10000000.
  Comparison.ofRats (((11625349 : Rat) / (5000000 : Rat))) (e071.hi) .eq,
  -- P168.upper.lambda; P168: lambda=3/2, y=27/32: 4978264/10000000 < L_minus(1+(3/2)/(11625349/5000000)); L_plus(1+(3/2)/(4650139/2000000)) < 4978269/10000000.
  Comparison.ofRats (((3 : Rat) / (2 : Rat))) (p168.lam) .eq,
  -- P168.upper.exp; P168: lambda=3/2, y=27/32: 4978264/10000000 < L_minus(1+(3/2)/(11625349/5000000)); L_plus(1+(3/2)/(4650139/2000000)) < 4978269/10000000.
  Comparison.ofRats (((4650139 : Rat) / (2000000 : Rat))) (e071.lo) .eq,
  -- P169.lower.lambda; P169: lambda=3/2, y=23/25: 4686140/10000000 < L_minus(1+(3/2)/(5018581/2000000)); L_plus(1+(3/2)/(12546451/5000000)) < 4686145/10000000.
  Comparison.ofRats (((3 : Rat) / (2 : Rat))) (p169.lam) .eq,
  -- P169.lower.exp; P169: lambda=3/2, y=23/25: 4686140/10000000 < L_minus(1+(3/2)/(5018581/2000000)); L_plus(1+(3/2)/(12546451/5000000)) < 4686145/10000000.
  Comparison.ofRats (((5018581 : Rat) / (2000000 : Rat))) (e086.hi) .eq,
  -- P169.upper.lambda; P169: lambda=3/2, y=23/25: 4686140/10000000 < L_minus(1+(3/2)/(5018581/2000000)); L_plus(1+(3/2)/(12546451/5000000)) < 4686145/10000000.
  Comparison.ofRats (((3 : Rat) / (2 : Rat))) (p169.lam) .eq,
  -- P169.upper.exp; P169: lambda=3/2, y=23/25: 4686140/10000000 < L_minus(1+(3/2)/(5018581/2000000)); L_plus(1+(3/2)/(12546451/5000000)) < 4686145/10000000.
  Comparison.ofRats (((12546451 : Rat) / (5000000 : Rat))) (e086.lo) .eq,
  -- P170.lower.lambda; P170: lambda=3/2, y=15/16: 4621025/10000000 < L_minus(1+(3/2)/(3191987/1250000)); L_plus(1+(3/2)/(25535893/10000000)) < 4621030/10000000.
  Comparison.ofRats (((3 : Rat) / (2 : Rat))) (p170.lam) .eq,
  -- P170.lower.exp; P170: lambda=3/2, y=15/16: 4621025/10000000 < L_minus(1+(3/2)/(3191987/1250000)); L_plus(1+(3/2)/(25535893/10000000)) < 4621030/10000000.
  Comparison.ofRats (((3191987 : Rat) / (1250000 : Rat))) (e088.hi) .eq,
  -- P170.upper.lambda; P170: lambda=3/2, y=15/16: 4621025/10000000 < L_minus(1+(3/2)/(3191987/1250000)); L_plus(1+(3/2)/(25535893/10000000)) < 4621030/10000000.
  Comparison.ofRats (((3 : Rat) / (2 : Rat))) (p170.lam) .eq,
  -- P170.upper.exp; P170: lambda=3/2, y=15/16: 4621025/10000000 < L_minus(1+(3/2)/(3191987/1250000)); L_plus(1+(3/2)/(25535893/10000000)) < 4621030/10000000.
  Comparison.ofRats (((25535893 : Rat) / (10000000 : Rat))) (e088.lo) .eq,
  -- P171.lower.lambda; P171: lambda=3/2, y=33/32: 4284268/10000000 < L_minus(1+(3/2)/(5609139/2000000)); L_plus(1+(3/2)/(7011423/2500000)) < 4284274/10000000.
  Comparison.ofRats (((3 : Rat) / (2 : Rat))) (p171.lam) .eq,
  -- P171.lower.exp; P171: lambda=3/2, y=33/32: 4284268/10000000 < L_minus(1+(3/2)/(5609139/2000000)); L_plus(1+(3/2)/(7011423/2500000)) < 4284274/10000000.
  Comparison.ofRats (((5609139 : Rat) / (2000000 : Rat))) (e097.hi) .eq,
  -- P171.upper.lambda; P171: lambda=3/2, y=33/32: 4284268/10000000 < L_minus(1+(3/2)/(5609139/2000000)); L_plus(1+(3/2)/(7011423/2500000)) < 4284274/10000000.
  Comparison.ofRats (((3 : Rat) / (2 : Rat))) (p171.lam) .eq,
  -- P171.upper.exp; P171: lambda=3/2, y=33/32: 4284268/10000000 < L_minus(1+(3/2)/(5609139/2000000)); L_plus(1+(3/2)/(7011423/2500000)) < 4284274/10000000.
  Comparison.ofRats (((7011423 : Rat) / (2500000 : Rat))) (e097.lo) .eq,
  -- P172.lower.lambda; P172: lambda=3/2, y=9/8: 3967460/10000000 < L_minus(1+(3/2)/(3080217/1000000)); L_plus(1+(3/2)/(30802167/10000000)) < 3967466/10000000.
  Comparison.ofRats (((3 : Rat) / (2 : Rat))) (p172.lam) .eq,
  -- P172.lower.exp; P172: lambda=3/2, y=9/8: 3967460/10000000 < L_minus(1+(3/2)/(3080217/1000000)); L_plus(1+(3/2)/(30802167/10000000)) < 3967466/10000000.
  Comparison.ofRats (((3080217 : Rat) / (1000000 : Rat))) (e103.hi) .eq,
  -- P172.upper.lambda; P172: lambda=3/2, y=9/8: 3967460/10000000 < L_minus(1+(3/2)/(3080217/1000000)); L_plus(1+(3/2)/(30802167/10000000)) < 3967466/10000000.
  Comparison.ofRats (((3 : Rat) / (2 : Rat))) (p172.lam) .eq,
  -- P172.upper.exp; P172: lambda=3/2, y=9/8: 3967460/10000000 < L_minus(1+(3/2)/(3080217/1000000)); L_plus(1+(3/2)/(30802167/10000000)) < 3967466/10000000.
  Comparison.ofRats (((30802167 : Rat) / (10000000 : Rat))) (e103.lo) .eq,
  -- P173.lower.lambda; P173: lambda=3/2, y=39/32: 3670005/10000000 < L_minus(1+(3/2)/(16914783/5000000)); L_plus(1+(3/2)/(16914781/5000000)) < 3670011/10000000.
  Comparison.ofRats (((3 : Rat) / (2 : Rat))) (p173.lam) .eq,
  -- P173.lower.exp; P173: lambda=3/2, y=39/32: 3670005/10000000 < L_minus(1+(3/2)/(16914783/5000000)); L_plus(1+(3/2)/(16914781/5000000)) < 3670011/10000000.
  Comparison.ofRats (((16914783 : Rat) / (5000000 : Rat))) (e108.hi) .eq,
  -- P173.upper.lambda; P173: lambda=3/2, y=39/32: 3670005/10000000 < L_minus(1+(3/2)/(16914783/5000000)); L_plus(1+(3/2)/(16914781/5000000)) < 3670011/10000000.
  Comparison.ofRats (((3 : Rat) / (2 : Rat))) (p173.lam) .eq,
  -- P173.upper.exp; P173: lambda=3/2, y=39/32: 3670005/10000000 < L_minus(1+(3/2)/(16914783/5000000)); L_plus(1+(3/2)/(16914781/5000000)) < 3670011/10000000.
  Comparison.ofRats (((16914781 : Rat) / (5000000 : Rat))) (e108.lo) .eq,
  -- P174.lower.lambda; P174: lambda=3/2, y=21/16: 3391252/10000000 < L_minus(1+(3/2)/(37154509/10000000)); L_plus(1+(3/2)/(18577253/5000000)) < 3391257/10000000.
  Comparison.ofRats (((3 : Rat) / (2 : Rat))) (p174.lam) .eq,
  -- P174.lower.exp; P174: lambda=3/2, y=21/16: 3391252/10000000 < L_minus(1+(3/2)/(37154509/10000000)); L_plus(1+(3/2)/(18577253/5000000)) < 3391257/10000000.
  Comparison.ofRats (((37154509 : Rat) / (10000000 : Rat))) (e112.hi) .eq,
  -- P174.upper.lambda; P174: lambda=3/2, y=21/16: 3391252/10000000 < L_minus(1+(3/2)/(37154509/10000000)); L_plus(1+(3/2)/(18577253/5000000)) < 3391257/10000000.
  Comparison.ofRats (((3 : Rat) / (2 : Rat))) (p174.lam) .eq,
  -- P174.upper.exp; P174: lambda=3/2, y=21/16: 3391252/10000000 < L_minus(1+(3/2)/(37154509/10000000)); L_plus(1+(3/2)/(18577253/5000000)) < 3391257/10000000.
  Comparison.ofRats (((18577253 : Rat) / (5000000 : Rat))) (e112.lo) .eq,
  -- P175.lower.lambda; P175: lambda=3/2, y=45/32: 3130503/10000000 < L_minus(1+(3/2)/(20403123/5000000)); L_plus(1+(3/2)/(20403121/5000000)) < 3130509/10000000.
  Comparison.ofRats (((3 : Rat) / (2 : Rat))) (p175.lam) .eq,
  -- P175.lower.exp; P175: lambda=3/2, y=45/32: 3130503/10000000 < L_minus(1+(3/2)/(20403123/5000000)); L_plus(1+(3/2)/(20403121/5000000)) < 3130509/10000000.
  Comparison.ofRats (((20403123 : Rat) / (5000000 : Rat))) (e116.hi) .eq,
  -- P175.upper.lambda; P175: lambda=3/2, y=45/32: 3130503/10000000 < L_minus(1+(3/2)/(20403123/5000000)); L_plus(1+(3/2)/(20403121/5000000)) < 3130509/10000000.
  Comparison.ofRats (((3 : Rat) / (2 : Rat))) (p175.lam) .eq,
  -- P175.upper.exp; P175: lambda=3/2, y=45/32: 3130503/10000000 < L_minus(1+(3/2)/(20403123/5000000)); L_plus(1+(3/2)/(20403121/5000000)) < 3130509/10000000.
  Comparison.ofRats (((20403121 : Rat) / (5000000 : Rat))) (e116.lo) .eq,
  -- P176.lower.lambda; P176: lambda=3/2, y=3/2: 2887027/10000000 < L_minus(1+(3/2)/(22408447/5000000)); L_plus(1+(3/2)/(44816889/10000000)) < 2887032/10000000.
  Comparison.ofRats (((3 : Rat) / (2 : Rat))) (p176.lam) .eq,
  -- P176.lower.exp; P176: lambda=3/2, y=3/2: 2887027/10000000 < L_minus(1+(3/2)/(22408447/5000000)); L_plus(1+(3/2)/(44816889/10000000)) < 2887032/10000000.
  Comparison.ofRats (((22408447 : Rat) / (5000000 : Rat))) (e120.hi) .eq,
  -- P176.upper.lambda; P176: lambda=3/2, y=3/2: 2887027/10000000 < L_minus(1+(3/2)/(22408447/5000000)); L_plus(1+(3/2)/(44816889/10000000)) < 2887032/10000000.
  Comparison.ofRats (((3 : Rat) / (2 : Rat))) (p176.lam) .eq,
  -- P176.upper.exp; P176: lambda=3/2, y=3/2: 2887027/10000000 < L_minus(1+(3/2)/(22408447/5000000)); L_plus(1+(3/2)/(44816889/10000000)) < 2887032/10000000.
  Comparison.ofRats (((44816889 : Rat) / (10000000 : Rat))) (e120.lo) .eq
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 64 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality011
