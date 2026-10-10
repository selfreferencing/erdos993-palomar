module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality015

def records : List Comparison := [
  -- P225.lower.lambda; P225: lambda=7/3, y=121/200: 8216161/10000000 < L_minus(1+(7/3)/(4578131/2500000)); L_plus(1+(7/3)/(18312521/10000000)) < 8216170/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p225.lam) .eq,
  -- P225.lower.exp; P225: lambda=7/3, y=121/200: 8216161/10000000 < L_minus(1+(7/3)/(4578131/2500000)); L_plus(1+(7/3)/(18312521/10000000)) < 8216170/10000000.
  Comparison.ofRats (((4578131 : Rat) / (2500000 : Rat))) (e033.hi) .eq,
  -- P225.upper.lambda; P225: lambda=7/3, y=121/200: 8216161/10000000 < L_minus(1+(7/3)/(4578131/2500000)); L_plus(1+(7/3)/(18312521/10000000)) < 8216170/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p225.lam) .eq,
  -- P225.upper.exp; P225: lambda=7/3, y=121/200: 8216161/10000000 < L_minus(1+(7/3)/(4578131/2500000)); L_plus(1+(7/3)/(18312521/10000000)) < 8216170/10000000.
  Comparison.ofRats (((18312521 : Rat) / (10000000 : Rat))) (e033.lo) .eq,
  -- P226.lower.lambda; P226: lambda=7/3, y=3/4: 7429783/10000000 < L_minus(1+(7/3)/(10585001/5000000)); L_plus(1+(7/3)/(21169999/10000000)) < 7429792/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p226.lam) .eq,
  -- P226.lower.exp; P226: lambda=7/3, y=3/4: 7429783/10000000 < L_minus(1+(7/3)/(10585001/5000000)); L_plus(1+(7/3)/(21169999/10000000)) < 7429792/10000000.
  Comparison.ofRats (((10585001 : Rat) / (5000000 : Rat))) (e053.hi) .eq,
  -- P226.upper.lambda; P226: lambda=7/3, y=3/4: 7429783/10000000 < L_minus(1+(7/3)/(10585001/5000000)); L_plus(1+(7/3)/(21169999/10000000)) < 7429792/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p226.lam) .eq,
  -- P226.upper.exp; P226: lambda=7/3, y=3/4: 7429783/10000000 < L_minus(1+(7/3)/(10585001/5000000)); L_plus(1+(7/3)/(21169999/10000000)) < 7429792/10000000.
  Comparison.ofRats (((21169999 : Rat) / (10000000 : Rat))) (e053.lo) .eq,
  -- P227.lower.lambda; P227: lambda=7/3, y=121/160: 7397063/10000000 < L_minus(1+(7/3)/(21302729/10000000)); L_plus(1+(7/3)/(10651363/5000000)) < 7397072/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p227.lam) .eq,
  -- P227.lower.exp; P227: lambda=7/3, y=121/160: 7397063/10000000 < L_minus(1+(7/3)/(21302729/10000000)); L_plus(1+(7/3)/(10651363/5000000)) < 7397072/10000000.
  Comparison.ofRats (((21302729 : Rat) / (10000000 : Rat))) (e054.hi) .eq,
  -- P227.upper.lambda; P227: lambda=7/3, y=121/160: 7397063/10000000 < L_minus(1+(7/3)/(21302729/10000000)); L_plus(1+(7/3)/(10651363/5000000)) < 7397072/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p227.lam) .eq,
  -- P227.upper.exp; P227: lambda=7/3, y=121/160: 7397063/10000000 < L_minus(1+(7/3)/(21302729/10000000)); L_plus(1+(7/3)/(10651363/5000000)) < 7397072/10000000.
  Comparison.ofRats (((10651363 : Rat) / (5000000 : Rat))) (e054.lo) .eq,
  -- P228.lower.lambda; P228: lambda=7/3, y=2541/3200: 7201184/10000000 < L_minus(1+(7/3)/(22123661/10000000)); L_plus(1+(7/3)/(11061829/5000000)) < 7201193/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p228.lam) .eq,
  -- P228.lower.exp; P228: lambda=7/3, y=2541/3200: 7201184/10000000 < L_minus(1+(7/3)/(22123661/10000000)); L_plus(1+(7/3)/(11061829/5000000)) < 7201193/10000000.
  Comparison.ofRats (((22123661 : Rat) / (10000000 : Rat))) (e060.hi) .eq,
  -- P228.upper.lambda; P228: lambda=7/3, y=2541/3200: 7201184/10000000 < L_minus(1+(7/3)/(22123661/10000000)); L_plus(1+(7/3)/(11061829/5000000)) < 7201193/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p228.lam) .eq,
  -- P228.upper.exp; P228: lambda=7/3, y=2541/3200: 7201184/10000000 < L_minus(1+(7/3)/(22123661/10000000)); L_plus(1+(7/3)/(11061829/5000000)) < 7201193/10000000.
  Comparison.ofRats (((11061829 : Rat) / (5000000 : Rat))) (e060.lo) .eq,
  -- P229.lower.lambda; P229: lambda=7/3, y=5203/6400: 7104584/10000000 < L_minus(1+(7/3)/(4509183/2000000)); L_plus(1+(7/3)/(2818239/1250000)) < 7104592/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p229.lam) .eq,
  -- P229.lower.exp; P229: lambda=7/3, y=5203/6400: 7104584/10000000 < L_minus(1+(7/3)/(4509183/2000000)); L_plus(1+(7/3)/(2818239/1250000)) < 7104592/10000000.
  Comparison.ofRats (((4509183 : Rat) / (2000000 : Rat))) (e064.hi) .eq,
  -- P229.upper.lambda; P229: lambda=7/3, y=5203/6400: 7104584/10000000 < L_minus(1+(7/3)/(4509183/2000000)); L_plus(1+(7/3)/(2818239/1250000)) < 7104592/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p229.lam) .eq,
  -- P229.upper.exp; P229: lambda=7/3, y=5203/6400: 7104584/10000000 < L_minus(1+(7/3)/(4509183/2000000)); L_plus(1+(7/3)/(2818239/1250000)) < 7104592/10000000.
  Comparison.ofRats (((2818239 : Rat) / (1250000 : Rat))) (e064.lo) .eq,
  -- P230.lower.lambda; P230: lambda=7/3, y=1331/1600: 7008877/10000000 < L_minus(1+(7/3)/(22976229/10000000)); L_plus(1+(7/3)/(11488113/5000000)) < 7008885/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p230.lam) .eq,
  -- P230.lower.exp; P230: lambda=7/3, y=1331/1600: 7008877/10000000 < L_minus(1+(7/3)/(22976229/10000000)); L_plus(1+(7/3)/(11488113/5000000)) < 7008885/10000000.
  Comparison.ofRats (((22976229 : Rat) / (10000000 : Rat))) (e068.hi) .eq,
  -- P230.upper.lambda; P230: lambda=7/3, y=1331/1600: 7008877/10000000 < L_minus(1+(7/3)/(22976229/10000000)); L_plus(1+(7/3)/(11488113/5000000)) < 7008885/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p230.lam) .eq,
  -- P230.upper.exp; P230: lambda=7/3, y=1331/1600: 7008877/10000000 < L_minus(1+(7/3)/(22976229/10000000)); L_plus(1+(7/3)/(11488113/5000000)) < 7008885/10000000.
  Comparison.ofRats (((11488113 : Rat) / (5000000 : Rat))) (e068.lo) .eq,
  -- P231.lower.lambda; P231: lambda=7/3, y=1089/1280: 6914064/10000000 < L_minus(1+(7/3)/(5853689/2500000)); L_plus(1+(7/3)/(23414753/10000000)) < 6914073/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p231.lam) .eq,
  -- P231.lower.exp; P231: lambda=7/3, y=1089/1280: 6914064/10000000 < L_minus(1+(7/3)/(5853689/2500000)); L_plus(1+(7/3)/(23414753/10000000)) < 6914073/10000000.
  Comparison.ofRats (((5853689 : Rat) / (2500000 : Rat))) (e072.hi) .eq,
  -- P231.upper.lambda; P231: lambda=7/3, y=1089/1280: 6914064/10000000 < L_minus(1+(7/3)/(5853689/2500000)); L_plus(1+(7/3)/(23414753/10000000)) < 6914073/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p231.lam) .eq,
  -- P231.upper.exp; P231: lambda=7/3, y=1089/1280: 6914064/10000000 < L_minus(1+(7/3)/(5853689/2500000)); L_plus(1+(7/3)/(23414753/10000000)) < 6914073/10000000.
  Comparison.ofRats (((23414753 : Rat) / (10000000 : Rat))) (e072.lo) .eq,
  -- P232.lower.lambda; P232: lambda=7/3, y=11011/12800: 6866992/10000000 < L_minus(1+(7/3)/(5909287/2500000)); L_plus(1+(7/3)/(4727429/2000000)) < 6867001/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p232.lam) .eq,
  -- P232.lower.exp; P232: lambda=7/3, y=11011/12800: 6866992/10000000 < L_minus(1+(7/3)/(5909287/2500000)); L_plus(1+(7/3)/(4727429/2000000)) < 6867001/10000000.
  Comparison.ofRats (((5909287 : Rat) / (2500000 : Rat))) (e075.hi) .eq,
  -- P232.upper.lambda; P232: lambda=7/3, y=11011/12800: 6866992/10000000 < L_minus(1+(7/3)/(5909287/2500000)); L_plus(1+(7/3)/(4727429/2000000)) < 6867001/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p232.lam) .eq,
  -- P232.upper.exp; P232: lambda=7/3, y=11011/12800: 6866992/10000000 < L_minus(1+(7/3)/(5909287/2500000)); L_plus(1+(7/3)/(4727429/2000000)) < 6867001/10000000.
  Comparison.ofRats (((4727429 : Rat) / (2000000 : Rat))) (e075.lo) .eq,
  -- P233.lower.lambda; P233: lambda=7/3, y=2783/3200: 6820145/10000000 < L_minus(1+(7/3)/(5965413/2500000)); L_plus(1+(7/3)/(23861649/10000000)) < 6820153/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p233.lam) .eq,
  -- P233.lower.exp; P233: lambda=7/3, y=2783/3200: 6820145/10000000 < L_minus(1+(7/3)/(5965413/2500000)); L_plus(1+(7/3)/(23861649/10000000)) < 6820153/10000000.
  Comparison.ofRats (((5965413 : Rat) / (2500000 : Rat))) (e077.hi) .eq,
  -- P233.upper.lambda; P233: lambda=7/3, y=2783/3200: 6820145/10000000 < L_minus(1+(7/3)/(5965413/2500000)); L_plus(1+(7/3)/(23861649/10000000)) < 6820153/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p233.lam) .eq,
  -- P233.upper.exp; P233: lambda=7/3, y=2783/3200: 6820145/10000000 < L_minus(1+(7/3)/(5965413/2500000)); L_plus(1+(7/3)/(23861649/10000000)) < 6820153/10000000.
  Comparison.ofRats (((23861649 : Rat) / (10000000 : Rat))) (e077.lo) .eq,
  -- P234.lower.lambda; P234: lambda=7/3, y=11253/12800: 6773520/10000000 < L_minus(1+(7/3)/(24088289/10000000)); L_plus(1+(7/3)/(12044143/5000000)) < 6773528/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p234.lam) .eq,
  -- P234.lower.exp; P234: lambda=7/3, y=11253/12800: 6773520/10000000 < L_minus(1+(7/3)/(24088289/10000000)); L_plus(1+(7/3)/(12044143/5000000)) < 6773528/10000000.
  Comparison.ofRats (((24088289 : Rat) / (10000000 : Rat))) (e079.hi) .eq,
  -- P234.upper.lambda; P234: lambda=7/3, y=11253/12800: 6773520/10000000 < L_minus(1+(7/3)/(24088289/10000000)); L_plus(1+(7/3)/(12044143/5000000)) < 6773528/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p234.lam) .eq,
  -- P234.upper.exp; P234: lambda=7/3, y=11253/12800: 6773520/10000000 < L_minus(1+(7/3)/(24088289/10000000)); L_plus(1+(7/3)/(12044143/5000000)) < 6773528/10000000.
  Comparison.ofRats (((12044143 : Rat) / (5000000 : Rat))) (e079.lo) .eq,
  -- P235.lower.lambda; P235: lambda=7/3, y=5687/6400: 6727119/10000000 < L_minus(1+(7/3)/(12158539/5000000)); L_plus(1+(7/3)/(972683/400000)) < 6727127/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p235.lam) .eq,
  -- P235.lower.exp; P235: lambda=7/3, y=5687/6400: 6727119/10000000 < L_minus(1+(7/3)/(12158539/5000000)); L_plus(1+(7/3)/(972683/400000)) < 6727127/10000000.
  Comparison.ofRats (((12158539 : Rat) / (5000000 : Rat))) (e080.hi) .eq,
  -- P235.upper.lambda; P235: lambda=7/3, y=5687/6400: 6727119/10000000 < L_minus(1+(7/3)/(12158539/5000000)); L_plus(1+(7/3)/(972683/400000)) < 6727127/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p235.lam) .eq,
  -- P235.upper.exp; P235: lambda=7/3, y=5687/6400: 6727119/10000000 < L_minus(1+(7/3)/(12158539/5000000)); L_plus(1+(7/3)/(972683/400000)) < 6727127/10000000.
  Comparison.ofRats (((972683 : Rat) / (400000 : Rat))) (e080.lo) .eq,
  -- P236.lower.lambda; P236: lambda=7/3, y=363/400: 6634986/10000000 < L_minus(1+(7/3)/(6195299/2500000)); L_plus(1+(7/3)/(24781193/10000000)) < 6634994/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p236.lam) .eq,
  -- P236.lower.exp; P236: lambda=7/3, y=363/400: 6634986/10000000 < L_minus(1+(7/3)/(6195299/2500000)); L_plus(1+(7/3)/(24781193/10000000)) < 6634994/10000000.
  Comparison.ofRats (((6195299 : Rat) / (2500000 : Rat))) (e084.hi) .eq,
  -- P236.upper.lambda; P236: lambda=7/3, y=363/400: 6634986/10000000 < L_minus(1+(7/3)/(6195299/2500000)); L_plus(1+(7/3)/(24781193/10000000)) < 6634994/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p236.lam) .eq,
  -- P236.upper.exp; P236: lambda=7/3, y=363/400: 6634986/10000000 < L_minus(1+(7/3)/(6195299/2500000)); L_plus(1+(7/3)/(24781193/10000000)) < 6634994/10000000.
  Comparison.ofRats (((24781193 : Rat) / (10000000 : Rat))) (e084.lo) .eq,
  -- P237.lower.lambda; P237: lambda=7/3, y=5929/6400: 6543746/10000000 < L_minus(1+(7/3)/(25254173/10000000)); L_plus(1+(7/3)/(2525417/1000000)) < 6543753/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p237.lam) .eq,
  -- P237.lower.exp; P237: lambda=7/3, y=5929/6400: 6543746/10000000 < L_minus(1+(7/3)/(25254173/10000000)); L_plus(1+(7/3)/(2525417/1000000)) < 6543753/10000000.
  Comparison.ofRats (((25254173 : Rat) / (10000000 : Rat))) (e087.hi) .eq,
  -- P237.upper.lambda; P237: lambda=7/3, y=5929/6400: 6543746/10000000 < L_minus(1+(7/3)/(25254173/10000000)); L_plus(1+(7/3)/(2525417/1000000)) < 6543753/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p237.lam) .eq,
  -- P237.upper.exp; P237: lambda=7/3, y=5929/6400: 6543746/10000000 < L_minus(1+(7/3)/(25254173/10000000)); L_plus(1+(7/3)/(2525417/1000000)) < 6543753/10000000.
  Comparison.ofRats (((2525417 : Rat) / (1000000 : Rat))) (e087.lo) .eq,
  -- P238.lower.lambda; P238: lambda=7/3, y=121/128: 6453398/10000000 < L_minus(1+(7/3)/(25736177/10000000)); L_plus(1+(7/3)/(12868087/5000000)) < 6453405/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p238.lam) .eq,
  -- P238.lower.exp; P238: lambda=7/3, y=121/128: 6453398/10000000 < L_minus(1+(7/3)/(25736177/10000000)); L_plus(1+(7/3)/(12868087/5000000)) < 6453405/10000000.
  Comparison.ofRats (((25736177 : Rat) / (10000000 : Rat))) (e089.hi) .eq,
  -- P238.upper.lambda; P238: lambda=7/3, y=121/128: 6453398/10000000 < L_minus(1+(7/3)/(25736177/10000000)); L_plus(1+(7/3)/(12868087/5000000)) < 6453405/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p238.lam) .eq,
  -- P238.upper.exp; P238: lambda=7/3, y=121/128: 6453398/10000000 < L_minus(1+(7/3)/(25736177/10000000)); L_plus(1+(7/3)/(12868087/5000000)) < 6453405/10000000.
  Comparison.ofRats (((12868087 : Rat) / (5000000 : Rat))) (e089.lo) .eq,
  -- P239.lower.lambda; P239: lambda=7/3, y=1573/1600: 6275376/10000000 < L_minus(1+(7/3)/(13363979/5000000)); L_plus(1+(7/3)/(5345591/2000000)) < 6275382/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p239.lam) .eq,
  -- P239.lower.exp; P239: lambda=7/3, y=1573/1600: 6275376/10000000 < L_minus(1+(7/3)/(13363979/5000000)); L_plus(1+(7/3)/(5345591/2000000)) < 6275382/10000000.
  Comparison.ofRats (((13363979 : Rat) / (5000000 : Rat))) (e092.hi) .eq,
  -- P239.upper.lambda; P239: lambda=7/3, y=1573/1600: 6275376/10000000 < L_minus(1+(7/3)/(13363979/5000000)); L_plus(1+(7/3)/(5345591/2000000)) < 6275382/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p239.lam) .eq,
  -- P239.upper.exp; P239: lambda=7/3, y=1573/1600: 6275376/10000000 < L_minus(1+(7/3)/(13363979/5000000)); L_plus(1+(7/3)/(5345591/2000000)) < 6275382/10000000.
  Comparison.ofRats (((5345591 : Rat) / (2000000 : Rat))) (e092.lo) .eq,
  -- P240.lower.lambda; P240: lambda=7/3, y=3267/3200: 6100912/10000000 < L_minus(1+(7/3)/(693949/250000)); L_plus(1+(7/3)/(27757957/10000000)) < 6100917/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p240.lam) .eq,
  -- P240.lower.exp; P240: lambda=7/3, y=3267/3200: 6100912/10000000 < L_minus(1+(7/3)/(693949/250000)); L_plus(1+(7/3)/(27757957/10000000)) < 6100917/10000000.
  Comparison.ofRats (((693949 : Rat) / (250000 : Rat))) (e096.hi) .eq,
  -- P240.upper.lambda; P240: lambda=7/3, y=3267/3200: 6100912/10000000 < L_minus(1+(7/3)/(693949/250000)); L_plus(1+(7/3)/(27757957/10000000)) < 6100917/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p240.lam) .eq,
  -- P240.upper.exp; P240: lambda=7/3, y=3267/3200: 6100912/10000000 < L_minus(1+(7/3)/(693949/250000)); L_plus(1+(7/3)/(27757957/10000000)) < 6100917/10000000.
  Comparison.ofRats (((27757957 : Rat) / (10000000 : Rat))) (e096.lo) .eq
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 64 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality015
