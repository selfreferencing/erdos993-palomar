module

public import Erdos993Lean.Analytic.V213.FiberInputRouteData
public import Erdos993Lean.Analytic.V213.FiberWindowRows

/-!
Accepted F14 exact logarithm bounds, six input-rate slacks and ten corners,
and F13 five class corners/eight weighted-window tests. Printed identity
is authoritative; complete formula witnesses are checked separately.
C1/C2 ell leaves are coupled endpoint values, not common lower rates.
Source: Eq89.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

inductive FiberCornerLogIdentity where
  | y29_20 | y3_2 | y8_5 | y53_25 | y54_25 | y9_4 | y12_5 | y13_5 | y11_4 | y29_10 | y61_20 | y13_4 | y10_3

inductive FiberCornerRateIdentity where
  | iota0 | iota1 | iota2 | iota3 | iota4 | iota5

inductive FiberRateCornerIdentity where
  | input30 | w1 | w2 | c1 | c2 | c4 | c5 | c6 | c7 | c8

inductive FiberWindowCornerIdentity where
  | c4 | c5 | c6 | c7 | c8

inductive FiberWindowWeightIdentity where
  | window3 | window4 | window5 | window6 | window7 | window8 | window9 | window10

structure FiberCornerLogRow where
  printed : String
  n : ℕ
  y : lowMeanFraction
  L : lowMeanFraction
  gap : lowMeanFraction
  upper : lowMeanFraction

structure FiberCornerRateRow where
  printed : String
  input : FiberInputIdentity
  base : lowMeanFraction
  slope : lowMeanFraction
  ell0 : lowMeanFraction
  lambda_hi : lowMeanFraction
  slack : lowMeanFraction

structure FiberRateCornerRow where
  printed : String
  ell : lowMeanFraction
  L : lowMeanFraction
  ts : lowMeanFraction
  gap : lowMeanFraction

structure FiberWindowCornerRow where
  printed : String
  outerClass : FiberOuterClassIdentity
  mu_c : lowMeanFraction
  ell_c : lowMeanFraction
  L_c : lowMeanFraction
  Z_W : lowMeanFraction
  epsilon_W : lowMeanFraction

structure FiberWindowWeightRow where
  printed : String
  window : FiberWindowIdentity
  corner : FiberWindowCornerIdentity
  n : ℕ
  y : lowMeanFraction
  upper : lowMeanFraction
  gap : lowMeanFraction
  epsilon : lowMeanFraction

def fiberCornerLogById : FiberCornerLogIdentity → FiberCornerLogRow
  | .y29_20 => ⟨"F14:log:y=29/20", 0, (29, 20), (929, 2500), (1, 100000), (852255002601, 2293699021880)⟩
  | .y3_2 => ⟨"F14:log:y=3/2", 0, (3, 2), (203, 500), (1, 10000), (177391, 437500)⟩
  | .y8_5 => ⟨"F14:log:y=8/5", 0, (8, 5), (471, 1000), (1, 10000), (97725099, 207924080)⟩
  | .y53_25 => ⟨"F14:log:y=53/25", 1, (53, 25), (94, 125), (1, 10000), (2019998592938581, 2688066759783125)⟩
  | .y54_25 => ⟨"F14:log:y=54/25", 1, (54, 25), (771, 1000), (1, 10000), (270227856257, 350871885000)⟩
  | .y9_4 => ⟨"F14:log:y=9/4", 1, (9, 4), (811, 1000), (1, 1000000), (725432362237, 894509910000)⟩
  | .y12_5 => ⟨"F14:log:y=12/5", 1, (12, 5), (219, 250), (1, 10000), (1850672542, 2113794375)⟩
  | .y13_5 => ⟨"F14:log:y=13/5", 1, (13, 5), (239, 250), (1, 10000), (349800551626, 366067008125)⟩
  | .y11_4 => ⟨"F14:log:y=11/4", 1, (11, 4), (253, 250), (1, 10000), (1928815197511, 1906596230000)⟩
  | .y29_10 => ⟨"F14:log:y=29/10", 1, (29, 10), (213, 200), (1, 10000), (305280895571027, 286712377735000)⟩
  | .y61_20 => ⟨"F14:log:y=61/20", 1, (61, 20), (279, 250), (1, 10000), (7149691567748227, 6411161305610000)⟩
  | .y13_4 => ⟨"F14:log:y=13/4", 1, (13, 4), (1179, 1000), (1, 10000), (4380705848137, 3716531910000)⟩
  | .y10_3 => ⟨"F14:log:y=10/3", 1, (10, 3), (241, 200), (1, 10000), (1348509, 1120000)⟩

def fiberCornerRateById : FiberCornerRateIdentity → FiberCornerRateRow
  | .iota0 => ⟨"F14:rate:iota=0", .iota_0, (243, 2000), (7, 20), (619, 2500), (9, 25), (1, 10000)⟩
  | .iota1 => ⟨"F14:rate:iota=1", .iota_1, (243, 2000), (7, 20), (1309, 5000), (2, 5), (3, 10000)⟩
  | .iota2 => ⟨"F14:rate:iota=2", .iota_2, (243, 2000), (7, 20), (2793, 10000), (9, 20), (3, 10000)⟩
  | .iota3 => ⟨"F14:rate:iota=3", .iota_3, (27, 250), (48, 125), (751, 2500), (1, 2), (1, 2500)⟩
  | .iota4 => ⟨"F14:rate:iota=4", .iota_4, (27, 250), (48, 125), (643, 2000), (11, 20), (23, 10000)⟩
  | .iota5 => ⟨"F14:rate:iota=5", .iota_5, (27, 250), (48, 125), (339, 1000), (3, 5), (3, 5000)⟩

def fiberRateCornerById : FiberRateCornerIdentity → FiberRateCornerRow
  | .input30 => ⟨"F14:corner:30", (907, 2000), (94, 125), (3, 5), (23, 10000)⟩
  | .w1 => ⟨"F14:corner:W1", (4481, 10000), (771, 1000), (29, 50), (23, 25000)⟩
  | .w2 => ⟨"F14:corner:W2", (1129, 2500), (811, 1000), (11, 20), (111, 20000)⟩
  | .c1 => ⟨"F14:corner:C1", (279, 1000), (929, 2500), (3, 5), (1401, 25000)⟩
  | .c2 => ⟨"F14:corner:C2", (423, 1250), (471, 1000), (69, 100), (1341, 100000)⟩
  | .c4 => ⟨"F14:corner:C4", (939, 2000), (253, 250), (21, 50), (2223, 50000)⟩
  | .c5 => ⟨"F14:corner:C5", (47, 100), (213, 200), (2, 5), (11, 250)⟩
  | .c6 => ⟨"F14:corner:C6", (2223, 5000), (279, 250), (9, 25), (1071, 25000)⟩
  | .c7 => ⟨"F14:corner:C7", (269, 625), (1179, 1000), (33, 100), (4133, 100000)⟩
  | .c8 => ⟨"F14:corner:C8", (1129, 2500), (241, 200), (3, 10), (901, 10000)⟩

def fiberWindowCornerById : FiberWindowCornerIdentity → FiberWindowCornerRow
  | .c4 => ⟨"F13:corner:C4", .c4, (40, 1), (939, 2000), (253, 250), (3, 100), (1, 100)⟩
  | .c5 => ⟨"F13:corner:C5", .c5, (50, 1), (47, 100), (213, 200), (11, 100), (1, 1000)⟩
  | .c6 => ⟨"F13:corner:C6", .c6, (50, 1), (2223, 5000), (279, 250), (3, 50), (1, 100)⟩
  | .c7 => ⟨"F13:corner:C7", .c7, (50, 1), (269, 625), (1179, 1000), (1, 10), (1, 100)⟩
  | .c8 => ⟨"F13:corner:C8", .c8, (50, 1), (1129, 2500), (241, 200), (1, 25), (1, 100)⟩

def fiberWindowWeightById : FiberWindowWeightIdentity → FiberWindowWeightRow
  | .window3 => ⟨"F13:weight=3", .window3, .c4, 3, (635, 57), (1888205844119864794407683, 783249938736326515230000), (138844997329748227007557, 783249938736326515230000), (1, 100)⟩
  | .window4 => ⟨"F13:weight=4", .window4, .c4, 1, (423, 200), (16749883888403075177447, 22359782725832312460000), (23014753711217109301417, 22359782725832312460000), (1, 100)⟩
  | .window5 => ⟨"F13:weight=5", .window5, .c5, 3, (98, 11), (287055675709496347, 131241610868445000), (1675868201082653, 131241610868445000), (1, 1000)⟩
  | .window6 => ⟨"F13:weight=6", .window6, .c6, 4, (29047, 1200), (162621369465902354010638902026686639, 51029595776900002421003075810880000), (32107568018748055227908835267631441, 51029595776900002421003075810880000), (1, 100)⟩
  | .window7 => ⟨"F13:weight=7", .window7, .c6, 3, (803, 100), (4957947951978136339969827, 2379803990332758956120000), (139592195314633344039213, 2379803990332758956120000), (1, 100)⟩
  | .window8 => ⟨"F13:weight=8", .window8, .c7, 5, (3959, 100), (61348833563732638832725680739, 16676132309016971495989984000), (2604133841347446854395907901, 16676132309016971495989984000), (1, 100)⟩
  | .window9 => ⟨"F13:weight=9", .window9, .c7, 2, (14899, 2000), (105498525242707183469866189262279, 52532459293869207223211536560000), (3059801888073533256900451038961, 52532459293869207223211536560000), (1, 100)⟩
  | .window10 => ⟨"F13:weight=10", .window10, .c8, 6, (3263, 40), (430787672720313143032486830019, 97865369086444200614056320000), (10095815014117980733836891581, 97865369086444200614056320000), (1, 100)⟩

def fiberCornerLogIdentityAt : ℕ → FiberCornerLogIdentity
  | 0 => .y29_20
  | 1 => .y3_2
  | 2 => .y8_5
  | 3 => .y53_25
  | 4 => .y54_25
  | 5 => .y9_4
  | 6 => .y12_5
  | 7 => .y13_5
  | 8 => .y11_4
  | 9 => .y29_10
  | 10 => .y61_20
  | 11 => .y13_4
  | _ => .y10_3

def fiberCornerLogIndex : FiberCornerLogIdentity → ℕ
  | .y29_20 => 0
  | .y3_2 => 1
  | .y8_5 => 2
  | .y53_25 => 3
  | .y54_25 => 4
  | .y9_4 => 5
  | .y12_5 => 6
  | .y13_5 => 7
  | .y11_4 => 8
  | .y29_10 => 9
  | .y61_20 => 10
  | .y13_4 => 11
  | .y10_3 => 12

def fiberCornerLogPrinted : FiberCornerLogIdentity → String
  | .y29_20 => "F14:log:y=29/20"
  | .y3_2 => "F14:log:y=3/2"
  | .y8_5 => "F14:log:y=8/5"
  | .y53_25 => "F14:log:y=53/25"
  | .y54_25 => "F14:log:y=54/25"
  | .y9_4 => "F14:log:y=9/4"
  | .y12_5 => "F14:log:y=12/5"
  | .y13_5 => "F14:log:y=13/5"
  | .y11_4 => "F14:log:y=11/4"
  | .y29_10 => "F14:log:y=29/10"
  | .y61_20 => "F14:log:y=61/20"
  | .y13_4 => "F14:log:y=13/4"
  | .y10_3 => "F14:log:y=10/3"

def fiberCornerRateIdentityAt : ℕ → FiberCornerRateIdentity
  | 0 => .iota0
  | 1 => .iota1
  | 2 => .iota2
  | 3 => .iota3
  | 4 => .iota4
  | _ => .iota5

def fiberCornerRateIndex : FiberCornerRateIdentity → ℕ
  | .iota0 => 0
  | .iota1 => 1
  | .iota2 => 2
  | .iota3 => 3
  | .iota4 => 4
  | .iota5 => 5

def fiberCornerRatePrinted : FiberCornerRateIdentity → String
  | .iota0 => "F14:rate:iota=0"
  | .iota1 => "F14:rate:iota=1"
  | .iota2 => "F14:rate:iota=2"
  | .iota3 => "F14:rate:iota=3"
  | .iota4 => "F14:rate:iota=4"
  | .iota5 => "F14:rate:iota=5"

def fiberRateCornerIdentityAt : ℕ → FiberRateCornerIdentity
  | 0 => .input30
  | 1 => .w1
  | 2 => .w2
  | 3 => .c1
  | 4 => .c2
  | 5 => .c4
  | 6 => .c5
  | 7 => .c6
  | 8 => .c7
  | _ => .c8

def fiberRateCornerIndex : FiberRateCornerIdentity → ℕ
  | .input30 => 0
  | .w1 => 1
  | .w2 => 2
  | .c1 => 3
  | .c2 => 4
  | .c4 => 5
  | .c5 => 6
  | .c6 => 7
  | .c7 => 8
  | .c8 => 9

def fiberRateCornerPrinted : FiberRateCornerIdentity → String
  | .input30 => "F14:corner:30"
  | .w1 => "F14:corner:W1"
  | .w2 => "F14:corner:W2"
  | .c1 => "F14:corner:C1"
  | .c2 => "F14:corner:C2"
  | .c4 => "F14:corner:C4"
  | .c5 => "F14:corner:C5"
  | .c6 => "F14:corner:C6"
  | .c7 => "F14:corner:C7"
  | .c8 => "F14:corner:C8"

def fiberWindowCornerIdentityAt : ℕ → FiberWindowCornerIdentity
  | 0 => .c4
  | 1 => .c5
  | 2 => .c6
  | 3 => .c7
  | _ => .c8

def fiberWindowCornerIndex : FiberWindowCornerIdentity → ℕ
  | .c4 => 0
  | .c5 => 1
  | .c6 => 2
  | .c7 => 3
  | .c8 => 4

def fiberWindowCornerPrinted : FiberWindowCornerIdentity → String
  | .c4 => "F13:corner:C4"
  | .c5 => "F13:corner:C5"
  | .c6 => "F13:corner:C6"
  | .c7 => "F13:corner:C7"
  | .c8 => "F13:corner:C8"

def fiberWindowWeightIdentityAt : ℕ → FiberWindowWeightIdentity
  | 0 => .window3
  | 1 => .window4
  | 2 => .window5
  | 3 => .window6
  | 4 => .window7
  | 5 => .window8
  | 6 => .window9
  | _ => .window10

def fiberWindowWeightIndex : FiberWindowWeightIdentity → ℕ
  | .window3 => 0
  | .window4 => 1
  | .window5 => 2
  | .window6 => 3
  | .window7 => 4
  | .window8 => 5
  | .window9 => 6
  | .window10 => 7

def fiberWindowWeightPrinted : FiberWindowWeightIdentity → String
  | .window3 => "F13:weight=3"
  | .window4 => "F13:weight=4"
  | .window5 => "F13:weight=5"
  | .window6 => "F13:weight=6"
  | .window7 => "F13:weight=7"
  | .window8 => "F13:weight=8"
  | .window9 => "F13:weight=9"
  | .window10 => "F13:weight=10"

end Erdos993Lean.Analytic.V213
