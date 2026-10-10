module

public import Erdos993Lean.Analytic.V213.ZeroTiltLaplaceRates
public import Erdos993Lean.Analytic.N44.Data.Params

/-! Ported to the Lean module system for the Palomar registry. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

/-! Literal reviewed current23 rate groups and55 input triples.
The definitions alone prove no inequality; every index correspondence is retained. -/

def groupLo (i : Nat) : Rat :=
  [(1/3), (9/25), (2/5), (9/20), (1/2), (11/20), (3/5), (13/20), (7/10), (3/4), (39/50), (87/100), (91/100), (23/25), (24/25), (99/100), (103/100), (26/25), (107/100), (5/4), (8/5), (19/10), (39/20)].getD i 0

def groupHi (i : Nat) : Rat :=
  [(9/25), (2/5), (9/20), (1/2), (11/20), (3/5), (13/20), (7/10), (3/4), (39/50), (87/100), (91/100), (23/25), (24/25), (99/100), (103/100), (26/25), (107/100), (5/4), (8/5), (19/10), (39/20), (7/3)].getD i 0

def groupBar (i : Nat) : Rat :=
  [(619/2500), (1309/5000), (2793/10000), (751/2500), (643/2000), (339/1000), (3531/10000), (459/1250), (953/2500), (1959/5000), (4129/10000), (171/400), (217/500), (871/2000), (441/1000), (889/2000), (449/1000), (901/2000), (907/2000), (37/80), (941/2000), (47/100), (1129/2500)].getD i 0

def groupMargin (i : Nat) : Nat :=
  [1542, 1479, 3705, 4944, 3833, 4194, 6032, 6135, 4772, 15794, 807, 2051, 1516, 1413, 1146, 1217, 1041, 548, 399, 3880, 880, 285, 6908].getD i 0

def groupOf (i : Nat) : Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 10, 10, 10, 11, 11, 11, 12, 13, 13, 13, 14, 14, 15, 15, 16, 17, 17, 18, 18, 18, 18, 18, 18, 18, 18, 18, 19, 19, 19, 19, 19, 19, 19, 20, 20, 20, 20, 20, 20, 21, 22, 22, 22, 22].getD i 0

def inputLo (i : Nat) : Rat :=
  [(1/3), (9/25), (2/5), (9/20), (1/2), (11/20), (3/5), (13/20), (7/10), (3/4), (39/50), (4/5), (21/25), (43/50), (87/100), (22/25), (89/100), (91/100), (23/25), (93/100), (47/50), (24/25), (97/100), (99/100), (1), (103/100), (26/25), (21/20), (107/100), (27/25), (11/10), (28/25), (57/50), (29/25), (59/50), (6/5), (49/40), (5/4), (13/10), (27/20), (7/5), (57/40), (29/20), (3/2), (8/5), (33/20), (17/10), (7/4), (9/5), (37/20), (19/10), (39/20), (2), (41/20), (9/4)].getD i 0

def inputHi (i : Nat) : Rat :=
  [(9/25), (2/5), (9/20), (1/2), (11/20), (3/5), (13/20), (7/10), (3/4), (39/50), (4/5), (21/25), (43/50), (87/100), (22/25), (89/100), (91/100), (23/25), (93/100), (47/50), (24/25), (97/100), (99/100), (1), (103/100), (26/25), (21/20), (107/100), (27/25), (11/10), (28/25), (57/50), (29/25), (59/50), (6/5), (49/40), (5/4), (13/10), (27/20), (7/5), (57/40), (29/20), (3/2), (8/5), (33/20), (17/10), (7/4), (9/5), (37/20), (19/10), (39/20), (2), (41/20), (9/4), (7/3)].getD i 0

def inputRate (i : Nat) : Rat :=
  [(619/2500), (1309/5000), (2793/10000), (751/2500), (643/2000), (339/1000), (3531/10000), (459/1250), (953/2500), (1959/5000), (817/2000), (4059/10000), (4129/10000), (4129/10000), (171/400), (4199/10000), (851/2000), (217/500), (871/2000), (173/400), (871/2000), (441/1000), (879/2000), (889/2000), (881/2000), (449/1000), (901/2000), (449/1000), (907/2000), (113/250), (907/2000), (4481/10000), (4481/10000), (1129/2500), (1129/2500), (1129/2500), (1129/2500), (4551/10000), (23/50), (37/80), (4481/10000), (4481/10000), (4481/10000), (1129/2500), (939/2000), (47/100), (941/2000), (941/2000), (47/100), (47/100), (47/100), (2223/5000), (2223/5000), (269/625), (1129/2500)].getD i 0


end Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.groupLo
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.groupLo
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.groupHi
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.groupHi
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.groupBar
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.groupBar
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.groupMargin
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.groupMargin
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.groupOf
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.groupOf
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.inputLo
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.inputLo
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.inputHi
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.inputHi
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.inputRate
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.inputRate
