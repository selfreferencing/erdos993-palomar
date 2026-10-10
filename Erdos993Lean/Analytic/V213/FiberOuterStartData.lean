module

public import Erdos993Lean.Analytic.V213.LowMeanIntegerShape

/-!
Accepted F05 four outer start rows. Printed typed
identities govern row and expression lookup. Every reduced arithmetic
witness is data only; the separate checker binds the full canonical
formulas, row leaves and printed thresholds before kernel consumption.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

inductive FiberOuterStartIdentity where
  | c3 | c4 | c5c6 | c7c8

inductive FiberOuterStartRole where
  | gain | rate | bonus | logarithm | target | gap

structure FiberOuterStartRow where
  printed : String
  n : lowMeanFraction
  a : lowMeanFraction
  sigma : lowMeanFraction
  b0 : lowMeanFraction
  beta0 : lowMeanFraction
  d_star : lowMeanFraction
  p_star : lowMeanFraction
  R_star : lowMeanFraction
  v_star : lowMeanFraction
  P : lowMeanFraction
  R : lowMeanFraction
  delta : lowMeanFraction
  f0 : lowMeanFraction
  printed_gap : lowMeanFraction
  logUpper : lowMeanFraction

def fiberOuterStartPrinted : FiberOuterStartIdentity → String
  | .c3 => "F05:start:C3"
  | .c4 => "F05:start:C4"
  | .c5c6 => "F05:start:C5,C6"
  | .c7c8 => "F05:start:C7,C8"

def fiberOuterStartById : FiberOuterStartIdentity → FiberOuterStartRow
  | .c3 => ⟨"F05:start:C3", (24, 1), (4, 25), (11, 25), (0, 1), (1, 2), (3, 5), (3, 10), (2, 3), (107, 60), (1513193930629, 4798272937500), (9064563384, 10730453125), (158, 261), (-782, 275), (1624159, 59173350), (5, 6)⟩
  | .c4 => ⟨"F05:start:C4", (18, 1), (9, 40), (21, 50), (3, 20), (3, 10), (9, 10), (2, 5), (2, 3), (143, 80), (7520029421, 18631940075), (33704929161, 43614743200), (2763, 3038), (-1863, 700), (14662997, 245045150), (7, 8)⟩
  | .c5c6 => ⟨"F05:start:C5,C6", (20, 1), (4, 15), (9, 25), (3, 10), (0, 1), (29, 20), (11, 20), (3, 4), (161, 80), (50835443, 91730100), (351439436, 461964195), (1524, 1045), (-493, 150), (15525156, 79560125), (41, 40)⟩
  | .c7c8 => ⟨"F05:start:C7,C8", (17, 1), (17, 50), (3, 10), (3, 10), (1, 1), (2, 1), (13, 20), (2, 3), (19, 8), (141280269, 217267600), (6283117193, 9297255000), (1547, 737), (-461, 60), (24833, 364004), (121, 100)⟩

def fiberOuterStartExpr_c3_gain : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (51, 20)
  let e1 : LowMeanIntegerExpr := .atom (1, 1)
  let e2 : LowMeanIntegerExpr := .atom (24, 1)
  let e3 : LowMeanIntegerExpr := .add (25, 1) e2 e1
  let e4 : LowMeanIntegerExpr := .atom (2, 1)
  let e5 : LowMeanIntegerExpr := .neg (-2, 1) e4
  let e6 : LowMeanIntegerExpr := .add (23, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .div (1, 23) e1 e6
  let e8 : LowMeanIntegerExpr := .neg (-1, 23) e7
  let e9 : LowMeanIntegerExpr := .add (1153, 460) e0 e8
  let e10 : LowMeanIntegerExpr := .div (1153, 11500) e9 e3
  let e11 : LowMeanIntegerExpr := .atom (4, 25)
  let e12 : LowMeanIntegerExpr := .pow (16, 625) e11 2
  let e13 : LowMeanIntegerExpr := .atom (3, 1)
  let e14 : LowMeanIntegerExpr := .neg (-16, 625) e12
  let e15 : LowMeanIntegerExpr := .add (609, 625) e1 e14
  let e16 : LowMeanIntegerExpr := .mul (1827, 625) e13 e15
  let e17 : LowMeanIntegerExpr := .div (16, 1827) e12 e16
  let e18 : LowMeanIntegerExpr := .neg (-16, 1827) e17
  let e19 : LowMeanIntegerExpr := .add (1811, 1827) e1 e18
  let e20 : LowMeanIntegerExpr := .mul (45275, 1827) e19 e3
  let e21 : LowMeanIntegerExpr := .atom (4, 1)
  let e22 : LowMeanIntegerExpr := .neg (-4, 1) e21
  let e23 : LowMeanIntegerExpr := .add (37967, 1827) e20 e22
  let e24 : LowMeanIntegerExpr := .pow (1441493089, 3337929) e23 2
  let e25 : LowMeanIntegerExpr := .mul (50, 1) e4 e3
  let e26 : LowMeanIntegerExpr := .div (1441493089, 166896450) e24 e25
  let e27 : LowMeanIntegerExpr := .neg (-1, 1) e1
  let e28 : LowMeanIntegerExpr := .add (24, 1) e3 e27
  let e29 : LowMeanIntegerExpr := .atom (6, 1)
  let e30 : LowMeanIntegerExpr := .mul (3654, 625) e29 e15
  let e31 : LowMeanIntegerExpr := .mul (84042, 625) e30 e6
  let e32 : LowMeanIntegerExpr := .div (2500, 14007) e28 e31
  let e33 : LowMeanIntegerExpr := .neg (-2500, 14007) e32
  let e34 : LowMeanIntegerExpr := .add (32469216047, 3838618350) e26 e33
  let e35 : LowMeanIntegerExpr := .mul (16, 25) e12 e3
  let e36 : LowMeanIntegerExpr := .atom (12, 1)
  let e37 : LowMeanIntegerExpr := .pow (370881, 390625) e15 2
  let e38 : LowMeanIntegerExpr := .mul (4450572, 390625) e36 e37
  let e39 : LowMeanIntegerExpr := .div (62500, 1112643) e35 e38
  let e40 : LowMeanIntegerExpr := .neg (-62500, 1112643) e39
  let e41 : LowMeanIntegerExpr := .add (32253591047, 3838618350) e34 e40
  let e42 : LowMeanIntegerExpr := .mul (258028728376, 1199568234375) e12 e41
  let e43 : LowMeanIntegerExpr := .add (1513193930629, 4798272937500) e10 e42
  e43

def fiberOuterStartExpr_c3_rate : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 1)
  let e1 : LowMeanIntegerExpr := .atom (4, 25)
  let e2 : LowMeanIntegerExpr := .pow (16, 625) e1 2
  let e3 : LowMeanIntegerExpr := .neg (-16, 625) e2
  let e4 : LowMeanIntegerExpr := .add (609, 625) e0 e3
  let e5 : LowMeanIntegerExpr := .atom (24, 1)
  let e6 : LowMeanIntegerExpr := .mul (14616, 625) e4 e5
  let e7 : LowMeanIntegerExpr := .add (25, 1) e5 e0
  let e8 : LowMeanIntegerExpr := .div (14616, 15625) e6 e7
  let e9 : LowMeanIntegerExpr := .atom (2, 1)
  let e10 : LowMeanIntegerExpr := .div (2, 25) e9 e7
  let e11 : LowMeanIntegerExpr := .atom (3, 1)
  let e12 : LowMeanIntegerExpr := .mul (1827, 625) e11 e4
  let e13 : LowMeanIntegerExpr := .div (16, 1827) e2 e12
  let e14 : LowMeanIntegerExpr := .add (4054, 45675) e10 e13
  let e15 : LowMeanIntegerExpr := .mul (48, 1) e9 e5
  let e16 : LowMeanIntegerExpr := .div (1, 48) e0 e15
  let e17 : LowMeanIntegerExpr := .neg (-1, 48) e16
  let e18 : LowMeanIntegerExpr := .add (47, 48) e0 e17
  let e19 : LowMeanIntegerExpr := .atom (6, 1)
  let e20 : LowMeanIntegerExpr := .pow (576, 1) e5 2
  let e21 : LowMeanIntegerExpr := .mul (3456, 1) e19 e20
  let e22 : LowMeanIntegerExpr := .div (1, 3456) e0 e21
  let e23 : LowMeanIntegerExpr := .neg (-1, 3456) e22
  let e24 : LowMeanIntegerExpr := .add (3383, 3456) e18 e23
  let e25 : LowMeanIntegerExpr := .div (1556736, 17168725) e14 e24
  let e26 : LowMeanIntegerExpr := .neg (-1556736, 17168725) e25
  let e27 : LowMeanIntegerExpr := .add (9064563384, 10730453125) e8 e26
  e27

def fiberOuterStartExpr_c3_bonus : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (4, 25)
  let e1 : LowMeanIntegerExpr := .pow (16, 625) e0 2
  let e2 : LowMeanIntegerExpr := .atom (1, 1)
  let e3 : LowMeanIntegerExpr := .neg (-16, 625) e1
  let e4 : LowMeanIntegerExpr := .add (609, 625) e2 e3
  let e5 : LowMeanIntegerExpr := .div (16, 609) e1 e4
  let e6 : LowMeanIntegerExpr := .atom (24, 1)
  let e7 : LowMeanIntegerExpr := .neg (-1, 1) e2
  let e8 : LowMeanIntegerExpr := .add (23, 1) e6 e7
  let e9 : LowMeanIntegerExpr := .div (1, 24) e2 e6
  let e10 : LowMeanIntegerExpr := .add (553, 24) e8 e9
  let e11 : LowMeanIntegerExpr := .mul (158, 261) e5 e10
  e11

def fiberOuterStartExpr_c3_logarithm : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (2, 1)
  let e1 : LowMeanIntegerExpr := .atom (1, 1)
  let e2 : LowMeanIntegerExpr := .atom (11, 25)
  let e3 : LowMeanIntegerExpr := .neg (-11, 25) e2
  let e4 : LowMeanIntegerExpr := .add (14, 25) e1 e3
  let e5 : LowMeanIntegerExpr := .add (36, 25) e1 e2
  let e6 : LowMeanIntegerExpr := .div (7, 18) e4 e5
  let e7 : LowMeanIntegerExpr := .pow (343, 5832) e6 3
  let e8 : LowMeanIntegerExpr := .atom (3, 1)
  let e9 : LowMeanIntegerExpr := .div (343, 17496) e7 e8
  let e10 : LowMeanIntegerExpr := .add (7147, 17496) e6 e9
  let e11 : LowMeanIntegerExpr := .pow (16807, 1889568) e6 5
  let e12 : LowMeanIntegerExpr := .atom (5, 1)
  let e13 : LowMeanIntegerExpr := .pow (49, 324) e6 2
  let e14 : LowMeanIntegerExpr := .neg (-49, 324) e13
  let e15 : LowMeanIntegerExpr := .add (275, 324) e1 e14
  let e16 : LowMeanIntegerExpr := .mul (1375, 324) e12 e15
  let e17 : LowMeanIntegerExpr := .div (16807, 8019000) e11 e16
  let e18 : LowMeanIntegerExpr := .add (4938773, 12028500) e10 e17
  let e19 : LowMeanIntegerExpr := .mul (4938773, 6014250) e0 e18
  e19

def fiberOuterStartExpr_c3_target : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (10, 1)
  let e1 : LowMeanIntegerExpr := .atom (1, 2)
  let e2 : LowMeanIntegerExpr := .add (21, 2) e0 e1
  let e3 : LowMeanIntegerExpr := .atom (9, 2)
  let e4 : LowMeanIntegerExpr := .atom (11, 25)
  let e5 : LowMeanIntegerExpr := .mul (99, 50) e3 e4
  let e6 : LowMeanIntegerExpr := .neg (-99, 50) e5
  let e7 : LowMeanIntegerExpr := .add (213, 25) e2 e6
  let e8 : LowMeanIntegerExpr := .add (5, 1) e3 e1
  let e9 : LowMeanIntegerExpr := .atom (0, 1)
  let e10 : LowMeanIntegerExpr := .neg (0, 1) e9
  let e11 : LowMeanIntegerExpr := .add (5, 1) e8 e10
  let e12 : LowMeanIntegerExpr := .div (125, 11) e11 e4
  let e13 : LowMeanIntegerExpr := .neg (-125, 11) e12
  let e14 : LowMeanIntegerExpr := .add (-782, 275) e7 e13
  e14

def fiberOuterStartExpr_c3_gap : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 1)
  let e1 : LowMeanIntegerExpr := .atom (3, 5)
  let e2 : LowMeanIntegerExpr := .add (8, 5) e0 e1
  let e3 : LowMeanIntegerExpr := .atom (2, 1)
  let e4 : LowMeanIntegerExpr := .atom (107, 60)
  let e5 : LowMeanIntegerExpr := .pow (11449, 3600) e4 2
  let e6 : LowMeanIntegerExpr := .atom (4, 1)
  let e7 : LowMeanIntegerExpr := .neg (-107, 60) e4
  let e8 : LowMeanIntegerExpr := .add (133, 60) e6 e7
  let e9 : LowMeanIntegerExpr := .atom (48, 1)
  let e10 : LowMeanIntegerExpr := .div (11449, 172800) e5 e9
  let e11 : LowMeanIntegerExpr := .add (394489, 172800) e8 e10
  let e12 : LowMeanIntegerExpr := .div (549552, 394489) e5 e11
  let e13 : LowMeanIntegerExpr := .mul (1099104, 394489) e3 e12
  let e14 : LowMeanIntegerExpr := .atom (2, 3)
  let e15 : LowMeanIntegerExpr := .div (1648656, 394489) e13 e14
  let e16 : LowMeanIntegerExpr := .neg (-1648656, 394489) e15
  let e17 : LowMeanIntegerExpr := .add (-5087368, 1972445) e2 e16
  let e18 : LowMeanIntegerExpr := .atom (24, 1)
  let e19 : LowMeanIntegerExpr := .neg (-2, 1) e3
  let e20 : LowMeanIntegerExpr := .add (22, 1) e18 e19
  let e21 : LowMeanIntegerExpr := .div (11, 12) e20 e18
  let e22 : LowMeanIntegerExpr := .atom (10, 1)
  let e23 : LowMeanIntegerExpr := .atom (1, 2)
  let e24 : LowMeanIntegerExpr := .add (21, 2) e22 e23
  let e25 : LowMeanIntegerExpr := .atom (9, 2)
  let e26 : LowMeanIntegerExpr := .atom (11, 25)
  let e27 : LowMeanIntegerExpr := .mul (99, 50) e25 e26
  let e28 : LowMeanIntegerExpr := .neg (-99, 50) e27
  let e29 : LowMeanIntegerExpr := .add (213, 25) e24 e28
  let e30 : LowMeanIntegerExpr := .add (5, 1) e25 e23
  let e31 : LowMeanIntegerExpr := .atom (0, 1)
  let e32 : LowMeanIntegerExpr := .neg (0, 1) e31
  let e33 : LowMeanIntegerExpr := .add (5, 1) e30 e32
  let e34 : LowMeanIntegerExpr := .div (125, 11) e33 e26
  let e35 : LowMeanIntegerExpr := .neg (-125, 11) e34
  let e36 : LowMeanIntegerExpr := .add (-782, 275) e29 e35
  let e37 : LowMeanIntegerExpr := .mul (-391, 150) e21 e36
  let e38 : LowMeanIntegerExpr := .neg (391, 150) e37
  let e39 : LowMeanIntegerExpr := .add (1624159, 59173350) e17 e38
  e39

def fiberOuterStartExpr_c4_gain : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (51, 20)
  let e1 : LowMeanIntegerExpr := .atom (1, 1)
  let e2 : LowMeanIntegerExpr := .atom (18, 1)
  let e3 : LowMeanIntegerExpr := .add (19, 1) e2 e1
  let e4 : LowMeanIntegerExpr := .atom (2, 1)
  let e5 : LowMeanIntegerExpr := .neg (-2, 1) e4
  let e6 : LowMeanIntegerExpr := .add (17, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .div (1, 17) e1 e6
  let e8 : LowMeanIntegerExpr := .neg (-1, 17) e7
  let e9 : LowMeanIntegerExpr := .add (847, 340) e0 e8
  let e10 : LowMeanIntegerExpr := .div (847, 6460) e9 e3
  let e11 : LowMeanIntegerExpr := .atom (9, 40)
  let e12 : LowMeanIntegerExpr := .pow (81, 1600) e11 2
  let e13 : LowMeanIntegerExpr := .atom (3, 1)
  let e14 : LowMeanIntegerExpr := .neg (-81, 1600) e12
  let e15 : LowMeanIntegerExpr := .add (1519, 1600) e1 e14
  let e16 : LowMeanIntegerExpr := .mul (4557, 1600) e13 e15
  let e17 : LowMeanIntegerExpr := .div (27, 1519) e12 e16
  let e18 : LowMeanIntegerExpr := .neg (-27, 1519) e17
  let e19 : LowMeanIntegerExpr := .add (1492, 1519) e1 e18
  let e20 : LowMeanIntegerExpr := .mul (28348, 1519) e19 e3
  let e21 : LowMeanIntegerExpr := .atom (4, 1)
  let e22 : LowMeanIntegerExpr := .neg (-4, 1) e21
  let e23 : LowMeanIntegerExpr := .add (22272, 1519) e20 e22
  let e24 : LowMeanIntegerExpr := .pow (496041984, 2307361) e23 2
  let e25 : LowMeanIntegerExpr := .mul (38, 1) e4 e3
  let e26 : LowMeanIntegerExpr := .div (248020992, 43839859) e24 e25
  let e27 : LowMeanIntegerExpr := .neg (-1, 1) e1
  let e28 : LowMeanIntegerExpr := .add (18, 1) e3 e27
  let e29 : LowMeanIntegerExpr := .atom (6, 1)
  let e30 : LowMeanIntegerExpr := .mul (4557, 800) e29 e15
  let e31 : LowMeanIntegerExpr := .mul (77469, 800) e30 e6
  let e32 : LowMeanIntegerExpr := .div (4800, 25823) e28 e31
  let e33 : LowMeanIntegerExpr := .neg (-4800, 25823) e32
  let e34 : LowMeanIntegerExpr := .add (4077824064, 745277603) e26 e33
  let e35 : LowMeanIntegerExpr := .mul (1539, 1600) e12 e3
  let e36 : LowMeanIntegerExpr := .atom (12, 1)
  let e37 : LowMeanIntegerExpr := .pow (2307361, 2560000) e15 2
  let e38 : LowMeanIntegerExpr := .mul (6922083, 640000) e36 e37
  let e39 : LowMeanIntegerExpr := .div (205200, 2307361) e35 e38
  let e40 : LowMeanIntegerExpr := .neg (-205200, 2307361) e39
  let e41 : LowMeanIntegerExpr := .add (4011544464, 745277603) e34 e40
  let e42 : LowMeanIntegerExpr := .mul (20308443849, 74527760300) e12 e41
  let e43 : LowMeanIntegerExpr := .add (7520029421, 18631940075) e10 e42
  e43

def fiberOuterStartExpr_c4_rate : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 1)
  let e1 : LowMeanIntegerExpr := .atom (9, 40)
  let e2 : LowMeanIntegerExpr := .pow (81, 1600) e1 2
  let e3 : LowMeanIntegerExpr := .neg (-81, 1600) e2
  let e4 : LowMeanIntegerExpr := .add (1519, 1600) e0 e3
  let e5 : LowMeanIntegerExpr := .atom (18, 1)
  let e6 : LowMeanIntegerExpr := .mul (13671, 800) e4 e5
  let e7 : LowMeanIntegerExpr := .add (19, 1) e5 e0
  let e8 : LowMeanIntegerExpr := .div (13671, 15200) e6 e7
  let e9 : LowMeanIntegerExpr := .atom (2, 1)
  let e10 : LowMeanIntegerExpr := .div (2, 19) e9 e7
  let e11 : LowMeanIntegerExpr := .atom (3, 1)
  let e12 : LowMeanIntegerExpr := .mul (4557, 1600) e11 e4
  let e13 : LowMeanIntegerExpr := .div (27, 1519) e2 e12
  let e14 : LowMeanIntegerExpr := .add (3551, 28861) e10 e13
  let e15 : LowMeanIntegerExpr := .mul (36, 1) e9 e5
  let e16 : LowMeanIntegerExpr := .div (1, 36) e0 e15
  let e17 : LowMeanIntegerExpr := .neg (-1, 36) e16
  let e18 : LowMeanIntegerExpr := .add (35, 36) e0 e17
  let e19 : LowMeanIntegerExpr := .atom (6, 1)
  let e20 : LowMeanIntegerExpr := .pow (324, 1) e5 2
  let e21 : LowMeanIntegerExpr := .mul (1944, 1) e19 e20
  let e22 : LowMeanIntegerExpr := .div (1, 1944) e0 e21
  let e23 : LowMeanIntegerExpr := .neg (-1, 1944) e22
  let e24 : LowMeanIntegerExpr := .add (1889, 1944) e18 e23
  let e25 : LowMeanIntegerExpr := .div (6903144, 54518429) e14 e24
  let e26 : LowMeanIntegerExpr := .neg (-6903144, 54518429) e25
  let e27 : LowMeanIntegerExpr := .add (33704929161, 43614743200) e8 e26
  e27

def fiberOuterStartExpr_c4_bonus : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (9, 40)
  let e1 : LowMeanIntegerExpr := .pow (81, 1600) e0 2
  let e2 : LowMeanIntegerExpr := .atom (1, 1)
  let e3 : LowMeanIntegerExpr := .neg (-81, 1600) e1
  let e4 : LowMeanIntegerExpr := .add (1519, 1600) e2 e3
  let e5 : LowMeanIntegerExpr := .div (81, 1519) e1 e4
  let e6 : LowMeanIntegerExpr := .atom (18, 1)
  let e7 : LowMeanIntegerExpr := .neg (-1, 1) e2
  let e8 : LowMeanIntegerExpr := .add (17, 1) e6 e7
  let e9 : LowMeanIntegerExpr := .div (1, 18) e2 e6
  let e10 : LowMeanIntegerExpr := .add (307, 18) e8 e9
  let e11 : LowMeanIntegerExpr := .mul (2763, 3038) e5 e10
  e11

def fiberOuterStartExpr_c4_logarithm : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (2, 1)
  let e1 : LowMeanIntegerExpr := .atom (1, 1)
  let e2 : LowMeanIntegerExpr := .atom (21, 50)
  let e3 : LowMeanIntegerExpr := .neg (-21, 50) e2
  let e4 : LowMeanIntegerExpr := .add (29, 50) e1 e3
  let e5 : LowMeanIntegerExpr := .add (71, 50) e1 e2
  let e6 : LowMeanIntegerExpr := .div (29, 71) e4 e5
  let e7 : LowMeanIntegerExpr := .pow (24389, 357911) e6 3
  let e8 : LowMeanIntegerExpr := .atom (3, 1)
  let e9 : LowMeanIntegerExpr := .div (24389, 1073733) e7 e8
  let e10 : LowMeanIntegerExpr := .add (462956, 1073733) e6 e9
  let e11 : LowMeanIntegerExpr := .pow (20511149, 1804229351) e6 5
  let e12 : LowMeanIntegerExpr := .atom (5, 1)
  let e13 : LowMeanIntegerExpr := .pow (841, 5041) e6 2
  let e14 : LowMeanIntegerExpr := .neg (-841, 5041) e13
  let e15 : LowMeanIntegerExpr := .add (4200, 5041) e1 e14
  let e16 : LowMeanIntegerExpr := .mul (21000, 5041) e12 e15
  let e17 : LowMeanIntegerExpr := .div (20511149, 7516131000) e11 e16
  let e18 : LowMeanIntegerExpr := .add (3261203149, 7516131000) e10 e17
  let e19 : LowMeanIntegerExpr := .mul (3261203149, 3758065500) e0 e18
  e19

def fiberOuterStartExpr_c4_target : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (10, 1)
  let e1 : LowMeanIntegerExpr := .atom (3, 10)
  let e2 : LowMeanIntegerExpr := .add (103, 10) e0 e1
  let e3 : LowMeanIntegerExpr := .atom (9, 2)
  let e4 : LowMeanIntegerExpr := .atom (21, 50)
  let e5 : LowMeanIntegerExpr := .mul (189, 100) e3 e4
  let e6 : LowMeanIntegerExpr := .neg (-189, 100) e5
  let e7 : LowMeanIntegerExpr := .add (841, 100) e2 e6
  let e8 : LowMeanIntegerExpr := .add (24, 5) e3 e1
  let e9 : LowMeanIntegerExpr := .atom (3, 20)
  let e10 : LowMeanIntegerExpr := .neg (-3, 20) e9
  let e11 : LowMeanIntegerExpr := .add (93, 20) e8 e10
  let e12 : LowMeanIntegerExpr := .div (155, 14) e11 e4
  let e13 : LowMeanIntegerExpr := .neg (-155, 14) e12
  let e14 : LowMeanIntegerExpr := .add (-1863, 700) e7 e13
  e14

def fiberOuterStartExpr_c4_gap : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 1)
  let e1 : LowMeanIntegerExpr := .atom (9, 10)
  let e2 : LowMeanIntegerExpr := .add (19, 10) e0 e1
  let e3 : LowMeanIntegerExpr := .atom (2, 1)
  let e4 : LowMeanIntegerExpr := .atom (143, 80)
  let e5 : LowMeanIntegerExpr := .pow (20449, 6400) e4 2
  let e6 : LowMeanIntegerExpr := .atom (4, 1)
  let e7 : LowMeanIntegerExpr := .neg (-143, 80) e4
  let e8 : LowMeanIntegerExpr := .add (177, 80) e6 e7
  let e9 : LowMeanIntegerExpr := .atom (48, 1)
  let e10 : LowMeanIntegerExpr := .div (20449, 307200) e5 e9
  let e11 : LowMeanIntegerExpr := .add (700129, 307200) e8 e10
  let e12 : LowMeanIntegerExpr := .div (981552, 700129) e5 e11
  let e13 : LowMeanIntegerExpr := .mul (1963104, 700129) e3 e12
  let e14 : LowMeanIntegerExpr := .atom (2, 3)
  let e15 : LowMeanIntegerExpr := .div (2944656, 700129) e13 e14
  let e16 : LowMeanIntegerExpr := .neg (-2944656, 700129) e15
  let e17 : LowMeanIntegerExpr := .add (-16144109, 7001290) e2 e16
  let e18 : LowMeanIntegerExpr := .atom (18, 1)
  let e19 : LowMeanIntegerExpr := .neg (-2, 1) e3
  let e20 : LowMeanIntegerExpr := .add (16, 1) e18 e19
  let e21 : LowMeanIntegerExpr := .div (8, 9) e20 e18
  let e22 : LowMeanIntegerExpr := .atom (10, 1)
  let e23 : LowMeanIntegerExpr := .atom (3, 10)
  let e24 : LowMeanIntegerExpr := .add (103, 10) e22 e23
  let e25 : LowMeanIntegerExpr := .atom (9, 2)
  let e26 : LowMeanIntegerExpr := .atom (21, 50)
  let e27 : LowMeanIntegerExpr := .mul (189, 100) e25 e26
  let e28 : LowMeanIntegerExpr := .neg (-189, 100) e27
  let e29 : LowMeanIntegerExpr := .add (841, 100) e24 e28
  let e30 : LowMeanIntegerExpr := .add (24, 5) e25 e23
  let e31 : LowMeanIntegerExpr := .atom (3, 20)
  let e32 : LowMeanIntegerExpr := .neg (-3, 20) e31
  let e33 : LowMeanIntegerExpr := .add (93, 20) e30 e32
  let e34 : LowMeanIntegerExpr := .div (155, 14) e33 e26
  let e35 : LowMeanIntegerExpr := .neg (-155, 14) e34
  let e36 : LowMeanIntegerExpr := .add (-1863, 700) e29 e35
  let e37 : LowMeanIntegerExpr := .mul (-414, 175) e21 e36
  let e38 : LowMeanIntegerExpr := .neg (414, 175) e37
  let e39 : LowMeanIntegerExpr := .add (14662997, 245045150) e17 e38
  e39

def fiberOuterStartExpr_c5c6_gain : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (51, 20)
  let e1 : LowMeanIntegerExpr := .atom (1, 1)
  let e2 : LowMeanIntegerExpr := .atom (20, 1)
  let e3 : LowMeanIntegerExpr := .add (21, 1) e2 e1
  let e4 : LowMeanIntegerExpr := .atom (2, 1)
  let e5 : LowMeanIntegerExpr := .neg (-2, 1) e4
  let e6 : LowMeanIntegerExpr := .add (19, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .div (1, 19) e1 e6
  let e8 : LowMeanIntegerExpr := .neg (-1, 19) e7
  let e9 : LowMeanIntegerExpr := .add (949, 380) e0 e8
  let e10 : LowMeanIntegerExpr := .div (949, 7980) e9 e3
  let e11 : LowMeanIntegerExpr := .atom (4, 15)
  let e12 : LowMeanIntegerExpr := .pow (16, 225) e11 2
  let e13 : LowMeanIntegerExpr := .atom (3, 1)
  let e14 : LowMeanIntegerExpr := .neg (-16, 225) e12
  let e15 : LowMeanIntegerExpr := .add (209, 225) e1 e14
  let e16 : LowMeanIntegerExpr := .mul (209, 75) e13 e15
  let e17 : LowMeanIntegerExpr := .div (16, 627) e12 e16
  let e18 : LowMeanIntegerExpr := .neg (-16, 627) e17
  let e19 : LowMeanIntegerExpr := .add (611, 627) e1 e18
  let e20 : LowMeanIntegerExpr := .mul (4277, 209) e19 e3
  let e21 : LowMeanIntegerExpr := .atom (4, 1)
  let e22 : LowMeanIntegerExpr := .neg (-4, 1) e21
  let e23 : LowMeanIntegerExpr := .add (3441, 209) e20 e22
  let e24 : LowMeanIntegerExpr := .pow (11840481, 43681) e23 2
  let e25 : LowMeanIntegerExpr := .mul (42, 1) e4 e3
  let e26 : LowMeanIntegerExpr := .div (3946827, 611534) e24 e25
  let e27 : LowMeanIntegerExpr := .neg (-1, 1) e1
  let e28 : LowMeanIntegerExpr := .add (20, 1) e3 e27
  let e29 : LowMeanIntegerExpr := .atom (6, 1)
  let e30 : LowMeanIntegerExpr := .mul (418, 75) e29 e15
  let e31 : LowMeanIntegerExpr := .mul (7942, 75) e30 e6
  let e32 : LowMeanIntegerExpr := .div (750, 3971) e28 e31
  let e33 : LowMeanIntegerExpr := .neg (-750, 3971) e32
  let e34 : LowMeanIntegerExpr := .add (3831327, 611534) e26 e33
  let e35 : LowMeanIntegerExpr := .mul (112, 75) e12 e3
  let e36 : LowMeanIntegerExpr := .atom (12, 1)
  let e37 : LowMeanIntegerExpr := .pow (43681, 50625) e15 2
  let e38 : LowMeanIntegerExpr := .mul (174724, 16875) e36 e37
  let e39 : LowMeanIntegerExpr := .div (6300, 43681) e35 e38
  let e40 : LowMeanIntegerExpr := .neg (-6300, 43681) e39
  let e41 : LowMeanIntegerExpr := .add (3743127, 611534) e34 e40
  let e42 : LowMeanIntegerExpr := .mul (3327224, 7644175) e12 e41
  let e43 : LowMeanIntegerExpr := .add (50835443, 91730100) e10 e42
  e43

def fiberOuterStartExpr_c5c6_rate : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 1)
  let e1 : LowMeanIntegerExpr := .atom (4, 15)
  let e2 : LowMeanIntegerExpr := .pow (16, 225) e1 2
  let e3 : LowMeanIntegerExpr := .neg (-16, 225) e2
  let e4 : LowMeanIntegerExpr := .add (209, 225) e0 e3
  let e5 : LowMeanIntegerExpr := .atom (20, 1)
  let e6 : LowMeanIntegerExpr := .mul (836, 45) e4 e5
  let e7 : LowMeanIntegerExpr := .add (21, 1) e5 e0
  let e8 : LowMeanIntegerExpr := .div (836, 945) e6 e7
  let e9 : LowMeanIntegerExpr := .atom (2, 1)
  let e10 : LowMeanIntegerExpr := .div (2, 21) e9 e7
  let e11 : LowMeanIntegerExpr := .atom (3, 1)
  let e12 : LowMeanIntegerExpr := .mul (209, 75) e11 e4
  let e13 : LowMeanIntegerExpr := .div (16, 627) e2 e12
  let e14 : LowMeanIntegerExpr := .add (530, 4389) e10 e13
  let e15 : LowMeanIntegerExpr := .mul (40, 1) e9 e5
  let e16 : LowMeanIntegerExpr := .div (1, 40) e0 e15
  let e17 : LowMeanIntegerExpr := .neg (-1, 40) e16
  let e18 : LowMeanIntegerExpr := .add (39, 40) e0 e17
  let e19 : LowMeanIntegerExpr := .atom (6, 1)
  let e20 : LowMeanIntegerExpr := .pow (400, 1) e5 2
  let e21 : LowMeanIntegerExpr := .mul (2400, 1) e19 e20
  let e22 : LowMeanIntegerExpr := .div (1, 2400) e0 e21
  let e23 : LowMeanIntegerExpr := .neg (-1, 2400) e22
  let e24 : LowMeanIntegerExpr := .add (2339, 2400) e18 e23
  let e25 : LowMeanIntegerExpr := .div (424000, 3421957) e14 e24
  let e26 : LowMeanIntegerExpr := .neg (-424000, 3421957) e25
  let e27 : LowMeanIntegerExpr := .add (351439436, 461964195) e8 e26
  e27

def fiberOuterStartExpr_c5c6_bonus : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (4, 15)
  let e1 : LowMeanIntegerExpr := .pow (16, 225) e0 2
  let e2 : LowMeanIntegerExpr := .atom (1, 1)
  let e3 : LowMeanIntegerExpr := .neg (-16, 225) e1
  let e4 : LowMeanIntegerExpr := .add (209, 225) e2 e3
  let e5 : LowMeanIntegerExpr := .div (16, 209) e1 e4
  let e6 : LowMeanIntegerExpr := .atom (20, 1)
  let e7 : LowMeanIntegerExpr := .neg (-1, 1) e2
  let e8 : LowMeanIntegerExpr := .add (19, 1) e6 e7
  let e9 : LowMeanIntegerExpr := .div (1, 20) e2 e6
  let e10 : LowMeanIntegerExpr := .add (381, 20) e8 e9
  let e11 : LowMeanIntegerExpr := .mul (1524, 1045) e5 e10
  e11

def fiberOuterStartExpr_c5c6_logarithm : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (2, 1)
  let e1 : LowMeanIntegerExpr := .atom (1, 1)
  let e2 : LowMeanIntegerExpr := .atom (9, 25)
  let e3 : LowMeanIntegerExpr := .neg (-9, 25) e2
  let e4 : LowMeanIntegerExpr := .add (16, 25) e1 e3
  let e5 : LowMeanIntegerExpr := .add (34, 25) e1 e2
  let e6 : LowMeanIntegerExpr := .div (8, 17) e4 e5
  let e7 : LowMeanIntegerExpr := .pow (512, 4913) e6 3
  let e8 : LowMeanIntegerExpr := .atom (3, 1)
  let e9 : LowMeanIntegerExpr := .div (512, 14739) e7 e8
  let e10 : LowMeanIntegerExpr := .add (7448, 14739) e6 e9
  let e11 : LowMeanIntegerExpr := .pow (32768, 1419857) e6 5
  let e12 : LowMeanIntegerExpr := .atom (5, 1)
  let e13 : LowMeanIntegerExpr := .pow (64, 289) e6 2
  let e14 : LowMeanIntegerExpr := .neg (-64, 289) e13
  let e15 : LowMeanIntegerExpr := .add (225, 289) e1 e14
  let e16 : LowMeanIntegerExpr := .mul (1125, 289) e12 e15
  let e17 : LowMeanIntegerExpr := .div (32768, 5527125) e11 e16
  let e18 : LowMeanIntegerExpr := .add (2825768, 5527125) e10 e17
  let e19 : LowMeanIntegerExpr := .mul (5651536, 5527125) e0 e18
  e19

def fiberOuterStartExpr_c5c6_target : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (10, 1)
  let e1 : LowMeanIntegerExpr := .atom (0, 1)
  let e2 : LowMeanIntegerExpr := .add (10, 1) e0 e1
  let e3 : LowMeanIntegerExpr := .atom (9, 2)
  let e4 : LowMeanIntegerExpr := .atom (9, 25)
  let e5 : LowMeanIntegerExpr := .mul (81, 50) e3 e4
  let e6 : LowMeanIntegerExpr := .neg (-81, 50) e5
  let e7 : LowMeanIntegerExpr := .add (419, 50) e2 e6
  let e8 : LowMeanIntegerExpr := .add (9, 2) e3 e1
  let e9 : LowMeanIntegerExpr := .atom (3, 10)
  let e10 : LowMeanIntegerExpr := .neg (-3, 10) e9
  let e11 : LowMeanIntegerExpr := .add (21, 5) e8 e10
  let e12 : LowMeanIntegerExpr := .div (35, 3) e11 e4
  let e13 : LowMeanIntegerExpr := .neg (-35, 3) e12
  let e14 : LowMeanIntegerExpr := .add (-493, 150) e7 e13
  e14

def fiberOuterStartExpr_c5c6_gap : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 1)
  let e1 : LowMeanIntegerExpr := .atom (29, 20)
  let e2 : LowMeanIntegerExpr := .add (49, 20) e0 e1
  let e3 : LowMeanIntegerExpr := .atom (2, 1)
  let e4 : LowMeanIntegerExpr := .atom (161, 80)
  let e5 : LowMeanIntegerExpr := .pow (25921, 6400) e4 2
  let e6 : LowMeanIntegerExpr := .atom (4, 1)
  let e7 : LowMeanIntegerExpr := .neg (-161, 80) e4
  let e8 : LowMeanIntegerExpr := .add (159, 80) e6 e7
  let e9 : LowMeanIntegerExpr := .atom (48, 1)
  let e10 : LowMeanIntegerExpr := .div (25921, 307200) e5 e9
  let e11 : LowMeanIntegerExpr := .add (636481, 307200) e8 e10
  let e12 : LowMeanIntegerExpr := .div (1244208, 636481) e5 e11
  let e13 : LowMeanIntegerExpr := .mul (2488416, 636481) e3 e12
  let e14 : LowMeanIntegerExpr := .atom (3, 4)
  let e15 : LowMeanIntegerExpr := .div (3317888, 636481) e13 e14
  let e16 : LowMeanIntegerExpr := .neg (-3317888, 636481) e15
  let e17 : LowMeanIntegerExpr := .add (-35170191, 12729620) e2 e16
  let e18 : LowMeanIntegerExpr := .atom (20, 1)
  let e19 : LowMeanIntegerExpr := .neg (-2, 1) e3
  let e20 : LowMeanIntegerExpr := .add (18, 1) e18 e19
  let e21 : LowMeanIntegerExpr := .div (9, 10) e20 e18
  let e22 : LowMeanIntegerExpr := .atom (10, 1)
  let e23 : LowMeanIntegerExpr := .atom (0, 1)
  let e24 : LowMeanIntegerExpr := .add (10, 1) e22 e23
  let e25 : LowMeanIntegerExpr := .atom (9, 2)
  let e26 : LowMeanIntegerExpr := .atom (9, 25)
  let e27 : LowMeanIntegerExpr := .mul (81, 50) e25 e26
  let e28 : LowMeanIntegerExpr := .neg (-81, 50) e27
  let e29 : LowMeanIntegerExpr := .add (419, 50) e24 e28
  let e30 : LowMeanIntegerExpr := .add (9, 2) e25 e23
  let e31 : LowMeanIntegerExpr := .atom (3, 10)
  let e32 : LowMeanIntegerExpr := .neg (-3, 10) e31
  let e33 : LowMeanIntegerExpr := .add (21, 5) e30 e32
  let e34 : LowMeanIntegerExpr := .div (35, 3) e33 e26
  let e35 : LowMeanIntegerExpr := .neg (-35, 3) e34
  let e36 : LowMeanIntegerExpr := .add (-493, 150) e29 e35
  let e37 : LowMeanIntegerExpr := .mul (-1479, 500) e21 e36
  let e38 : LowMeanIntegerExpr := .neg (1479, 500) e37
  let e39 : LowMeanIntegerExpr := .add (15525156, 79560125) e17 e38
  e39

def fiberOuterStartExpr_c7c8_gain : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (51, 20)
  let e1 : LowMeanIntegerExpr := .atom (1, 1)
  let e2 : LowMeanIntegerExpr := .atom (17, 1)
  let e3 : LowMeanIntegerExpr := .add (18, 1) e2 e1
  let e4 : LowMeanIntegerExpr := .atom (2, 1)
  let e5 : LowMeanIntegerExpr := .neg (-2, 1) e4
  let e6 : LowMeanIntegerExpr := .add (16, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .div (1, 16) e1 e6
  let e8 : LowMeanIntegerExpr := .neg (-1, 16) e7
  let e9 : LowMeanIntegerExpr := .add (199, 80) e0 e8
  let e10 : LowMeanIntegerExpr := .div (199, 1440) e9 e3
  let e11 : LowMeanIntegerExpr := .atom (17, 50)
  let e12 : LowMeanIntegerExpr := .pow (289, 2500) e11 2
  let e13 : LowMeanIntegerExpr := .atom (3, 1)
  let e14 : LowMeanIntegerExpr := .neg (-289, 2500) e12
  let e15 : LowMeanIntegerExpr := .add (2211, 2500) e1 e14
  let e16 : LowMeanIntegerExpr := .mul (6633, 2500) e13 e15
  let e17 : LowMeanIntegerExpr := .div (289, 6633) e12 e16
  let e18 : LowMeanIntegerExpr := .neg (-289, 6633) e17
  let e19 : LowMeanIntegerExpr := .add (6344, 6633) e1 e18
  let e20 : LowMeanIntegerExpr := .mul (12688, 737) e19 e3
  let e21 : LowMeanIntegerExpr := .atom (4, 1)
  let e22 : LowMeanIntegerExpr := .neg (-4, 1) e21
  let e23 : LowMeanIntegerExpr := .add (9740, 737) e20 e22
  let e24 : LowMeanIntegerExpr := .pow (94867600, 543169) e23 2
  let e25 : LowMeanIntegerExpr := .mul (36, 1) e4 e3
  let e26 : LowMeanIntegerExpr := .div (23716900, 4888521) e24 e25
  let e27 : LowMeanIntegerExpr := .neg (-1, 1) e1
  let e28 : LowMeanIntegerExpr := .add (17, 1) e3 e27
  let e29 : LowMeanIntegerExpr := .atom (6, 1)
  let e30 : LowMeanIntegerExpr := .mul (6633, 1250) e29 e15
  let e31 : LowMeanIntegerExpr := .mul (53064, 625) e30 e6
  let e32 : LowMeanIntegerExpr := .div (10625, 53064) e28 e31
  let e33 : LowMeanIntegerExpr := .neg (-10625, 53064) e32
  let e34 : LowMeanIntegerExpr := .add (181904575, 39108168) e26 e33
  let e35 : LowMeanIntegerExpr := .mul (2601, 1250) e12 e3
  let e36 : LowMeanIntegerExpr := .atom (12, 1)
  let e37 : LowMeanIntegerExpr := .pow (4888521, 6250000) e15 2
  let e38 : LowMeanIntegerExpr := .mul (14665563, 1562500) e36 e37
  let e39 : LowMeanIntegerExpr := .div (361250, 1629507) e35 e38
  let e40 : LowMeanIntegerExpr := .neg (-361250, 1629507) e39
  let e41 : LowMeanIntegerExpr := .add (173234575, 39108168) e34 e40
  let e42 : LowMeanIntegerExpr := .mul (2002591687, 3910816800) e12 e41
  let e43 : LowMeanIntegerExpr := .add (141280269, 217267600) e10 e42
  e43

def fiberOuterStartExpr_c7c8_rate : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 1)
  let e1 : LowMeanIntegerExpr := .atom (17, 50)
  let e2 : LowMeanIntegerExpr := .pow (289, 2500) e1 2
  let e3 : LowMeanIntegerExpr := .neg (-289, 2500) e2
  let e4 : LowMeanIntegerExpr := .add (2211, 2500) e0 e3
  let e5 : LowMeanIntegerExpr := .atom (17, 1)
  let e6 : LowMeanIntegerExpr := .mul (37587, 2500) e4 e5
  let e7 : LowMeanIntegerExpr := .add (18, 1) e5 e0
  let e8 : LowMeanIntegerExpr := .div (12529, 15000) e6 e7
  let e9 : LowMeanIntegerExpr := .atom (2, 1)
  let e10 : LowMeanIntegerExpr := .div (1, 9) e9 e7
  let e11 : LowMeanIntegerExpr := .atom (3, 1)
  let e12 : LowMeanIntegerExpr := .mul (6633, 2500) e11 e4
  let e13 : LowMeanIntegerExpr := .div (289, 6633) e2 e12
  let e14 : LowMeanIntegerExpr := .add (114, 737) e10 e13
  let e15 : LowMeanIntegerExpr := .mul (34, 1) e9 e5
  let e16 : LowMeanIntegerExpr := .div (1, 34) e0 e15
  let e17 : LowMeanIntegerExpr := .neg (-1, 34) e16
  let e18 : LowMeanIntegerExpr := .add (33, 34) e0 e17
  let e19 : LowMeanIntegerExpr := .atom (6, 1)
  let e20 : LowMeanIntegerExpr := .pow (289, 1) e5 2
  let e21 : LowMeanIntegerExpr := .mul (1734, 1) e19 e20
  let e22 : LowMeanIntegerExpr := .div (1, 1734) e0 e21
  let e23 : LowMeanIntegerExpr := .neg (-1, 1734) e22
  let e24 : LowMeanIntegerExpr := .add (841, 867) e18 e23
  let e25 : LowMeanIntegerExpr := .div (98838, 619817) e14 e24
  let e26 : LowMeanIntegerExpr := .neg (-98838, 619817) e25
  let e27 : LowMeanIntegerExpr := .add (6283117193, 9297255000) e8 e26
  e27

def fiberOuterStartExpr_c7c8_bonus : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (17, 50)
  let e1 : LowMeanIntegerExpr := .pow (289, 2500) e0 2
  let e2 : LowMeanIntegerExpr := .atom (1, 1)
  let e3 : LowMeanIntegerExpr := .neg (-289, 2500) e1
  let e4 : LowMeanIntegerExpr := .add (2211, 2500) e2 e3
  let e5 : LowMeanIntegerExpr := .div (289, 2211) e1 e4
  let e6 : LowMeanIntegerExpr := .atom (17, 1)
  let e7 : LowMeanIntegerExpr := .neg (-1, 1) e2
  let e8 : LowMeanIntegerExpr := .add (16, 1) e6 e7
  let e9 : LowMeanIntegerExpr := .div (1, 17) e2 e6
  let e10 : LowMeanIntegerExpr := .add (273, 17) e8 e9
  let e11 : LowMeanIntegerExpr := .mul (1547, 737) e5 e10
  e11

def fiberOuterStartExpr_c7c8_logarithm : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (2, 1)
  let e1 : LowMeanIntegerExpr := .atom (1, 1)
  let e2 : LowMeanIntegerExpr := .atom (3, 10)
  let e3 : LowMeanIntegerExpr := .neg (-3, 10) e2
  let e4 : LowMeanIntegerExpr := .add (7, 10) e1 e3
  let e5 : LowMeanIntegerExpr := .add (13, 10) e1 e2
  let e6 : LowMeanIntegerExpr := .div (7, 13) e4 e5
  let e7 : LowMeanIntegerExpr := .pow (343, 2197) e6 3
  let e8 : LowMeanIntegerExpr := .atom (3, 1)
  let e9 : LowMeanIntegerExpr := .div (343, 6591) e7 e8
  let e10 : LowMeanIntegerExpr := .add (3892, 6591) e6 e9
  let e11 : LowMeanIntegerExpr := .pow (16807, 371293) e6 5
  let e12 : LowMeanIntegerExpr := .atom (5, 1)
  let e13 : LowMeanIntegerExpr := .pow (49, 169) e6 2
  let e14 : LowMeanIntegerExpr := .neg (-49, 169) e13
  let e15 : LowMeanIntegerExpr := .add (120, 169) e1 e14
  let e16 : LowMeanIntegerExpr := .mul (600, 169) e12 e15
  let e17 : LowMeanIntegerExpr := .div (16807, 1318200) e11 e16
  let e18 : LowMeanIntegerExpr := .add (265069, 439400) e10 e17
  let e19 : LowMeanIntegerExpr := .mul (265069, 219700) e0 e18
  e19

def fiberOuterStartExpr_c7c8_target : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (10, 1)
  let e1 : LowMeanIntegerExpr := .atom (1, 1)
  let e2 : LowMeanIntegerExpr := .add (11, 1) e0 e1
  let e3 : LowMeanIntegerExpr := .atom (9, 2)
  let e4 : LowMeanIntegerExpr := .atom (3, 10)
  let e5 : LowMeanIntegerExpr := .mul (27, 20) e3 e4
  let e6 : LowMeanIntegerExpr := .neg (-27, 20) e5
  let e7 : LowMeanIntegerExpr := .add (193, 20) e2 e6
  let e8 : LowMeanIntegerExpr := .add (11, 2) e3 e1
  let e9 : LowMeanIntegerExpr := .neg (-3, 10) e4
  let e10 : LowMeanIntegerExpr := .add (26, 5) e8 e9
  let e11 : LowMeanIntegerExpr := .div (52, 3) e10 e4
  let e12 : LowMeanIntegerExpr := .neg (-52, 3) e11
  let e13 : LowMeanIntegerExpr := .add (-461, 60) e7 e12
  e13

def fiberOuterStartExpr_c7c8_gap : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 1)
  let e1 : LowMeanIntegerExpr := .atom (2, 1)
  let e2 : LowMeanIntegerExpr := .add (3, 1) e0 e1
  let e3 : LowMeanIntegerExpr := .atom (19, 8)
  let e4 : LowMeanIntegerExpr := .pow (361, 64) e3 2
  let e5 : LowMeanIntegerExpr := .atom (4, 1)
  let e6 : LowMeanIntegerExpr := .neg (-19, 8) e3
  let e7 : LowMeanIntegerExpr := .add (13, 8) e5 e6
  let e8 : LowMeanIntegerExpr := .atom (48, 1)
  let e9 : LowMeanIntegerExpr := .div (361, 3072) e4 e8
  let e10 : LowMeanIntegerExpr := .add (5353, 3072) e7 e9
  let e11 : LowMeanIntegerExpr := .div (17328, 5353) e4 e10
  let e12 : LowMeanIntegerExpr := .mul (34656, 5353) e1 e11
  let e13 : LowMeanIntegerExpr := .atom (2, 3)
  let e14 : LowMeanIntegerExpr := .div (51984, 5353) e12 e13
  let e15 : LowMeanIntegerExpr := .neg (-51984, 5353) e14
  let e16 : LowMeanIntegerExpr := .add (-35925, 5353) e2 e15
  let e17 : LowMeanIntegerExpr := .atom (17, 1)
  let e18 : LowMeanIntegerExpr := .neg (-2, 1) e1
  let e19 : LowMeanIntegerExpr := .add (15, 1) e17 e18
  let e20 : LowMeanIntegerExpr := .div (15, 17) e19 e17
  let e21 : LowMeanIntegerExpr := .atom (10, 1)
  let e22 : LowMeanIntegerExpr := .add (11, 1) e21 e0
  let e23 : LowMeanIntegerExpr := .atom (9, 2)
  let e24 : LowMeanIntegerExpr := .atom (3, 10)
  let e25 : LowMeanIntegerExpr := .mul (27, 20) e23 e24
  let e26 : LowMeanIntegerExpr := .neg (-27, 20) e25
  let e27 : LowMeanIntegerExpr := .add (193, 20) e22 e26
  let e28 : LowMeanIntegerExpr := .add (11, 2) e23 e0
  let e29 : LowMeanIntegerExpr := .neg (-3, 10) e24
  let e30 : LowMeanIntegerExpr := .add (26, 5) e28 e29
  let e31 : LowMeanIntegerExpr := .div (52, 3) e30 e24
  let e32 : LowMeanIntegerExpr := .neg (-52, 3) e31
  let e33 : LowMeanIntegerExpr := .add (-461, 60) e27 e32
  let e34 : LowMeanIntegerExpr := .mul (-461, 68) e20 e33
  let e35 : LowMeanIntegerExpr := .neg (461, 68) e34
  let e36 : LowMeanIntegerExpr := .add (24833, 364004) e16 e35
  e36

def fiberOuterStartExpr : FiberOuterStartIdentity → FiberOuterStartRole → LowMeanIntegerExpr
  | .c3, .gain => fiberOuterStartExpr_c3_gain
  | .c3, .rate => fiberOuterStartExpr_c3_rate
  | .c3, .bonus => fiberOuterStartExpr_c3_bonus
  | .c3, .logarithm => fiberOuterStartExpr_c3_logarithm
  | .c3, .target => fiberOuterStartExpr_c3_target
  | .c3, .gap => fiberOuterStartExpr_c3_gap
  | .c4, .gain => fiberOuterStartExpr_c4_gain
  | .c4, .rate => fiberOuterStartExpr_c4_rate
  | .c4, .bonus => fiberOuterStartExpr_c4_bonus
  | .c4, .logarithm => fiberOuterStartExpr_c4_logarithm
  | .c4, .target => fiberOuterStartExpr_c4_target
  | .c4, .gap => fiberOuterStartExpr_c4_gap
  | .c5c6, .gain => fiberOuterStartExpr_c5c6_gain
  | .c5c6, .rate => fiberOuterStartExpr_c5c6_rate
  | .c5c6, .bonus => fiberOuterStartExpr_c5c6_bonus
  | .c5c6, .logarithm => fiberOuterStartExpr_c5c6_logarithm
  | .c5c6, .target => fiberOuterStartExpr_c5c6_target
  | .c5c6, .gap => fiberOuterStartExpr_c5c6_gap
  | .c7c8, .gain => fiberOuterStartExpr_c7c8_gain
  | .c7c8, .rate => fiberOuterStartExpr_c7c8_rate
  | .c7c8, .bonus => fiberOuterStartExpr_c7c8_bonus
  | .c7c8, .logarithm => fiberOuterStartExpr_c7c8_logarithm
  | .c7c8, .target => fiberOuterStartExpr_c7c8_target
  | .c7c8, .gap => fiberOuterStartExpr_c7c8_gap

def fiberOuterStartIdentityAt : ℕ → FiberOuterStartIdentity
  | 0 => .c3
  | 1 => .c4
  | 2 => .c5c6
  | _ => .c7c8

def fiberOuterStartRoleAt : ℕ → FiberOuterStartRole
  | 0 => .gain
  | 1 => .rate
  | 2 => .bonus
  | 3 => .logarithm
  | 4 => .target
  | _ => .gap

end Erdos993Lean.Analytic.V213
