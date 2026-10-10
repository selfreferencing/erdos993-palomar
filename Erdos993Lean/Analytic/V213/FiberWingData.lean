module

public import Erdos993Lean.Analytic.V213.LowMeanIntegerShape

/-!
Accepted F04 wing starts, actual printed W1/W2/W3 identities. The canonical
integer trees retain Eq86 and both Eq87 sums including every factorial.
All values are data only until checked against full shapes and thresholds.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

inductive FiberWingIdentity where
  | w1 | w2 | w3

inductive FiberWingRole where
  | rate | bonus | gain | rootSquare | eta | width
  | taylorLeft | taylorRight | gap | target

structure FiberWingRow where
  printed : String
  N0 : lowMeanFraction
  R : lowMeanFraction
  a : lowMeanFraction
  b : lowMeanFraction
  d : lowMeanFraction
  eta : lowMeanFraction
  mu_W : lowMeanFraction
  p : lowMeanFraction
  s0 : lowMeanFraction
  skew_lower : lowMeanFraction
  skew_upper : lowMeanFraction
  tau : lowMeanFraction
  sqrtUpper : lowMeanFraction
  gainCoefficient : lowMeanFraction
  taylorLeft : lowMeanFraction
  taylorRight : lowMeanFraction
  gap : lowMeanFraction

def fiberWingPrinted : FiberWingIdentity → String
  | .w1 => "F04:W1"
  | .w2 => "F04:W2"
  | .w3 => "F04:W3"

def fiberWingById : FiberWingIdentity → FiberWingRow
  | .w1 => ⟨"F04:W1", (13, 1), (22, 25), (7, 125), (3, 40), (3, 100), (11, 13), (19, 1), (11, 100), (-13, 25), (283, 5000), (741, 10000), (29, 50), (11, 3), (221, 100), (271824567898672, 3337860107421875), (3833756109466309, 46875000000000000), (15329, 248820)⟩
  | .w2 => ⟨"F04:W2", (13, 1), (17, 20), (37, 500), (9, 80), (13, 200), (11, 13), (20, 1), (7, 50), (-553, 1000), (37, 500), (139, 1250), (11, 20), (11, 3), (221, 100), (165284989713873635776332232223, 2500000000000000000000000000000), (1997708975251, 30000000000000), (4361, 395148)⟩
  | .w3 => ⟨"F04:W3", (31, 2), (41, 50), (11, 100), (17, 100), (7, 40), (27, 31), (26, 1), (9, 50), (-7, 12), (1111, 10000), (1667, 10000), (13, 25), (63, 16), (54, 25), (15063967235, 278628139008), (1663016520191, 30517578125000), (483179, 9913800)⟩

def fiberWingExpr_w1_rate : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 1)
  let e1 : LowMeanIntegerExpr := .atom (3, 40)
  let e2 : LowMeanIntegerExpr := .pow (9, 1600) e1 2
  let e3 : LowMeanIntegerExpr := .neg (-9, 1600) e2
  let e4 : LowMeanIntegerExpr := .add (1591, 1600) e0 e3
  let e5 : LowMeanIntegerExpr := .atom (13, 1)
  let e6 : LowMeanIntegerExpr := .mul (20683, 1600) e4 e5
  let e7 : LowMeanIntegerExpr := .add (14, 1) e5 e0
  let e8 : LowMeanIntegerExpr := .div (20683, 22400) e6 e7
  let e9 : LowMeanIntegerExpr := .atom (2, 1)
  let e10 : LowMeanIntegerExpr := .mul (3, 20) e9 e1
  let e11 : LowMeanIntegerExpr := .atom (11, 3)
  let e12 : LowMeanIntegerExpr := .mul (11, 20) e10 e11
  let e13 : LowMeanIntegerExpr := .div (11, 280) e12 e7
  let e14 : LowMeanIntegerExpr := .neg (-11, 280) e13
  let e15 : LowMeanIntegerExpr := .add (2829, 3200) e8 e14
  let e16 : LowMeanIntegerExpr := .mul (117, 1600) e2 e5
  let e17 : LowMeanIntegerExpr := .atom (3, 1)
  let e18 : LowMeanIntegerExpr := .neg (-1, 1) e0
  let e19 : LowMeanIntegerExpr := .add (12, 1) e5 e18
  let e20 : LowMeanIntegerExpr := .mul (36, 1) e17 e19
  let e21 : LowMeanIntegerExpr := .div (13, 6400) e16 e20
  let e22 : LowMeanIntegerExpr := .neg (-13, 6400) e21
  let e23 : LowMeanIntegerExpr := .add (1129, 1280) e15 e22
  e23

def fiberWingExpr_w1_bonus : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (7, 125)
  let e1 : LowMeanIntegerExpr := .pow (49, 15625) e0 2
  let e2 : LowMeanIntegerExpr := .atom (13, 1)
  let e3 : LowMeanIntegerExpr := .atom (1, 1)
  let e4 : LowMeanIntegerExpr := .neg (-1, 1) e3
  let e5 : LowMeanIntegerExpr := .add (12, 1) e2 e4
  let e6 : LowMeanIntegerExpr := .mul (588, 15625) e1 e5
  e6

def fiberWingExpr_w1_gain : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (221, 100)
  let e1 : LowMeanIntegerExpr := .atom (7, 125)
  let e2 : LowMeanIntegerExpr := .mul (1547, 12500) e0 e1
  let e3 : LowMeanIntegerExpr := .atom (21, 5)
  let e4 : LowMeanIntegerExpr := .pow (49, 15625) e1 2
  let e5 : LowMeanIntegerExpr := .mul (1029, 78125) e3 e4
  let e6 : LowMeanIntegerExpr := .neg (-1029, 78125) e5
  let e7 : LowMeanIntegerExpr := .add (34559, 312500) e2 e6
  e7

def fiberWingExpr_w1_rootSquare : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (11, 3)
  let e1 : LowMeanIntegerExpr := .pow (121, 9) e0 2
  let e2 : LowMeanIntegerExpr := .atom (13, 1)
  let e3 : LowMeanIntegerExpr := .neg (-13, 1) e2
  let e4 : LowMeanIntegerExpr := .add (4, 9) e1 e3
  e4

def fiberWingExpr_w1_eta : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (13, 1)
  let e1 : LowMeanIntegerExpr := .atom (2, 1)
  let e2 : LowMeanIntegerExpr := .neg (-2, 1) e1
  let e3 : LowMeanIntegerExpr := .add (11, 1) e0 e2
  let e4 : LowMeanIntegerExpr := .div (11, 13) e3 e0
  e4

def fiberWingExpr_w1_width : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (19, 1)
  let e1 : LowMeanIntegerExpr := .atom (29, 50)
  let e2 : LowMeanIntegerExpr := .mul (551, 50) e0 e1
  let e3 : LowMeanIntegerExpr := .atom (2, 1)
  let e4 : LowMeanIntegerExpr := .add (651, 50) e2 e3
  let e5 : LowMeanIntegerExpr := .atom (13, 1)
  let e6 : LowMeanIntegerExpr := .neg (-13, 1) e5
  let e7 : LowMeanIntegerExpr := .add (1, 50) e4 e6
  e7

def fiberWingExpr_w1_taylorLeft : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 1)
  let e1 : LowMeanIntegerExpr := .atom (-13, 25)
  let e2 : LowMeanIntegerExpr := .add (12, 25) e0 e1
  let e3 : LowMeanIntegerExpr := .pow (144, 625) e2 2
  let e4 : LowMeanIntegerExpr := .atom (2, 1)
  let e5 : LowMeanIntegerExpr := .mul (-26, 25) e4 e1
  let e6 : LowMeanIntegerExpr := .pow (1, 1) e5 0
  let e7 : LowMeanIntegerExpr := .div (1, 1) e6 e0
  let e8 : LowMeanIntegerExpr := .pow (-26, 25) e5 1
  let e9 : LowMeanIntegerExpr := .div (-26, 25) e8 e0
  let e10 : LowMeanIntegerExpr := .add (-1, 25) e7 e9
  let e11 : LowMeanIntegerExpr := .pow (676, 625) e5 2
  let e12 : LowMeanIntegerExpr := .div (338, 625) e11 e4
  let e13 : LowMeanIntegerExpr := .add (313, 625) e10 e12
  let e14 : LowMeanIntegerExpr := .pow (-17576, 15625) e5 3
  let e15 : LowMeanIntegerExpr := .atom (6, 1)
  let e16 : LowMeanIntegerExpr := .div (-8788, 46875) e14 e15
  let e17 : LowMeanIntegerExpr := .add (14687, 46875) e13 e16
  let e18 : LowMeanIntegerExpr := .pow (456976, 390625) e5 4
  let e19 : LowMeanIntegerExpr := .atom (24, 1)
  let e20 : LowMeanIntegerExpr := .div (57122, 1171875) e18 e19
  let e21 : LowMeanIntegerExpr := .add (424297, 1171875) e17 e20
  let e22 : LowMeanIntegerExpr := .pow (-11881376, 9765625) e5 5
  let e23 : LowMeanIntegerExpr := .atom (120, 1)
  let e24 : LowMeanIntegerExpr := .div (-1485172, 146484375) e22 e23
  let e25 : LowMeanIntegerExpr := .add (51551953, 146484375) e21 e24
  let e26 : LowMeanIntegerExpr := .pow (308915776, 244140625) e5 6
  let e27 : LowMeanIntegerExpr := .atom (720, 1)
  let e28 : LowMeanIntegerExpr := .div (19307236, 10986328125) e26 e27
  let e29 : LowMeanIntegerExpr := .add (3885703711, 10986328125) e25 e28
  let e30 : LowMeanIntegerExpr := .pow (-8031810176, 6103515625) e5 7
  let e31 : LowMeanIntegerExpr := .atom (5040, 1)
  let e32 : LowMeanIntegerExpr := .div (-501988136, 1922607421875) e30 e31
  let e33 : LowMeanIntegerExpr := .add (679496161289, 1922607421875) e29 e32
  let e34 : LowMeanIntegerExpr := .pow (208827064576, 152587890625) e5 8
  let e35 : LowMeanIntegerExpr := .atom (40320, 1)
  let e36 : LowMeanIntegerExpr := .div (1631461442, 48065185546875) e34 e35
  let e37 : LowMeanIntegerExpr := .add (16989035493667, 48065185546875) e33 e36
  let e38 : LowMeanIntegerExpr := .mul (271824567898672, 3337860107421875) e3 e37
  e38

def fiberWingExpr_w1_taylorRight : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (29, 50)
  let e1 : LowMeanIntegerExpr := .pow (20511149, 312500000) e0 5
  let e2 : LowMeanIntegerExpr := .atom (2, 1)
  let e3 : LowMeanIntegerExpr := .atom (11, 100)
  let e4 : LowMeanIntegerExpr := .mul (11, 50) e2 e3
  let e5 : LowMeanIntegerExpr := .pow (1, 1) e4 0
  let e6 : LowMeanIntegerExpr := .atom (1, 1)
  let e7 : LowMeanIntegerExpr := .div (1, 1) e5 e6
  let e8 : LowMeanIntegerExpr := .pow (11, 50) e4 1
  let e9 : LowMeanIntegerExpr := .div (11, 50) e8 e6
  let e10 : LowMeanIntegerExpr := .add (61, 50) e7 e9
  let e11 : LowMeanIntegerExpr := .pow (121, 2500) e4 2
  let e12 : LowMeanIntegerExpr := .div (121, 5000) e11 e2
  let e13 : LowMeanIntegerExpr := .add (6221, 5000) e10 e12
  let e14 : LowMeanIntegerExpr := .pow (1331, 125000) e4 3
  let e15 : LowMeanIntegerExpr := .atom (6, 1)
  let e16 : LowMeanIntegerExpr := .div (1331, 750000) e14 e15
  let e17 : LowMeanIntegerExpr := .add (934481, 750000) e13 e16
  let e18 : LowMeanIntegerExpr := .pow (14641, 6250000) e4 4
  let e19 : LowMeanIntegerExpr := .atom (24, 1)
  let e20 : LowMeanIntegerExpr := .div (14641, 150000000) e18 e19
  let e21 : LowMeanIntegerExpr := .add (186910841, 150000000) e17 e20
  let e22 : LowMeanIntegerExpr := .mul (3833756109466309, 46875000000000000) e1 e21
  e22

def fiberWingExpr_w1_gap : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 1)
  let e1 : LowMeanIntegerExpr := .atom (3, 100)
  let e2 : LowMeanIntegerExpr := .add (103, 100) e0 e1
  let e3 : LowMeanIntegerExpr := .atom (2, 1)
  let e4 : LowMeanIntegerExpr := .atom (-13, 25)
  let e5 : LowMeanIntegerExpr := .pow (169, 625) e4 2
  let e6 : LowMeanIntegerExpr := .mul (338, 625) e3 e5
  let e7 : LowMeanIntegerExpr := .atom (22, 25)
  let e8 : LowMeanIntegerExpr := .add (12, 25) e0 e4
  let e9 : LowMeanIntegerExpr := .mul (264, 625) e7 e8
  let e10 : LowMeanIntegerExpr := .div (169, 132) e6 e9
  let e11 : LowMeanIntegerExpr := .neg (-169, 132) e10
  let e12 : LowMeanIntegerExpr := .add (-413, 1650) e2 e11
  let e13 : LowMeanIntegerExpr := .atom (13, 1)
  let e14 : LowMeanIntegerExpr := .neg (-2, 1) e3
  let e15 : LowMeanIntegerExpr := .add (11, 1) e13 e14
  let e16 : LowMeanIntegerExpr := .div (11, 13) e15 e13
  let e17 : LowMeanIntegerExpr := .atom (10, 1)
  let e18 : LowMeanIntegerExpr := .atom (9, 2)
  let e19 : LowMeanIntegerExpr := .atom (29, 50)
  let e20 : LowMeanIntegerExpr := .mul (261, 100) e18 e19
  let e21 : LowMeanIntegerExpr := .neg (-261, 100) e20
  let e22 : LowMeanIntegerExpr := .add (739, 100) e17 e21
  let e23 : LowMeanIntegerExpr := .div (225, 29) e18 e19
  let e24 : LowMeanIntegerExpr := .neg (-225, 29) e23
  let e25 : LowMeanIntegerExpr := .add (-1069, 2900) e22 e24
  let e26 : LowMeanIntegerExpr := .mul (-11759, 37700) e16 e25
  let e27 : LowMeanIntegerExpr := .neg (11759, 37700) e26
  let e28 : LowMeanIntegerExpr := .add (15329, 248820) e12 e27
  e28

def fiberWingExpr_w1_target : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (10, 1)
  let e1 : LowMeanIntegerExpr := .atom (9, 2)
  let e2 : LowMeanIntegerExpr := .atom (29, 50)
  let e3 : LowMeanIntegerExpr := .mul (261, 100) e1 e2
  let e4 : LowMeanIntegerExpr := .neg (-261, 100) e3
  let e5 : LowMeanIntegerExpr := .add (739, 100) e0 e4
  let e6 : LowMeanIntegerExpr := .div (225, 29) e1 e2
  let e7 : LowMeanIntegerExpr := .neg (-225, 29) e6
  let e8 : LowMeanIntegerExpr := .add (-1069, 2900) e5 e7
  e8

def fiberWingExpr_w2_rate : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 1)
  let e1 : LowMeanIntegerExpr := .atom (9, 80)
  let e2 : LowMeanIntegerExpr := .pow (81, 6400) e1 2
  let e3 : LowMeanIntegerExpr := .neg (-81, 6400) e2
  let e4 : LowMeanIntegerExpr := .add (6319, 6400) e0 e3
  let e5 : LowMeanIntegerExpr := .atom (13, 1)
  let e6 : LowMeanIntegerExpr := .mul (82147, 6400) e4 e5
  let e7 : LowMeanIntegerExpr := .add (14, 1) e5 e0
  let e8 : LowMeanIntegerExpr := .div (82147, 89600) e6 e7
  let e9 : LowMeanIntegerExpr := .atom (2, 1)
  let e10 : LowMeanIntegerExpr := .mul (9, 40) e9 e1
  let e11 : LowMeanIntegerExpr := .atom (11, 3)
  let e12 : LowMeanIntegerExpr := .mul (33, 40) e10 e11
  let e13 : LowMeanIntegerExpr := .div (33, 560) e12 e7
  let e14 : LowMeanIntegerExpr := .neg (-33, 560) e13
  let e15 : LowMeanIntegerExpr := .add (10981, 12800) e8 e14
  let e16 : LowMeanIntegerExpr := .mul (1053, 6400) e2 e5
  let e17 : LowMeanIntegerExpr := .atom (3, 1)
  let e18 : LowMeanIntegerExpr := .neg (-1, 1) e0
  let e19 : LowMeanIntegerExpr := .add (12, 1) e5 e18
  let e20 : LowMeanIntegerExpr := .mul (36, 1) e17 e19
  let e21 : LowMeanIntegerExpr := .div (117, 25600) e16 e20
  let e22 : LowMeanIntegerExpr := .neg (-117, 25600) e21
  let e23 : LowMeanIntegerExpr := .add (4369, 5120) e15 e22
  e23

def fiberWingExpr_w2_bonus : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (37, 500)
  let e1 : LowMeanIntegerExpr := .pow (1369, 250000) e0 2
  let e2 : LowMeanIntegerExpr := .atom (13, 1)
  let e3 : LowMeanIntegerExpr := .atom (1, 1)
  let e4 : LowMeanIntegerExpr := .neg (-1, 1) e3
  let e5 : LowMeanIntegerExpr := .add (12, 1) e2 e4
  let e6 : LowMeanIntegerExpr := .mul (4107, 62500) e1 e5
  e6

def fiberWingExpr_w2_gain : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (221, 100)
  let e1 : LowMeanIntegerExpr := .atom (37, 500)
  let e2 : LowMeanIntegerExpr := .mul (8177, 50000) e0 e1
  let e3 : LowMeanIntegerExpr := .atom (21, 5)
  let e4 : LowMeanIntegerExpr := .pow (1369, 250000) e1 2
  let e5 : LowMeanIntegerExpr := .mul (28749, 1250000) e3 e4
  let e6 : LowMeanIntegerExpr := .neg (-28749, 1250000) e5
  let e7 : LowMeanIntegerExpr := .add (43919, 312500) e2 e6
  e7

def fiberWingExpr_w2_rootSquare : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (11, 3)
  let e1 : LowMeanIntegerExpr := .pow (121, 9) e0 2
  let e2 : LowMeanIntegerExpr := .atom (13, 1)
  let e3 : LowMeanIntegerExpr := .neg (-13, 1) e2
  let e4 : LowMeanIntegerExpr := .add (4, 9) e1 e3
  e4

def fiberWingExpr_w2_eta : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (13, 1)
  let e1 : LowMeanIntegerExpr := .atom (2, 1)
  let e2 : LowMeanIntegerExpr := .neg (-2, 1) e1
  let e3 : LowMeanIntegerExpr := .add (11, 1) e0 e2
  let e4 : LowMeanIntegerExpr := .div (11, 13) e3 e0
  e4

def fiberWingExpr_w2_width : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (20, 1)
  let e1 : LowMeanIntegerExpr := .atom (11, 20)
  let e2 : LowMeanIntegerExpr := .mul (11, 1) e0 e1
  let e3 : LowMeanIntegerExpr := .atom (2, 1)
  let e4 : LowMeanIntegerExpr := .add (13, 1) e2 e3
  let e5 : LowMeanIntegerExpr := .atom (13, 1)
  let e6 : LowMeanIntegerExpr := .neg (-13, 1) e5
  let e7 : LowMeanIntegerExpr := .add (0, 1) e4 e6
  e7

def fiberWingExpr_w2_taylorLeft : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 1)
  let e1 : LowMeanIntegerExpr := .atom (-553, 1000)
  let e2 : LowMeanIntegerExpr := .add (447, 1000) e0 e1
  let e3 : LowMeanIntegerExpr := .pow (199809, 1000000) e2 2
  let e4 : LowMeanIntegerExpr := .atom (2, 1)
  let e5 : LowMeanIntegerExpr := .mul (-553, 500) e4 e1
  let e6 : LowMeanIntegerExpr := .pow (1, 1) e5 0
  let e7 : LowMeanIntegerExpr := .div (1, 1) e6 e0
  let e8 : LowMeanIntegerExpr := .pow (-553, 500) e5 1
  let e9 : LowMeanIntegerExpr := .div (-553, 500) e8 e0
  let e10 : LowMeanIntegerExpr := .add (-53, 500) e7 e9
  let e11 : LowMeanIntegerExpr := .pow (305809, 250000) e5 2
  let e12 : LowMeanIntegerExpr := .div (305809, 500000) e11 e4
  let e13 : LowMeanIntegerExpr := .add (252809, 500000) e10 e12
  let e14 : LowMeanIntegerExpr := .pow (-169112377, 125000000) e5 3
  let e15 : LowMeanIntegerExpr := .atom (6, 1)
  let e16 : LowMeanIntegerExpr := .div (-169112377, 750000000) e14 e15
  let e17 : LowMeanIntegerExpr := .add (210101123, 750000000) e13 e16
  let e18 : LowMeanIntegerExpr := .pow (93519144481, 62500000000) e5 4
  let e19 : LowMeanIntegerExpr := .atom (24, 1)
  let e20 : LowMeanIntegerExpr := .div (93519144481, 1500000000000) e18 e19
  let e21 : LowMeanIntegerExpr := .add (513721390481, 1500000000000) e17 e20
  let e22 : LowMeanIntegerExpr := .pow (-51716086897993, 31250000000000) e5 5
  let e23 : LowMeanIntegerExpr := .atom (120, 1)
  let e24 : LowMeanIntegerExpr := .div (-51716086897993, 3750000000000000) e22 e23
  let e25 : LowMeanIntegerExpr := .add (1232587389304507, 3750000000000000) e21 e24
  let e26 : LowMeanIntegerExpr := .pow (28598996054590129, 15625000000000000) e5 6
  let e27 : LowMeanIntegerExpr := .atom (720, 1)
  let e28 : LowMeanIntegerExpr := .div (28598996054590129, 11250000000000000000) e26 e27
  let e29 : LowMeanIntegerExpr := .add (3726361163968111129, 11250000000000000000) e25 e28
  let e30 : LowMeanIntegerExpr := .pow (-15815244818188341337, 7812500000000000000) e5 7
  let e31 : LowMeanIntegerExpr := .atom (5040, 1)
  let e32 : LowMeanIntegerExpr := .div (-2259320688312620191, 5625000000000000000000) e30 e31
  let e33 : LowMeanIntegerExpr := .add (1860921261295742944309, 5625000000000000000000) e29 e32
  let e34 : LowMeanIntegerExpr := .pow (8745830384458152759361, 3906250000000000000000) e5 8
  let e35 : LowMeanIntegerExpr := .atom (40320, 1)
  let e36 : LowMeanIntegerExpr := .div (1249404340636878965623, 22500000000000000000000000) e34 e35
  let e37 : LowMeanIntegerExpr := .add (7444934449523608656201623, 22500000000000000000000000) e33 e36
  let e38 : LowMeanIntegerExpr := .mul (165284989713873635776332232223, 2500000000000000000000000000000) e3 e37
  e38

def fiberWingExpr_w2_taylorRight : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (11, 20)
  let e1 : LowMeanIntegerExpr := .pow (161051, 3200000) e0 5
  let e2 : LowMeanIntegerExpr := .atom (2, 1)
  let e3 : LowMeanIntegerExpr := .atom (7, 50)
  let e4 : LowMeanIntegerExpr := .mul (7, 25) e2 e3
  let e5 : LowMeanIntegerExpr := .pow (1, 1) e4 0
  let e6 : LowMeanIntegerExpr := .atom (1, 1)
  let e7 : LowMeanIntegerExpr := .div (1, 1) e5 e6
  let e8 : LowMeanIntegerExpr := .pow (7, 25) e4 1
  let e9 : LowMeanIntegerExpr := .div (7, 25) e8 e6
  let e10 : LowMeanIntegerExpr := .add (32, 25) e7 e9
  let e11 : LowMeanIntegerExpr := .pow (49, 625) e4 2
  let e12 : LowMeanIntegerExpr := .div (49, 1250) e11 e2
  let e13 : LowMeanIntegerExpr := .add (1649, 1250) e10 e12
  let e14 : LowMeanIntegerExpr := .pow (343, 15625) e4 3
  let e15 : LowMeanIntegerExpr := .atom (6, 1)
  let e16 : LowMeanIntegerExpr := .div (343, 93750) e14 e15
  let e17 : LowMeanIntegerExpr := .add (62009, 46875) e13 e16
  let e18 : LowMeanIntegerExpr := .pow (2401, 390625) e4 4
  let e19 : LowMeanIntegerExpr := .atom (24, 1)
  let e20 : LowMeanIntegerExpr := .div (2401, 9375000) e18 e19
  let e21 : LowMeanIntegerExpr := .add (12404201, 9375000) e17 e20
  let e22 : LowMeanIntegerExpr := .mul (1997708975251, 30000000000000) e1 e21
  e22

def fiberWingExpr_w2_gap : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 1)
  let e1 : LowMeanIntegerExpr := .atom (13, 200)
  let e2 : LowMeanIntegerExpr := .add (213, 200) e0 e1
  let e3 : LowMeanIntegerExpr := .atom (2, 1)
  let e4 : LowMeanIntegerExpr := .atom (-553, 1000)
  let e5 : LowMeanIntegerExpr := .pow (305809, 1000000) e4 2
  let e6 : LowMeanIntegerExpr := .mul (305809, 500000) e3 e5
  let e7 : LowMeanIntegerExpr := .atom (17, 20)
  let e8 : LowMeanIntegerExpr := .add (447, 1000) e0 e4
  let e9 : LowMeanIntegerExpr := .mul (7599, 20000) e7 e8
  let e10 : LowMeanIntegerExpr := .div (305809, 189975) e6 e9
  let e11 : LowMeanIntegerExpr := .neg (-305809, 189975) e10
  let e12 : LowMeanIntegerExpr := .add (-165577, 303960) e2 e11
  let e13 : LowMeanIntegerExpr := .atom (13, 1)
  let e14 : LowMeanIntegerExpr := .neg (-2, 1) e3
  let e15 : LowMeanIntegerExpr := .add (11, 1) e13 e14
  let e16 : LowMeanIntegerExpr := .div (11, 13) e15 e13
  let e17 : LowMeanIntegerExpr := .atom (10, 1)
  let e18 : LowMeanIntegerExpr := .atom (9, 2)
  let e19 : LowMeanIntegerExpr := .atom (11, 20)
  let e20 : LowMeanIntegerExpr := .mul (99, 40) e18 e19
  let e21 : LowMeanIntegerExpr := .neg (-99, 40) e20
  let e22 : LowMeanIntegerExpr := .add (301, 40) e17 e21
  let e23 : LowMeanIntegerExpr := .div (90, 11) e18 e19
  let e24 : LowMeanIntegerExpr := .neg (-90, 11) e23
  let e25 : LowMeanIntegerExpr := .add (-289, 440) e22 e24
  let e26 : LowMeanIntegerExpr := .mul (-289, 520) e16 e25
  let e27 : LowMeanIntegerExpr := .neg (289, 520) e26
  let e28 : LowMeanIntegerExpr := .add (4361, 395148) e12 e27
  e28

def fiberWingExpr_w2_target : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (10, 1)
  let e1 : LowMeanIntegerExpr := .atom (9, 2)
  let e2 : LowMeanIntegerExpr := .atom (11, 20)
  let e3 : LowMeanIntegerExpr := .mul (99, 40) e1 e2
  let e4 : LowMeanIntegerExpr := .neg (-99, 40) e3
  let e5 : LowMeanIntegerExpr := .add (301, 40) e0 e4
  let e6 : LowMeanIntegerExpr := .div (90, 11) e1 e2
  let e7 : LowMeanIntegerExpr := .neg (-90, 11) e6
  let e8 : LowMeanIntegerExpr := .add (-289, 440) e5 e7
  e8

def fiberWingExpr_w3_rate : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 1)
  let e1 : LowMeanIntegerExpr := .atom (17, 100)
  let e2 : LowMeanIntegerExpr := .pow (289, 10000) e1 2
  let e3 : LowMeanIntegerExpr := .neg (-289, 10000) e2
  let e4 : LowMeanIntegerExpr := .add (9711, 10000) e0 e3
  let e5 : LowMeanIntegerExpr := .atom (31, 2)
  let e6 : LowMeanIntegerExpr := .mul (301041, 20000) e4 e5
  let e7 : LowMeanIntegerExpr := .add (33, 2) e5 e0
  let e8 : LowMeanIntegerExpr := .div (100347, 110000) e6 e7
  let e9 : LowMeanIntegerExpr := .atom (2, 1)
  let e10 : LowMeanIntegerExpr := .mul (17, 50) e9 e1
  let e11 : LowMeanIntegerExpr := .atom (63, 16)
  let e12 : LowMeanIntegerExpr := .mul (1071, 800) e10 e11
  let e13 : LowMeanIntegerExpr := .div (357, 4400) e12 e7
  let e14 : LowMeanIntegerExpr := .neg (-357, 4400) e13
  let e15 : LowMeanIntegerExpr := .add (45711, 55000) e8 e14
  let e16 : LowMeanIntegerExpr := .mul (8959, 20000) e2 e5
  let e17 : LowMeanIntegerExpr := .atom (3, 1)
  let e18 : LowMeanIntegerExpr := .neg (-1, 1) e0
  let e19 : LowMeanIntegerExpr := .add (29, 2) e5 e18
  let e20 : LowMeanIntegerExpr := .mul (87, 2) e17 e19
  let e21 : LowMeanIntegerExpr := .div (8959, 870000) e16 e20
  let e22 : LowMeanIntegerExpr := .neg (-8959, 870000) e21
  let e23 : LowMeanIntegerExpr := .add (1571033, 1914000) e15 e22
  e23

def fiberWingExpr_w3_bonus : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (11, 100)
  let e1 : LowMeanIntegerExpr := .pow (121, 10000) e0 2
  let e2 : LowMeanIntegerExpr := .atom (31, 2)
  let e3 : LowMeanIntegerExpr := .atom (1, 1)
  let e4 : LowMeanIntegerExpr := .neg (-1, 1) e3
  let e5 : LowMeanIntegerExpr := .add (29, 2) e2 e4
  let e6 : LowMeanIntegerExpr := .mul (3509, 20000) e1 e5
  e6

def fiberWingExpr_w3_gain : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (54, 25)
  let e1 : LowMeanIntegerExpr := .atom (11, 100)
  let e2 : LowMeanIntegerExpr := .mul (297, 1250) e0 e1
  let e3 : LowMeanIntegerExpr := .atom (21, 5)
  let e4 : LowMeanIntegerExpr := .pow (121, 10000) e1 2
  let e5 : LowMeanIntegerExpr := .mul (2541, 50000) e3 e4
  let e6 : LowMeanIntegerExpr := .neg (-2541, 50000) e5
  let e7 : LowMeanIntegerExpr := .add (9339, 50000) e2 e6
  e7

def fiberWingExpr_w3_rootSquare : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (63, 16)
  let e1 : LowMeanIntegerExpr := .pow (3969, 256) e0 2
  let e2 : LowMeanIntegerExpr := .atom (31, 2)
  let e3 : LowMeanIntegerExpr := .neg (-31, 2) e2
  let e4 : LowMeanIntegerExpr := .add (1, 256) e1 e3
  e4

def fiberWingExpr_w3_eta : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (31, 2)
  let e1 : LowMeanIntegerExpr := .atom (2, 1)
  let e2 : LowMeanIntegerExpr := .neg (-2, 1) e1
  let e3 : LowMeanIntegerExpr := .add (27, 2) e0 e2
  let e4 : LowMeanIntegerExpr := .div (27, 31) e3 e0
  e4

def fiberWingExpr_w3_width : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (26, 1)
  let e1 : LowMeanIntegerExpr := .atom (13, 25)
  let e2 : LowMeanIntegerExpr := .mul (338, 25) e0 e1
  let e3 : LowMeanIntegerExpr := .atom (2, 1)
  let e4 : LowMeanIntegerExpr := .add (388, 25) e2 e3
  let e5 : LowMeanIntegerExpr := .atom (31, 2)
  let e6 : LowMeanIntegerExpr := .neg (-31, 2) e5
  let e7 : LowMeanIntegerExpr := .add (1, 50) e4 e6
  e7

def fiberWingExpr_w3_taylorLeft : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 1)
  let e1 : LowMeanIntegerExpr := .atom (-7, 12)
  let e2 : LowMeanIntegerExpr := .add (5, 12) e0 e1
  let e3 : LowMeanIntegerExpr := .pow (25, 144) e2 2
  let e4 : LowMeanIntegerExpr := .atom (2, 1)
  let e5 : LowMeanIntegerExpr := .mul (-7, 6) e4 e1
  let e6 : LowMeanIntegerExpr := .pow (1, 1) e5 0
  let e7 : LowMeanIntegerExpr := .div (1, 1) e6 e0
  let e8 : LowMeanIntegerExpr := .pow (-7, 6) e5 1
  let e9 : LowMeanIntegerExpr := .div (-7, 6) e8 e0
  let e10 : LowMeanIntegerExpr := .add (-1, 6) e7 e9
  let e11 : LowMeanIntegerExpr := .pow (49, 36) e5 2
  let e12 : LowMeanIntegerExpr := .div (49, 72) e11 e4
  let e13 : LowMeanIntegerExpr := .add (37, 72) e10 e12
  let e14 : LowMeanIntegerExpr := .pow (-343, 216) e5 3
  let e15 : LowMeanIntegerExpr := .atom (6, 1)
  let e16 : LowMeanIntegerExpr := .div (-343, 1296) e14 e15
  let e17 : LowMeanIntegerExpr := .add (323, 1296) e13 e16
  let e18 : LowMeanIntegerExpr := .pow (2401, 1296) e5 4
  let e19 : LowMeanIntegerExpr := .atom (24, 1)
  let e20 : LowMeanIntegerExpr := .div (2401, 31104) e18 e19
  let e21 : LowMeanIntegerExpr := .add (10153, 31104) e17 e20
  let e22 : LowMeanIntegerExpr := .pow (-16807, 7776) e5 5
  let e23 : LowMeanIntegerExpr := .atom (120, 1)
  let e24 : LowMeanIntegerExpr := .div (-16807, 933120) e22 e23
  let e25 : LowMeanIntegerExpr := .add (287783, 933120) e21 e24
  let e26 : LowMeanIntegerExpr := .pow (117649, 46656) e5 6
  let e27 : LowMeanIntegerExpr := .atom (720, 1)
  let e28 : LowMeanIntegerExpr := .div (117649, 33592320) e26 e27
  let e29 : LowMeanIntegerExpr := .add (10477837, 33592320) e25 e28
  let e30 : LowMeanIntegerExpr := .pow (-823543, 279936) e5 7
  let e31 : LowMeanIntegerExpr := .atom (5040, 1)
  let e32 : LowMeanIntegerExpr := .div (-117649, 201553920) e30 e31
  let e33 : LowMeanIntegerExpr := .add (62749373, 201553920) e29 e32
  let e34 : LowMeanIntegerExpr := .pow (5764801, 1679616) e5 8
  let e35 : LowMeanIntegerExpr := .atom (40320, 1)
  let e36 : LowMeanIntegerExpr := .div (823543, 9674588160) e34 e35
  let e37 : LowMeanIntegerExpr := .add (3012793447, 9674588160) e33 e36
  let e38 : LowMeanIntegerExpr := .mul (15063967235, 278628139008) e3 e37
  e38

def fiberWingExpr_w3_taylorRight : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (13, 25)
  let e1 : LowMeanIntegerExpr := .pow (371293, 9765625) e0 5
  let e2 : LowMeanIntegerExpr := .atom (2, 1)
  let e3 : LowMeanIntegerExpr := .atom (9, 50)
  let e4 : LowMeanIntegerExpr := .mul (9, 25) e2 e3
  let e5 : LowMeanIntegerExpr := .pow (1, 1) e4 0
  let e6 : LowMeanIntegerExpr := .atom (1, 1)
  let e7 : LowMeanIntegerExpr := .div (1, 1) e5 e6
  let e8 : LowMeanIntegerExpr := .pow (9, 25) e4 1
  let e9 : LowMeanIntegerExpr := .div (9, 25) e8 e6
  let e10 : LowMeanIntegerExpr := .add (34, 25) e7 e9
  let e11 : LowMeanIntegerExpr := .pow (81, 625) e4 2
  let e12 : LowMeanIntegerExpr := .div (81, 1250) e11 e2
  let e13 : LowMeanIntegerExpr := .add (1781, 1250) e10 e12
  let e14 : LowMeanIntegerExpr := .pow (729, 15625) e4 3
  let e15 : LowMeanIntegerExpr := .atom (6, 1)
  let e16 : LowMeanIntegerExpr := .div (243, 31250) e14 e15
  let e17 : LowMeanIntegerExpr := .add (22384, 15625) e13 e16
  let e18 : LowMeanIntegerExpr := .pow (6561, 390625) e4 4
  let e19 : LowMeanIntegerExpr := .atom (24, 1)
  let e20 : LowMeanIntegerExpr := .div (2187, 3125000) e18 e19
  let e21 : LowMeanIntegerExpr := .add (4478987, 3125000) e17 e20
  let e22 : LowMeanIntegerExpr := .mul (1663016520191, 30517578125000) e1 e21
  e22

def fiberWingExpr_w3_gap : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 1)
  let e1 : LowMeanIntegerExpr := .atom (7, 40)
  let e2 : LowMeanIntegerExpr := .add (47, 40) e0 e1
  let e3 : LowMeanIntegerExpr := .atom (2, 1)
  let e4 : LowMeanIntegerExpr := .atom (-7, 12)
  let e5 : LowMeanIntegerExpr := .pow (49, 144) e4 2
  let e6 : LowMeanIntegerExpr := .mul (49, 72) e3 e5
  let e7 : LowMeanIntegerExpr := .atom (41, 50)
  let e8 : LowMeanIntegerExpr := .add (5, 12) e0 e4
  let e9 : LowMeanIntegerExpr := .mul (41, 120) e7 e8
  let e10 : LowMeanIntegerExpr := .div (245, 123) e6 e9
  let e11 : LowMeanIntegerExpr := .neg (-245, 123) e10
  let e12 : LowMeanIntegerExpr := .add (-4019, 4920) e2 e11
  let e13 : LowMeanIntegerExpr := .atom (31, 2)
  let e14 : LowMeanIntegerExpr := .neg (-2, 1) e3
  let e15 : LowMeanIntegerExpr := .add (27, 2) e13 e14
  let e16 : LowMeanIntegerExpr := .div (27, 31) e15 e13
  let e17 : LowMeanIntegerExpr := .atom (10, 1)
  let e18 : LowMeanIntegerExpr := .atom (9, 2)
  let e19 : LowMeanIntegerExpr := .atom (13, 25)
  let e20 : LowMeanIntegerExpr := .mul (117, 50) e18 e19
  let e21 : LowMeanIntegerExpr := .neg (-117, 50) e20
  let e22 : LowMeanIntegerExpr := .add (383, 50) e17 e21
  let e23 : LowMeanIntegerExpr := .div (225, 26) e18 e19
  let e24 : LowMeanIntegerExpr := .neg (-225, 26) e23
  let e25 : LowMeanIntegerExpr := .add (-323, 325) e22 e24
  let e26 : LowMeanIntegerExpr := .mul (-8721, 10075) e16 e25
  let e27 : LowMeanIntegerExpr := .neg (8721, 10075) e26
  let e28 : LowMeanIntegerExpr := .add (483179, 9913800) e12 e27
  e28

def fiberWingExpr_w3_target : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (10, 1)
  let e1 : LowMeanIntegerExpr := .atom (9, 2)
  let e2 : LowMeanIntegerExpr := .atom (13, 25)
  let e3 : LowMeanIntegerExpr := .mul (117, 50) e1 e2
  let e4 : LowMeanIntegerExpr := .neg (-117, 50) e3
  let e5 : LowMeanIntegerExpr := .add (383, 50) e0 e4
  let e6 : LowMeanIntegerExpr := .div (225, 26) e1 e2
  let e7 : LowMeanIntegerExpr := .neg (-225, 26) e6
  let e8 : LowMeanIntegerExpr := .add (-323, 325) e5 e7
  e8

def fiberWingExpr : FiberWingIdentity → FiberWingRole → LowMeanIntegerExpr
  | .w1, .rate => fiberWingExpr_w1_rate
  | .w1, .bonus => fiberWingExpr_w1_bonus
  | .w1, .gain => fiberWingExpr_w1_gain
  | .w1, .rootSquare => fiberWingExpr_w1_rootSquare
  | .w1, .eta => fiberWingExpr_w1_eta
  | .w1, .width => fiberWingExpr_w1_width
  | .w1, .taylorLeft => fiberWingExpr_w1_taylorLeft
  | .w1, .taylorRight => fiberWingExpr_w1_taylorRight
  | .w1, .gap => fiberWingExpr_w1_gap
  | .w1, .target => fiberWingExpr_w1_target
  | .w2, .rate => fiberWingExpr_w2_rate
  | .w2, .bonus => fiberWingExpr_w2_bonus
  | .w2, .gain => fiberWingExpr_w2_gain
  | .w2, .rootSquare => fiberWingExpr_w2_rootSquare
  | .w2, .eta => fiberWingExpr_w2_eta
  | .w2, .width => fiberWingExpr_w2_width
  | .w2, .taylorLeft => fiberWingExpr_w2_taylorLeft
  | .w2, .taylorRight => fiberWingExpr_w2_taylorRight
  | .w2, .gap => fiberWingExpr_w2_gap
  | .w2, .target => fiberWingExpr_w2_target
  | .w3, .rate => fiberWingExpr_w3_rate
  | .w3, .bonus => fiberWingExpr_w3_bonus
  | .w3, .gain => fiberWingExpr_w3_gain
  | .w3, .rootSquare => fiberWingExpr_w3_rootSquare
  | .w3, .eta => fiberWingExpr_w3_eta
  | .w3, .width => fiberWingExpr_w3_width
  | .w3, .taylorLeft => fiberWingExpr_w3_taylorLeft
  | .w3, .taylorRight => fiberWingExpr_w3_taylorRight
  | .w3, .gap => fiberWingExpr_w3_gap
  | .w3, .target => fiberWingExpr_w3_target

def fiberWingIdentityAt : ℕ → FiberWingIdentity
  | 0 => .w1
  | 1 => .w2
  | _ => .w3

def fiberWingRoleAt : ℕ → FiberWingRole
  | 0 => .rate
  | 1 => .bonus
  | 2 => .gain
  | 3 => .rootSquare
  | 4 => .eta
  | 5 => .width
  | 6 => .taylorLeft
  | 7 => .taylorRight
  | 8 => .gap
  | _ => .target

end Erdos993Lean.Analytic.V213
