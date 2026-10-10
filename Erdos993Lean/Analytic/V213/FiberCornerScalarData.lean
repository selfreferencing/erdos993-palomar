module

public import Erdos993Lean.Analytic.V213.FiberCornerLogData

/-!
Accepted F14 exact logarithm bounds, six input-rate slacks and ten corners,
and F13 five class corners/eight weighted-window tests. Printed identity
is authoritative; complete formula witnesses are checked separately.
C1/C2 ell leaves are coupled endpoint values, not common lower rates.
Source: Eq89.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

def fiberCornerRateExpr_iota0_gap : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (619, 2500)
  let e1 : LowMeanIntegerExpr := .atom (243, 2000)
  let e2 : LowMeanIntegerExpr := .atom (7, 20)
  let e3 : LowMeanIntegerExpr := .atom (9, 25)
  let e4 : LowMeanIntegerExpr := .mul (63, 500) e2 e3
  let e5 : LowMeanIntegerExpr := .add (99, 400) e1 e4
  let e6 : LowMeanIntegerExpr := .neg (-99, 400) e5
  let e7 : LowMeanIntegerExpr := .add (1, 10000) e0 e6
  e7

def fiberCornerRateExpr_iota1_gap : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1309, 5000)
  let e1 : LowMeanIntegerExpr := .atom (243, 2000)
  let e2 : LowMeanIntegerExpr := .atom (7, 20)
  let e3 : LowMeanIntegerExpr := .atom (2, 5)
  let e4 : LowMeanIntegerExpr := .mul (7, 50) e2 e3
  let e5 : LowMeanIntegerExpr := .add (523, 2000) e1 e4
  let e6 : LowMeanIntegerExpr := .neg (-523, 2000) e5
  let e7 : LowMeanIntegerExpr := .add (3, 10000) e0 e6
  e7

def fiberCornerRateExpr_iota2_gap : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (2793, 10000)
  let e1 : LowMeanIntegerExpr := .atom (243, 2000)
  let e2 : LowMeanIntegerExpr := .atom (7, 20)
  let e3 : LowMeanIntegerExpr := .atom (9, 20)
  let e4 : LowMeanIntegerExpr := .mul (63, 400) e2 e3
  let e5 : LowMeanIntegerExpr := .add (279, 1000) e1 e4
  let e6 : LowMeanIntegerExpr := .neg (-279, 1000) e5
  let e7 : LowMeanIntegerExpr := .add (3, 10000) e0 e6
  e7

def fiberCornerRateExpr_iota3_gap : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (751, 2500)
  let e1 : LowMeanIntegerExpr := .atom (27, 250)
  let e2 : LowMeanIntegerExpr := .atom (48, 125)
  let e3 : LowMeanIntegerExpr := .atom (1, 2)
  let e4 : LowMeanIntegerExpr := .mul (24, 125) e2 e3
  let e5 : LowMeanIntegerExpr := .add (3, 10) e1 e4
  let e6 : LowMeanIntegerExpr := .neg (-3, 10) e5
  let e7 : LowMeanIntegerExpr := .add (1, 2500) e0 e6
  e7

def fiberCornerRateExpr_iota4_gap : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (643, 2000)
  let e1 : LowMeanIntegerExpr := .atom (27, 250)
  let e2 : LowMeanIntegerExpr := .atom (48, 125)
  let e3 : LowMeanIntegerExpr := .atom (11, 20)
  let e4 : LowMeanIntegerExpr := .mul (132, 625) e2 e3
  let e5 : LowMeanIntegerExpr := .add (399, 1250) e1 e4
  let e6 : LowMeanIntegerExpr := .neg (-399, 1250) e5
  let e7 : LowMeanIntegerExpr := .add (23, 10000) e0 e6
  e7

def fiberCornerRateExpr_iota5_gap : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (339, 1000)
  let e1 : LowMeanIntegerExpr := .atom (27, 250)
  let e2 : LowMeanIntegerExpr := .atom (48, 125)
  let e3 : LowMeanIntegerExpr := .atom (3, 5)
  let e4 : LowMeanIntegerExpr := .mul (144, 625) e2 e3
  let e5 : LowMeanIntegerExpr := .add (423, 1250) e1 e4
  let e6 : LowMeanIntegerExpr := .neg (-423, 1250) e5
  let e7 : LowMeanIntegerExpr := .add (3, 5000) e0 e6
  e7

def fiberRateCornerExpr_input30_gap : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (907, 2000)
  let e1 : LowMeanIntegerExpr := .atom (94, 125)
  let e2 : LowMeanIntegerExpr := .atom (3, 5)
  let e3 : LowMeanIntegerExpr := .mul (282, 625) e1 e2
  let e4 : LowMeanIntegerExpr := .neg (-282, 625) e3
  let e5 : LowMeanIntegerExpr := .add (23, 10000) e0 e4
  e5

def fiberRateCornerExpr_w1_gap : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (4481, 10000)
  let e1 : LowMeanIntegerExpr := .atom (771, 1000)
  let e2 : LowMeanIntegerExpr := .atom (29, 50)
  let e3 : LowMeanIntegerExpr := .mul (22359, 50000) e1 e2
  let e4 : LowMeanIntegerExpr := .neg (-22359, 50000) e3
  let e5 : LowMeanIntegerExpr := .add (23, 25000) e0 e4
  e5

def fiberRateCornerExpr_w2_gap : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1129, 2500)
  let e1 : LowMeanIntegerExpr := .atom (811, 1000)
  let e2 : LowMeanIntegerExpr := .atom (11, 20)
  let e3 : LowMeanIntegerExpr := .mul (8921, 20000) e1 e2
  let e4 : LowMeanIntegerExpr := .neg (-8921, 20000) e3
  let e5 : LowMeanIntegerExpr := .add (111, 20000) e0 e4
  e5

def fiberRateCornerExpr_c1_gap : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (279, 1000)
  let e1 : LowMeanIntegerExpr := .atom (929, 2500)
  let e2 : LowMeanIntegerExpr := .atom (3, 5)
  let e3 : LowMeanIntegerExpr := .mul (2787, 12500) e1 e2
  let e4 : LowMeanIntegerExpr := .neg (-2787, 12500) e3
  let e5 : LowMeanIntegerExpr := .add (1401, 25000) e0 e4
  e5

def fiberRateCornerExpr_c2_gap : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (423, 1250)
  let e1 : LowMeanIntegerExpr := .atom (471, 1000)
  let e2 : LowMeanIntegerExpr := .atom (69, 100)
  let e3 : LowMeanIntegerExpr := .mul (32499, 100000) e1 e2
  let e4 : LowMeanIntegerExpr := .neg (-32499, 100000) e3
  let e5 : LowMeanIntegerExpr := .add (1341, 100000) e0 e4
  e5

def fiberRateCornerExpr_c4_gap : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (939, 2000)
  let e1 : LowMeanIntegerExpr := .atom (253, 250)
  let e2 : LowMeanIntegerExpr := .atom (21, 50)
  let e3 : LowMeanIntegerExpr := .mul (5313, 12500) e1 e2
  let e4 : LowMeanIntegerExpr := .neg (-5313, 12500) e3
  let e5 : LowMeanIntegerExpr := .add (2223, 50000) e0 e4
  e5

def fiberRateCornerExpr_c5_gap : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (47, 100)
  let e1 : LowMeanIntegerExpr := .atom (213, 200)
  let e2 : LowMeanIntegerExpr := .atom (2, 5)
  let e3 : LowMeanIntegerExpr := .mul (213, 500) e1 e2
  let e4 : LowMeanIntegerExpr := .neg (-213, 500) e3
  let e5 : LowMeanIntegerExpr := .add (11, 250) e0 e4
  e5

def fiberRateCornerExpr_c6_gap : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (2223, 5000)
  let e1 : LowMeanIntegerExpr := .atom (279, 250)
  let e2 : LowMeanIntegerExpr := .atom (9, 25)
  let e3 : LowMeanIntegerExpr := .mul (2511, 6250) e1 e2
  let e4 : LowMeanIntegerExpr := .neg (-2511, 6250) e3
  let e5 : LowMeanIntegerExpr := .add (1071, 25000) e0 e4
  e5

def fiberRateCornerExpr_c7_gap : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (269, 625)
  let e1 : LowMeanIntegerExpr := .atom (1179, 1000)
  let e2 : LowMeanIntegerExpr := .atom (33, 100)
  let e3 : LowMeanIntegerExpr := .mul (38907, 100000) e1 e2
  let e4 : LowMeanIntegerExpr := .neg (-38907, 100000) e3
  let e5 : LowMeanIntegerExpr := .add (4133, 100000) e0 e4
  e5

def fiberRateCornerExpr_c8_gap : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1129, 2500)
  let e1 : LowMeanIntegerExpr := .atom (241, 200)
  let e2 : LowMeanIntegerExpr := .atom (3, 10)
  let e3 : LowMeanIntegerExpr := .mul (723, 2000) e1 e2
  let e4 : LowMeanIntegerExpr := .neg (-723, 2000) e3
  let e5 : LowMeanIntegerExpr := .add (901, 10000) e0 e4
  e5

def fiberCornerRateExpr : FiberCornerRateIdentity → LowMeanIntegerExpr
  | .iota0 => fiberCornerRateExpr_iota0_gap
  | .iota1 => fiberCornerRateExpr_iota1_gap
  | .iota2 => fiberCornerRateExpr_iota2_gap
  | .iota3 => fiberCornerRateExpr_iota3_gap
  | .iota4 => fiberCornerRateExpr_iota4_gap
  | .iota5 => fiberCornerRateExpr_iota5_gap

def fiberRateCornerExpr : FiberRateCornerIdentity → LowMeanIntegerExpr
  | .input30 => fiberRateCornerExpr_input30_gap
  | .w1 => fiberRateCornerExpr_w1_gap
  | .w2 => fiberRateCornerExpr_w2_gap
  | .c1 => fiberRateCornerExpr_c1_gap
  | .c2 => fiberRateCornerExpr_c2_gap
  | .c4 => fiberRateCornerExpr_c4_gap
  | .c5 => fiberRateCornerExpr_c5_gap
  | .c6 => fiberRateCornerExpr_c6_gap
  | .c7 => fiberRateCornerExpr_c7_gap
  | .c8 => fiberRateCornerExpr_c8_gap

end Erdos993Lean.Analytic.V213
