module

public import Erdos993Lean.Analytic.V213.FiberBudgetRows

/-!
All thirteen accepted F17 printed budget rows, keyed by their own iota
spans (distinct from F16's partition at37). Complete canonical B, strict
budget gap and printed margin trees retain every operation. Actual input
D/theta/mean leaves remain the accepted Part1 records; no second list of
55 epsilon values is introduced. Data only; two ordered checkers follow.

-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

def fiberBudgetExpr_iota_0_5_budget : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 1)
  let e1 : LowMeanIntegerExpr := .atom (2, 5)
  let e2 : LowMeanIntegerExpr := .add (7, 5) e0 e1
  let e3 : LowMeanIntegerExpr := .neg (-1, 1) e0
  let e4 : LowMeanIntegerExpr := .add (2, 5) e2 e3
  let e5 : LowMeanIntegerExpr := .atom (9, 1)
  let e6 : LowMeanIntegerExpr := .atom (6, 5)
  let e7 : LowMeanIntegerExpr := .mul (54, 5) e5 e6
  let e8 : LowMeanIntegerExpr := .atom (2, 1)
  let e9 : LowMeanIntegerExpr := .atom (45, 1)
  let e10 : LowMeanIntegerExpr := .mul (90, 1) e8 e9
  let e11 : LowMeanIntegerExpr := .div (3, 25) e7 e10
  let e12 : LowMeanIntegerExpr := .neg (-3, 25) e11
  let e13 : LowMeanIntegerExpr := .add (7, 25) e4 e12
  let e14 : LowMeanIntegerExpr := .atom (1, 2)
  let e15 : LowMeanIntegerExpr := .pow (1, 4) e14 2
  let e16 : LowMeanIntegerExpr := .neg (-1, 4) e15
  let e17 : LowMeanIntegerExpr := .add (3, 4) e0 e16
  let e18 : LowMeanIntegerExpr := .mul (135, 4) e17 e9
  let e19 : LowMeanIntegerExpr := .div (1, 135) e15 e18
  let e20 : LowMeanIntegerExpr := .neg (-1, 135) e19
  let e21 : LowMeanIntegerExpr := .add (184, 675) e13 e20
  e21

def fiberBudgetExpr_iota_0_5_strictGap : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 1)
  let e1 : LowMeanIntegerExpr := .atom (2, 5)
  let e2 : LowMeanIntegerExpr := .add (7, 5) e0 e1
  let e3 : LowMeanIntegerExpr := .neg (-1, 1) e0
  let e4 : LowMeanIntegerExpr := .add (2, 5) e2 e3
  let e5 : LowMeanIntegerExpr := .atom (9, 1)
  let e6 : LowMeanIntegerExpr := .atom (6, 5)
  let e7 : LowMeanIntegerExpr := .mul (54, 5) e5 e6
  let e8 : LowMeanIntegerExpr := .atom (2, 1)
  let e9 : LowMeanIntegerExpr := .atom (45, 1)
  let e10 : LowMeanIntegerExpr := .mul (90, 1) e8 e9
  let e11 : LowMeanIntegerExpr := .div (3, 25) e7 e10
  let e12 : LowMeanIntegerExpr := .neg (-3, 25) e11
  let e13 : LowMeanIntegerExpr := .add (7, 25) e4 e12
  let e14 : LowMeanIntegerExpr := .atom (1, 2)
  let e15 : LowMeanIntegerExpr := .pow (1, 4) e14 2
  let e16 : LowMeanIntegerExpr := .neg (-1, 4) e15
  let e17 : LowMeanIntegerExpr := .add (3, 4) e0 e16
  let e18 : LowMeanIntegerExpr := .mul (135, 4) e17 e9
  let e19 : LowMeanIntegerExpr := .div (1, 135) e15 e18
  let e20 : LowMeanIntegerExpr := .neg (-1, 135) e19
  let e21 : LowMeanIntegerExpr := .add (184, 675) e13 e20
  let e22 : LowMeanIntegerExpr := .atom (34, 125)
  let e23 : LowMeanIntegerExpr := .neg (-34, 125) e22
  let e24 : LowMeanIntegerExpr := .add (2, 3375) e21 e23
  e24

def fiberBudgetExpr_iota_0_5_margin : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (34, 125)
  let e1 : LowMeanIntegerExpr := .atom (13, 50)
  let e2 : LowMeanIntegerExpr := .neg (-13, 50) e1
  let e3 : LowMeanIntegerExpr := .add (3, 250) e0 e2
  e3

def fiberBudgetExpr_iota_6_9_budget : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 1)
  let e1 : LowMeanIntegerExpr := .atom (0, 1)
  let e2 : LowMeanIntegerExpr := .add (1, 1) e0 e1
  let e3 : LowMeanIntegerExpr := .atom (7, 10)
  let e4 : LowMeanIntegerExpr := .neg (-7, 10) e3
  let e5 : LowMeanIntegerExpr := .add (3, 10) e2 e4
  let e6 : LowMeanIntegerExpr := .atom (9, 1)
  let e7 : LowMeanIntegerExpr := .atom (6, 5)
  let e8 : LowMeanIntegerExpr := .mul (54, 5) e6 e7
  let e9 : LowMeanIntegerExpr := .atom (2, 1)
  let e10 : LowMeanIntegerExpr := .atom (23, 1)
  let e11 : LowMeanIntegerExpr := .mul (46, 1) e9 e10
  let e12 : LowMeanIntegerExpr := .div (27, 115) e8 e11
  let e13 : LowMeanIntegerExpr := .neg (-27, 115) e12
  let e14 : LowMeanIntegerExpr := .add (3, 46) e5 e13
  let e15 : LowMeanIntegerExpr := .atom (1, 4)
  let e16 : LowMeanIntegerExpr := .pow (1, 16) e15 2
  let e17 : LowMeanIntegerExpr := .neg (-1, 16) e16
  let e18 : LowMeanIntegerExpr := .add (15, 16) e0 e17
  let e19 : LowMeanIntegerExpr := .mul (345, 16) e18 e10
  let e20 : LowMeanIntegerExpr := .div (1, 345) e16 e19
  let e21 : LowMeanIntegerExpr := .neg (-1, 345) e20
  let e22 : LowMeanIntegerExpr := .add (43, 690) e14 e21
  e22

def fiberBudgetExpr_iota_6_9_strictGap : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 1)
  let e1 : LowMeanIntegerExpr := .atom (0, 1)
  let e2 : LowMeanIntegerExpr := .add (1, 1) e0 e1
  let e3 : LowMeanIntegerExpr := .atom (7, 10)
  let e4 : LowMeanIntegerExpr := .neg (-7, 10) e3
  let e5 : LowMeanIntegerExpr := .add (3, 10) e2 e4
  let e6 : LowMeanIntegerExpr := .atom (9, 1)
  let e7 : LowMeanIntegerExpr := .atom (6, 5)
  let e8 : LowMeanIntegerExpr := .mul (54, 5) e6 e7
  let e9 : LowMeanIntegerExpr := .atom (2, 1)
  let e10 : LowMeanIntegerExpr := .atom (23, 1)
  let e11 : LowMeanIntegerExpr := .mul (46, 1) e9 e10
  let e12 : LowMeanIntegerExpr := .div (27, 115) e8 e11
  let e13 : LowMeanIntegerExpr := .neg (-27, 115) e12
  let e14 : LowMeanIntegerExpr := .add (3, 46) e5 e13
  let e15 : LowMeanIntegerExpr := .atom (1, 4)
  let e16 : LowMeanIntegerExpr := .pow (1, 16) e15 2
  let e17 : LowMeanIntegerExpr := .neg (-1, 16) e16
  let e18 : LowMeanIntegerExpr := .add (15, 16) e0 e17
  let e19 : LowMeanIntegerExpr := .mul (345, 16) e18 e10
  let e20 : LowMeanIntegerExpr := .div (1, 345) e16 e19
  let e21 : LowMeanIntegerExpr := .neg (-1, 345) e20
  let e22 : LowMeanIntegerExpr := .add (43, 690) e14 e21
  let e23 : LowMeanIntegerExpr := .atom (31, 500)
  let e24 : LowMeanIntegerExpr := .neg (-31, 500) e23
  let e25 : LowMeanIntegerExpr := .add (11, 34500) e22 e24
  e25

def fiberBudgetExpr_iota_6_9_margin : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (31, 500)
  let e1 : LowMeanIntegerExpr := .atom (3, 50)
  let e2 : LowMeanIntegerExpr := .neg (-3, 50) e1
  let e3 : LowMeanIntegerExpr := .add (1, 500) e0 e2
  e3

def fiberBudgetExpr_iota_10_10_budget : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 1)
  let e1 : LowMeanIntegerExpr := .atom (0, 1)
  let e2 : LowMeanIntegerExpr := .add (1, 1) e0 e1
  let e3 : LowMeanIntegerExpr := .atom (13, 20)
  let e4 : LowMeanIntegerExpr := .neg (-13, 20) e3
  let e5 : LowMeanIntegerExpr := .add (7, 20) e2 e4
  let e6 : LowMeanIntegerExpr := .atom (9, 1)
  let e7 : LowMeanIntegerExpr := .atom (6, 5)
  let e8 : LowMeanIntegerExpr := .mul (54, 5) e6 e7
  let e9 : LowMeanIntegerExpr := .atom (2, 1)
  let e10 : LowMeanIntegerExpr := .atom (20, 1)
  let e11 : LowMeanIntegerExpr := .mul (40, 1) e9 e10
  let e12 : LowMeanIntegerExpr := .div (27, 100) e8 e11
  let e13 : LowMeanIntegerExpr := .neg (-27, 100) e12
  let e14 : LowMeanIntegerExpr := .add (2, 25) e5 e13
  let e15 : LowMeanIntegerExpr := .atom (1, 8)
  let e16 : LowMeanIntegerExpr := .pow (1, 64) e15 2
  let e17 : LowMeanIntegerExpr := .neg (-1, 64) e16
  let e18 : LowMeanIntegerExpr := .add (63, 64) e0 e17
  let e19 : LowMeanIntegerExpr := .mul (315, 16) e18 e10
  let e20 : LowMeanIntegerExpr := .div (1, 1260) e16 e19
  let e21 : LowMeanIntegerExpr := .neg (-1, 1260) e20
  let e22 : LowMeanIntegerExpr := .add (499, 6300) e14 e21
  e22

def fiberBudgetExpr_iota_10_10_strictGap : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 1)
  let e1 : LowMeanIntegerExpr := .atom (0, 1)
  let e2 : LowMeanIntegerExpr := .add (1, 1) e0 e1
  let e3 : LowMeanIntegerExpr := .atom (13, 20)
  let e4 : LowMeanIntegerExpr := .neg (-13, 20) e3
  let e5 : LowMeanIntegerExpr := .add (7, 20) e2 e4
  let e6 : LowMeanIntegerExpr := .atom (9, 1)
  let e7 : LowMeanIntegerExpr := .atom (6, 5)
  let e8 : LowMeanIntegerExpr := .mul (54, 5) e6 e7
  let e9 : LowMeanIntegerExpr := .atom (2, 1)
  let e10 : LowMeanIntegerExpr := .atom (20, 1)
  let e11 : LowMeanIntegerExpr := .mul (40, 1) e9 e10
  let e12 : LowMeanIntegerExpr := .div (27, 100) e8 e11
  let e13 : LowMeanIntegerExpr := .neg (-27, 100) e12
  let e14 : LowMeanIntegerExpr := .add (2, 25) e5 e13
  let e15 : LowMeanIntegerExpr := .atom (1, 8)
  let e16 : LowMeanIntegerExpr := .pow (1, 64) e15 2
  let e17 : LowMeanIntegerExpr := .neg (-1, 64) e16
  let e18 : LowMeanIntegerExpr := .add (63, 64) e0 e17
  let e19 : LowMeanIntegerExpr := .mul (315, 16) e18 e10
  let e20 : LowMeanIntegerExpr := .div (1, 1260) e16 e19
  let e21 : LowMeanIntegerExpr := .neg (-1, 1260) e20
  let e22 : LowMeanIntegerExpr := .add (499, 6300) e14 e21
  let e23 : LowMeanIntegerExpr := .atom (79, 1000)
  let e24 : LowMeanIntegerExpr := .neg (-79, 1000) e23
  let e25 : LowMeanIntegerExpr := .add (13, 63000) e22 e24
  e25

def fiberBudgetExpr_iota_10_10_margin : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (79, 1000)
  let e1 : LowMeanIntegerExpr := .atom (77, 1000)
  let e2 : LowMeanIntegerExpr := .neg (-77, 1000) e1
  let e3 : LowMeanIntegerExpr := .add (1, 500) e0 e2
  e3

def fiberBudgetExpr_iota_11_29_budget : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 1)
  let e1 : LowMeanIntegerExpr := .atom (0, 1)
  let e2 : LowMeanIntegerExpr := .add (1, 1) e0 e1
  let e3 : LowMeanIntegerExpr := .atom (3, 5)
  let e4 : LowMeanIntegerExpr := .neg (-3, 5) e3
  let e5 : LowMeanIntegerExpr := .add (2, 5) e2 e4
  let e6 : LowMeanIntegerExpr := .atom (9, 1)
  let e7 : LowMeanIntegerExpr := .atom (6, 5)
  let e8 : LowMeanIntegerExpr := .mul (54, 5) e6 e7
  let e9 : LowMeanIntegerExpr := .atom (2, 1)
  let e10 : LowMeanIntegerExpr := .atom (19, 1)
  let e11 : LowMeanIntegerExpr := .mul (38, 1) e9 e10
  let e12 : LowMeanIntegerExpr := .div (27, 95) e8 e11
  let e13 : LowMeanIntegerExpr := .neg (-27, 95) e12
  let e14 : LowMeanIntegerExpr := .add (11, 95) e5 e13
  let e15 : LowMeanIntegerExpr := .atom (1, 8)
  let e16 : LowMeanIntegerExpr := .pow (1, 64) e15 2
  let e17 : LowMeanIntegerExpr := .neg (-1, 64) e16
  let e18 : LowMeanIntegerExpr := .add (63, 64) e0 e17
  let e19 : LowMeanIntegerExpr := .mul (1197, 64) e18 e10
  let e20 : LowMeanIntegerExpr := .div (1, 1197) e16 e19
  let e21 : LowMeanIntegerExpr := .neg (-1, 1197) e20
  let e22 : LowMeanIntegerExpr := .add (688, 5985) e14 e21
  e22

def fiberBudgetExpr_iota_11_29_strictGap : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 1)
  let e1 : LowMeanIntegerExpr := .atom (0, 1)
  let e2 : LowMeanIntegerExpr := .add (1, 1) e0 e1
  let e3 : LowMeanIntegerExpr := .atom (3, 5)
  let e4 : LowMeanIntegerExpr := .neg (-3, 5) e3
  let e5 : LowMeanIntegerExpr := .add (2, 5) e2 e4
  let e6 : LowMeanIntegerExpr := .atom (9, 1)
  let e7 : LowMeanIntegerExpr := .atom (6, 5)
  let e8 : LowMeanIntegerExpr := .mul (54, 5) e6 e7
  let e9 : LowMeanIntegerExpr := .atom (2, 1)
  let e10 : LowMeanIntegerExpr := .atom (19, 1)
  let e11 : LowMeanIntegerExpr := .mul (38, 1) e9 e10
  let e12 : LowMeanIntegerExpr := .div (27, 95) e8 e11
  let e13 : LowMeanIntegerExpr := .neg (-27, 95) e12
  let e14 : LowMeanIntegerExpr := .add (11, 95) e5 e13
  let e15 : LowMeanIntegerExpr := .atom (1, 8)
  let e16 : LowMeanIntegerExpr := .pow (1, 64) e15 2
  let e17 : LowMeanIntegerExpr := .neg (-1, 64) e16
  let e18 : LowMeanIntegerExpr := .add (63, 64) e0 e17
  let e19 : LowMeanIntegerExpr := .mul (1197, 64) e18 e10
  let e20 : LowMeanIntegerExpr := .div (1, 1197) e16 e19
  let e21 : LowMeanIntegerExpr := .neg (-1, 1197) e20
  let e22 : LowMeanIntegerExpr := .add (688, 5985) e14 e21
  let e23 : LowMeanIntegerExpr := .atom (57, 500)
  let e24 : LowMeanIntegerExpr := .neg (-57, 500) e23
  let e25 : LowMeanIntegerExpr := .add (571, 598500) e22 e24
  e25

def fiberBudgetExpr_iota_11_29_margin : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (57, 500)
  let e1 : LowMeanIntegerExpr := .atom (11, 100)
  let e2 : LowMeanIntegerExpr := .neg (-11, 100) e1
  let e3 : LowMeanIntegerExpr := .add (1, 250) e0 e2
  e3

def fiberBudgetExpr_iota_30_36_budget : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 1)
  let e1 : LowMeanIntegerExpr := .atom (0, 1)
  let e2 : LowMeanIntegerExpr := .add (1, 1) e0 e1
  let e3 : LowMeanIntegerExpr := .atom (3, 5)
  let e4 : LowMeanIntegerExpr := .neg (-3, 5) e3
  let e5 : LowMeanIntegerExpr := .add (2, 5) e2 e4
  let e6 : LowMeanIntegerExpr := .atom (9, 1)
  let e7 : LowMeanIntegerExpr := .atom (6, 5)
  let e8 : LowMeanIntegerExpr := .mul (54, 5) e6 e7
  let e9 : LowMeanIntegerExpr := .atom (2, 1)
  let e10 : LowMeanIntegerExpr := .atom (20, 1)
  let e11 : LowMeanIntegerExpr := .mul (40, 1) e9 e10
  let e12 : LowMeanIntegerExpr := .div (27, 100) e8 e11
  let e13 : LowMeanIntegerExpr := .neg (-27, 100) e12
  let e14 : LowMeanIntegerExpr := .add (13, 100) e5 e13
  let e15 : LowMeanIntegerExpr := .atom (1, 8)
  let e16 : LowMeanIntegerExpr := .pow (1, 64) e15 2
  let e17 : LowMeanIntegerExpr := .neg (-1, 64) e16
  let e18 : LowMeanIntegerExpr := .add (63, 64) e0 e17
  let e19 : LowMeanIntegerExpr := .mul (315, 16) e18 e10
  let e20 : LowMeanIntegerExpr := .div (1, 1260) e16 e19
  let e21 : LowMeanIntegerExpr := .neg (-1, 1260) e20
  let e22 : LowMeanIntegerExpr := .add (407, 3150) e14 e21
  e22

def fiberBudgetExpr_iota_30_36_strictGap : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 1)
  let e1 : LowMeanIntegerExpr := .atom (0, 1)
  let e2 : LowMeanIntegerExpr := .add (1, 1) e0 e1
  let e3 : LowMeanIntegerExpr := .atom (3, 5)
  let e4 : LowMeanIntegerExpr := .neg (-3, 5) e3
  let e5 : LowMeanIntegerExpr := .add (2, 5) e2 e4
  let e6 : LowMeanIntegerExpr := .atom (9, 1)
  let e7 : LowMeanIntegerExpr := .atom (6, 5)
  let e8 : LowMeanIntegerExpr := .mul (54, 5) e6 e7
  let e9 : LowMeanIntegerExpr := .atom (2, 1)
  let e10 : LowMeanIntegerExpr := .atom (20, 1)
  let e11 : LowMeanIntegerExpr := .mul (40, 1) e9 e10
  let e12 : LowMeanIntegerExpr := .div (27, 100) e8 e11
  let e13 : LowMeanIntegerExpr := .neg (-27, 100) e12
  let e14 : LowMeanIntegerExpr := .add (13, 100) e5 e13
  let e15 : LowMeanIntegerExpr := .atom (1, 8)
  let e16 : LowMeanIntegerExpr := .pow (1, 64) e15 2
  let e17 : LowMeanIntegerExpr := .neg (-1, 64) e16
  let e18 : LowMeanIntegerExpr := .add (63, 64) e0 e17
  let e19 : LowMeanIntegerExpr := .mul (315, 16) e18 e10
  let e20 : LowMeanIntegerExpr := .div (1, 1260) e16 e19
  let e21 : LowMeanIntegerExpr := .neg (-1, 1260) e20
  let e22 : LowMeanIntegerExpr := .add (407, 3150) e14 e21
  let e23 : LowMeanIntegerExpr := .atom (129, 1000)
  let e24 : LowMeanIntegerExpr := .neg (-129, 1000) e23
  let e25 : LowMeanIntegerExpr := .add (13, 63000) e22 e24
  e25

def fiberBudgetExpr_iota_30_36_margin : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (129, 1000)
  let e1 : LowMeanIntegerExpr := .atom (1, 8)
  let e2 : LowMeanIntegerExpr := .neg (-1, 8) e1
  let e3 : LowMeanIntegerExpr := .add (1, 250) e0 e2
  e3

def fiberBudgetExpr_iota_37_37_budget : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 1)
  let e1 : LowMeanIntegerExpr := .atom (0, 1)
  let e2 : LowMeanIntegerExpr := .add (1, 1) e0 e1
  let e3 : LowMeanIntegerExpr := .atom (3, 5)
  let e4 : LowMeanIntegerExpr := .neg (-3, 5) e3
  let e5 : LowMeanIntegerExpr := .add (2, 5) e2 e4
  let e6 : LowMeanIntegerExpr := .atom (9, 1)
  let e7 : LowMeanIntegerExpr := .atom (6, 5)
  let e8 : LowMeanIntegerExpr := .mul (54, 5) e6 e7
  let e9 : LowMeanIntegerExpr := .atom (2, 1)
  let e10 : LowMeanIntegerExpr := .atom (26, 1)
  let e11 : LowMeanIntegerExpr := .mul (52, 1) e9 e10
  let e12 : LowMeanIntegerExpr := .div (27, 130) e8 e11
  let e13 : LowMeanIntegerExpr := .neg (-27, 130) e12
  let e14 : LowMeanIntegerExpr := .add (5, 26) e5 e13
  let e15 : LowMeanIntegerExpr := .atom (1, 6)
  let e16 : LowMeanIntegerExpr := .pow (1, 36) e15 2
  let e17 : LowMeanIntegerExpr := .neg (-1, 36) e16
  let e18 : LowMeanIntegerExpr := .add (35, 36) e0 e17
  let e19 : LowMeanIntegerExpr := .mul (455, 18) e18 e10
  let e20 : LowMeanIntegerExpr := .div (1, 910) e16 e19
  let e21 : LowMeanIntegerExpr := .neg (-1, 910) e20
  let e22 : LowMeanIntegerExpr := .add (87, 455) e14 e21
  e22

def fiberBudgetExpr_iota_37_37_strictGap : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 1)
  let e1 : LowMeanIntegerExpr := .atom (0, 1)
  let e2 : LowMeanIntegerExpr := .add (1, 1) e0 e1
  let e3 : LowMeanIntegerExpr := .atom (3, 5)
  let e4 : LowMeanIntegerExpr := .neg (-3, 5) e3
  let e5 : LowMeanIntegerExpr := .add (2, 5) e2 e4
  let e6 : LowMeanIntegerExpr := .atom (9, 1)
  let e7 : LowMeanIntegerExpr := .atom (6, 5)
  let e8 : LowMeanIntegerExpr := .mul (54, 5) e6 e7
  let e9 : LowMeanIntegerExpr := .atom (2, 1)
  let e10 : LowMeanIntegerExpr := .atom (26, 1)
  let e11 : LowMeanIntegerExpr := .mul (52, 1) e9 e10
  let e12 : LowMeanIntegerExpr := .div (27, 130) e8 e11
  let e13 : LowMeanIntegerExpr := .neg (-27, 130) e12
  let e14 : LowMeanIntegerExpr := .add (5, 26) e5 e13
  let e15 : LowMeanIntegerExpr := .atom (1, 6)
  let e16 : LowMeanIntegerExpr := .pow (1, 36) e15 2
  let e17 : LowMeanIntegerExpr := .neg (-1, 36) e16
  let e18 : LowMeanIntegerExpr := .add (35, 36) e0 e17
  let e19 : LowMeanIntegerExpr := .mul (455, 18) e18 e10
  let e20 : LowMeanIntegerExpr := .div (1, 910) e16 e19
  let e21 : LowMeanIntegerExpr := .neg (-1, 910) e20
  let e22 : LowMeanIntegerExpr := .add (87, 455) e14 e21
  let e23 : LowMeanIntegerExpr := .atom (191, 1000)
  let e24 : LowMeanIntegerExpr := .neg (-191, 1000) e23
  let e25 : LowMeanIntegerExpr := .add (19, 91000) e22 e24
  e25

def fiberBudgetExpr_iota_37_37_margin : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (191, 1000)
  let e1 : LowMeanIntegerExpr := .atom (1, 10)
  let e2 : LowMeanIntegerExpr := .neg (-1, 10) e1
  let e3 : LowMeanIntegerExpr := .add (91, 1000) e0 e2
  e3

def fiberBudgetExpr_iota_38_39_budget : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 1)
  let e1 : LowMeanIntegerExpr := .atom (0, 1)
  let e2 : LowMeanIntegerExpr := .add (1, 1) e0 e1
  let e3 : LowMeanIntegerExpr := .atom (7, 10)
  let e4 : LowMeanIntegerExpr := .neg (-7, 10) e3
  let e5 : LowMeanIntegerExpr := .add (3, 10) e2 e4
  let e6 : LowMeanIntegerExpr := .atom (9, 1)
  let e7 : LowMeanIntegerExpr := .atom (7, 5)
  let e8 : LowMeanIntegerExpr := .mul (63, 5) e6 e7
  let e9 : LowMeanIntegerExpr := .atom (2, 1)
  let e10 : LowMeanIntegerExpr := .atom (32, 1)
  let e11 : LowMeanIntegerExpr := .mul (64, 1) e9 e10
  let e12 : LowMeanIntegerExpr := .div (63, 320) e8 e11
  let e13 : LowMeanIntegerExpr := .neg (-63, 320) e12
  let e14 : LowMeanIntegerExpr := .add (33, 320) e5 e13
  let e15 : LowMeanIntegerExpr := .atom (1, 6)
  let e16 : LowMeanIntegerExpr := .pow (1, 36) e15 2
  let e17 : LowMeanIntegerExpr := .neg (-1, 36) e16
  let e18 : LowMeanIntegerExpr := .add (35, 36) e0 e17
  let e19 : LowMeanIntegerExpr := .mul (280, 9) e18 e10
  let e20 : LowMeanIntegerExpr := .div (1, 1120) e16 e19
  let e21 : LowMeanIntegerExpr := .neg (-1, 1120) e20
  let e22 : LowMeanIntegerExpr := .add (229, 2240) e14 e21
  e22

def fiberBudgetExpr_iota_38_39_strictGap : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 1)
  let e1 : LowMeanIntegerExpr := .atom (0, 1)
  let e2 : LowMeanIntegerExpr := .add (1, 1) e0 e1
  let e3 : LowMeanIntegerExpr := .atom (7, 10)
  let e4 : LowMeanIntegerExpr := .neg (-7, 10) e3
  let e5 : LowMeanIntegerExpr := .add (3, 10) e2 e4
  let e6 : LowMeanIntegerExpr := .atom (9, 1)
  let e7 : LowMeanIntegerExpr := .atom (7, 5)
  let e8 : LowMeanIntegerExpr := .mul (63, 5) e6 e7
  let e9 : LowMeanIntegerExpr := .atom (2, 1)
  let e10 : LowMeanIntegerExpr := .atom (32, 1)
  let e11 : LowMeanIntegerExpr := .mul (64, 1) e9 e10
  let e12 : LowMeanIntegerExpr := .div (63, 320) e8 e11
  let e13 : LowMeanIntegerExpr := .neg (-63, 320) e12
  let e14 : LowMeanIntegerExpr := .add (33, 320) e5 e13
  let e15 : LowMeanIntegerExpr := .atom (1, 6)
  let e16 : LowMeanIntegerExpr := .pow (1, 36) e15 2
  let e17 : LowMeanIntegerExpr := .neg (-1, 36) e16
  let e18 : LowMeanIntegerExpr := .add (35, 36) e0 e17
  let e19 : LowMeanIntegerExpr := .mul (280, 9) e18 e10
  let e20 : LowMeanIntegerExpr := .div (1, 1120) e16 e19
  let e21 : LowMeanIntegerExpr := .neg (-1, 1120) e20
  let e22 : LowMeanIntegerExpr := .add (229, 2240) e14 e21
  let e23 : LowMeanIntegerExpr := .atom (51, 500)
  let e24 : LowMeanIntegerExpr := .neg (-51, 500) e23
  let e25 : LowMeanIntegerExpr := .add (13, 56000) e22 e24
  e25

def fiberBudgetExpr_iota_38_39_margin : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (51, 500)
  let e1 : LowMeanIntegerExpr := .atom (1, 10)
  let e2 : LowMeanIntegerExpr := .neg (-1, 10) e1
  let e3 : LowMeanIntegerExpr := .add (1, 500) e0 e2
  e3

def fiberBudgetExpr_iota_40_43_budget : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 1)
  let e1 : LowMeanIntegerExpr := .atom (0, 1)
  let e2 : LowMeanIntegerExpr := .add (1, 1) e0 e1
  let e3 : LowMeanIntegerExpr := .atom (7, 10)
  let e4 : LowMeanIntegerExpr := .neg (-7, 10) e3
  let e5 : LowMeanIntegerExpr := .add (3, 10) e2 e4
  let e6 : LowMeanIntegerExpr := .atom (9, 1)
  let e7 : LowMeanIntegerExpr := .atom (8, 5)
  let e8 : LowMeanIntegerExpr := .mul (72, 5) e6 e7
  let e9 : LowMeanIntegerExpr := .atom (2, 1)
  let e10 : LowMeanIntegerExpr := .atom (50, 1)
  let e11 : LowMeanIntegerExpr := .mul (100, 1) e9 e10
  let e12 : LowMeanIntegerExpr := .div (18, 125) e8 e11
  let e13 : LowMeanIntegerExpr := .neg (-18, 125) e12
  let e14 : LowMeanIntegerExpr := .add (39, 250) e5 e13
  let e15 : LowMeanIntegerExpr := .atom (1, 4)
  let e16 : LowMeanIntegerExpr := .pow (1, 16) e15 2
  let e17 : LowMeanIntegerExpr := .neg (-1, 16) e16
  let e18 : LowMeanIntegerExpr := .add (15, 16) e0 e17
  let e19 : LowMeanIntegerExpr := .mul (375, 8) e18 e10
  let e20 : LowMeanIntegerExpr := .div (1, 750) e16 e19
  let e21 : LowMeanIntegerExpr := .neg (-1, 750) e20
  let e22 : LowMeanIntegerExpr := .add (58, 375) e14 e21
  e22

def fiberBudgetExpr_iota_40_43_strictGap : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 1)
  let e1 : LowMeanIntegerExpr := .atom (0, 1)
  let e2 : LowMeanIntegerExpr := .add (1, 1) e0 e1
  let e3 : LowMeanIntegerExpr := .atom (7, 10)
  let e4 : LowMeanIntegerExpr := .neg (-7, 10) e3
  let e5 : LowMeanIntegerExpr := .add (3, 10) e2 e4
  let e6 : LowMeanIntegerExpr := .atom (9, 1)
  let e7 : LowMeanIntegerExpr := .atom (8, 5)
  let e8 : LowMeanIntegerExpr := .mul (72, 5) e6 e7
  let e9 : LowMeanIntegerExpr := .atom (2, 1)
  let e10 : LowMeanIntegerExpr := .atom (50, 1)
  let e11 : LowMeanIntegerExpr := .mul (100, 1) e9 e10
  let e12 : LowMeanIntegerExpr := .div (18, 125) e8 e11
  let e13 : LowMeanIntegerExpr := .neg (-18, 125) e12
  let e14 : LowMeanIntegerExpr := .add (39, 250) e5 e13
  let e15 : LowMeanIntegerExpr := .atom (1, 4)
  let e16 : LowMeanIntegerExpr := .pow (1, 16) e15 2
  let e17 : LowMeanIntegerExpr := .neg (-1, 16) e16
  let e18 : LowMeanIntegerExpr := .add (15, 16) e0 e17
  let e19 : LowMeanIntegerExpr := .mul (375, 8) e18 e10
  let e20 : LowMeanIntegerExpr := .div (1, 750) e16 e19
  let e21 : LowMeanIntegerExpr := .neg (-1, 750) e20
  let e22 : LowMeanIntegerExpr := .add (58, 375) e14 e21
  let e23 : LowMeanIntegerExpr := .atom (77, 500)
  let e24 : LowMeanIntegerExpr := .neg (-77, 500) e23
  let e25 : LowMeanIntegerExpr := .add (1, 1500) e22 e24
  e25

def fiberBudgetExpr_iota_40_43_margin : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (77, 500)
  let e1 : LowMeanIntegerExpr := .atom (3, 25)
  let e2 : LowMeanIntegerExpr := .neg (-3, 25) e1
  let e3 : LowMeanIntegerExpr := .add (17, 500) e0 e2
  e3

def fiberBudgetExpr_iota_44_44_budget : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 1)
  let e1 : LowMeanIntegerExpr := .atom (3, 20)
  let e2 : LowMeanIntegerExpr := .add (23, 20) e0 e1
  let e3 : LowMeanIntegerExpr := .atom (9, 10)
  let e4 : LowMeanIntegerExpr := .neg (-9, 10) e3
  let e5 : LowMeanIntegerExpr := .add (1, 4) e2 e4
  let e6 : LowMeanIntegerExpr := .atom (9, 1)
  let e7 : LowMeanIntegerExpr := .atom (8, 5)
  let e8 : LowMeanIntegerExpr := .mul (72, 5) e6 e7
  let e9 : LowMeanIntegerExpr := .atom (2, 1)
  let e10 : LowMeanIntegerExpr := .atom (40, 1)
  let e11 : LowMeanIntegerExpr := .mul (80, 1) e9 e10
  let e12 : LowMeanIntegerExpr := .div (9, 50) e8 e11
  let e13 : LowMeanIntegerExpr := .neg (-9, 50) e12
  let e14 : LowMeanIntegerExpr := .add (7, 100) e5 e13
  let e15 : LowMeanIntegerExpr := .atom (7, 25)
  let e16 : LowMeanIntegerExpr := .pow (49, 625) e15 2
  let e17 : LowMeanIntegerExpr := .neg (-49, 625) e16
  let e18 : LowMeanIntegerExpr := .add (576, 625) e0 e17
  let e19 : LowMeanIntegerExpr := .mul (4608, 125) e18 e10
  let e20 : LowMeanIntegerExpr := .div (49, 23040) e16 e19
  let e21 : LowMeanIntegerExpr := .neg (-49, 23040) e20
  let e22 : LowMeanIntegerExpr := .add (7819, 115200) e14 e21
  e22

def fiberBudgetExpr_iota_44_44_strictGap : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 1)
  let e1 : LowMeanIntegerExpr := .atom (3, 20)
  let e2 : LowMeanIntegerExpr := .add (23, 20) e0 e1
  let e3 : LowMeanIntegerExpr := .atom (9, 10)
  let e4 : LowMeanIntegerExpr := .neg (-9, 10) e3
  let e5 : LowMeanIntegerExpr := .add (1, 4) e2 e4
  let e6 : LowMeanIntegerExpr := .atom (9, 1)
  let e7 : LowMeanIntegerExpr := .atom (8, 5)
  let e8 : LowMeanIntegerExpr := .mul (72, 5) e6 e7
  let e9 : LowMeanIntegerExpr := .atom (2, 1)
  let e10 : LowMeanIntegerExpr := .atom (40, 1)
  let e11 : LowMeanIntegerExpr := .mul (80, 1) e9 e10
  let e12 : LowMeanIntegerExpr := .div (9, 50) e8 e11
  let e13 : LowMeanIntegerExpr := .neg (-9, 50) e12
  let e14 : LowMeanIntegerExpr := .add (7, 100) e5 e13
  let e15 : LowMeanIntegerExpr := .atom (7, 25)
  let e16 : LowMeanIntegerExpr := .pow (49, 625) e15 2
  let e17 : LowMeanIntegerExpr := .neg (-49, 625) e16
  let e18 : LowMeanIntegerExpr := .add (576, 625) e0 e17
  let e19 : LowMeanIntegerExpr := .mul (4608, 125) e18 e10
  let e20 : LowMeanIntegerExpr := .div (49, 23040) e16 e19
  let e21 : LowMeanIntegerExpr := .neg (-49, 23040) e20
  let e22 : LowMeanIntegerExpr := .add (7819, 115200) e14 e21
  let e23 : LowMeanIntegerExpr := .atom (67, 1000)
  let e24 : LowMeanIntegerExpr := .neg (-67, 1000) e23
  let e25 : LowMeanIntegerExpr := .add (503, 576000) e22 e24
  e25

def fiberBudgetExpr_iota_44_44_margin : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (67, 1000)
  let e1 : LowMeanIntegerExpr := .atom (53, 1000)
  let e2 : LowMeanIntegerExpr := .neg (-53, 1000) e1
  let e3 : LowMeanIntegerExpr := .add (7, 500) e0 e2
  e3

def fiberBudgetExpr_iota_45_46_budget : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 1)
  let e1 : LowMeanIntegerExpr := .atom (3, 20)
  let e2 : LowMeanIntegerExpr := .add (23, 20) e0 e1
  let e3 : LowMeanIntegerExpr := .atom (19, 20)
  let e4 : LowMeanIntegerExpr := .neg (-19, 20) e3
  let e5 : LowMeanIntegerExpr := .add (1, 5) e2 e4
  let e6 : LowMeanIntegerExpr := .atom (9, 1)
  let e7 : LowMeanIntegerExpr := .atom (8, 5)
  let e8 : LowMeanIntegerExpr := .mul (72, 5) e6 e7
  let e9 : LowMeanIntegerExpr := .atom (2, 1)
  let e10 : LowMeanIntegerExpr := .atom (45, 1)
  let e11 : LowMeanIntegerExpr := .mul (90, 1) e9 e10
  let e12 : LowMeanIntegerExpr := .div (4, 25) e8 e11
  let e13 : LowMeanIntegerExpr := .neg (-4, 25) e12
  let e14 : LowMeanIntegerExpr := .add (1, 25) e5 e13
  let e15 : LowMeanIntegerExpr := .atom (7, 25)
  let e16 : LowMeanIntegerExpr := .pow (49, 625) e15 2
  let e17 : LowMeanIntegerExpr := .neg (-49, 625) e16
  let e18 : LowMeanIntegerExpr := .add (576, 625) e0 e17
  let e19 : LowMeanIntegerExpr := .mul (5184, 125) e18 e10
  let e20 : LowMeanIntegerExpr := .div (49, 25920) e16 e19
  let e21 : LowMeanIntegerExpr := .neg (-49, 25920) e20
  let e22 : LowMeanIntegerExpr := .add (4939, 129600) e14 e21
  e22

def fiberBudgetExpr_iota_45_46_strictGap : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 1)
  let e1 : LowMeanIntegerExpr := .atom (3, 20)
  let e2 : LowMeanIntegerExpr := .add (23, 20) e0 e1
  let e3 : LowMeanIntegerExpr := .atom (19, 20)
  let e4 : LowMeanIntegerExpr := .neg (-19, 20) e3
  let e5 : LowMeanIntegerExpr := .add (1, 5) e2 e4
  let e6 : LowMeanIntegerExpr := .atom (9, 1)
  let e7 : LowMeanIntegerExpr := .atom (8, 5)
  let e8 : LowMeanIntegerExpr := .mul (72, 5) e6 e7
  let e9 : LowMeanIntegerExpr := .atom (2, 1)
  let e10 : LowMeanIntegerExpr := .atom (45, 1)
  let e11 : LowMeanIntegerExpr := .mul (90, 1) e9 e10
  let e12 : LowMeanIntegerExpr := .div (4, 25) e8 e11
  let e13 : LowMeanIntegerExpr := .neg (-4, 25) e12
  let e14 : LowMeanIntegerExpr := .add (1, 25) e5 e13
  let e15 : LowMeanIntegerExpr := .atom (7, 25)
  let e16 : LowMeanIntegerExpr := .pow (49, 625) e15 2
  let e17 : LowMeanIntegerExpr := .neg (-49, 625) e16
  let e18 : LowMeanIntegerExpr := .add (576, 625) e0 e17
  let e19 : LowMeanIntegerExpr := .mul (5184, 125) e18 e10
  let e20 : LowMeanIntegerExpr := .div (49, 25920) e16 e19
  let e21 : LowMeanIntegerExpr := .neg (-49, 25920) e20
  let e22 : LowMeanIntegerExpr := .add (4939, 129600) e14 e21
  let e23 : LowMeanIntegerExpr := .atom (19, 500)
  let e24 : LowMeanIntegerExpr := .neg (-19, 500) e23
  let e25 : LowMeanIntegerExpr := .add (71, 648000) e22 e24
  e25

def fiberBudgetExpr_iota_45_46_margin : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (19, 500)
  let e1 : LowMeanIntegerExpr := .atom (17, 500)
  let e2 : LowMeanIntegerExpr := .neg (-17, 500) e1
  let e3 : LowMeanIntegerExpr := .add (1, 250) e0 e2
  e3

def fiberBudgetExpr_iota_47_49_budget : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 1)
  let e1 : LowMeanIntegerExpr := .atom (3, 10)
  let e2 : LowMeanIntegerExpr := .add (13, 10) e0 e1
  let e3 : LowMeanIntegerExpr := .neg (-1, 1) e0
  let e4 : LowMeanIntegerExpr := .add (3, 10) e2 e3
  let e5 : LowMeanIntegerExpr := .atom (9, 1)
  let e6 : LowMeanIntegerExpr := .atom (9, 5)
  let e7 : LowMeanIntegerExpr := .mul (81, 5) e5 e6
  let e8 : LowMeanIntegerExpr := .atom (2, 1)
  let e9 : LowMeanIntegerExpr := .atom (50, 1)
  let e10 : LowMeanIntegerExpr := .mul (100, 1) e8 e9
  let e11 : LowMeanIntegerExpr := .div (81, 500) e7 e10
  let e12 : LowMeanIntegerExpr := .neg (-81, 500) e11
  let e13 : LowMeanIntegerExpr := .add (69, 500) e4 e12
  let e14 : LowMeanIntegerExpr := .atom (2, 5)
  let e15 : LowMeanIntegerExpr := .pow (4, 25) e14 2
  let e16 : LowMeanIntegerExpr := .neg (-4, 25) e15
  let e17 : LowMeanIntegerExpr := .add (21, 25) e0 e16
  let e18 : LowMeanIntegerExpr := .mul (42, 1) e17 e9
  let e19 : LowMeanIntegerExpr := .div (2, 525) e15 e18
  let e20 : LowMeanIntegerExpr := .neg (-2, 525) e19
  let e21 : LowMeanIntegerExpr := .add (1409, 10500) e13 e20
  e21

def fiberBudgetExpr_iota_47_49_strictGap : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 1)
  let e1 : LowMeanIntegerExpr := .atom (3, 10)
  let e2 : LowMeanIntegerExpr := .add (13, 10) e0 e1
  let e3 : LowMeanIntegerExpr := .neg (-1, 1) e0
  let e4 : LowMeanIntegerExpr := .add (3, 10) e2 e3
  let e5 : LowMeanIntegerExpr := .atom (9, 1)
  let e6 : LowMeanIntegerExpr := .atom (9, 5)
  let e7 : LowMeanIntegerExpr := .mul (81, 5) e5 e6
  let e8 : LowMeanIntegerExpr := .atom (2, 1)
  let e9 : LowMeanIntegerExpr := .atom (50, 1)
  let e10 : LowMeanIntegerExpr := .mul (100, 1) e8 e9
  let e11 : LowMeanIntegerExpr := .div (81, 500) e7 e10
  let e12 : LowMeanIntegerExpr := .neg (-81, 500) e11
  let e13 : LowMeanIntegerExpr := .add (69, 500) e4 e12
  let e14 : LowMeanIntegerExpr := .atom (2, 5)
  let e15 : LowMeanIntegerExpr := .pow (4, 25) e14 2
  let e16 : LowMeanIntegerExpr := .neg (-4, 25) e15
  let e17 : LowMeanIntegerExpr := .add (21, 25) e0 e16
  let e18 : LowMeanIntegerExpr := .mul (42, 1) e17 e9
  let e19 : LowMeanIntegerExpr := .div (2, 525) e15 e18
  let e20 : LowMeanIntegerExpr := .neg (-2, 525) e19
  let e21 : LowMeanIntegerExpr := .add (1409, 10500) e13 e20
  let e22 : LowMeanIntegerExpr := .atom (67, 500)
  let e23 : LowMeanIntegerExpr := .neg (-67, 500) e22
  let e24 : LowMeanIntegerExpr := .add (1, 5250) e21 e23
  e24

def fiberBudgetExpr_iota_47_49_margin : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (67, 500)
  let e1 : LowMeanIntegerExpr := .atom (11, 100)
  let e2 : LowMeanIntegerExpr := .neg (-11, 100) e1
  let e3 : LowMeanIntegerExpr := .add (3, 125) e0 e2
  e3

def fiberBudgetExpr_iota_50_52_budget : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 1)
  let e1 : LowMeanIntegerExpr := .atom (3, 10)
  let e2 : LowMeanIntegerExpr := .add (13, 10) e0 e1
  let e3 : LowMeanIntegerExpr := .neg (-1, 1) e0
  let e4 : LowMeanIntegerExpr := .add (3, 10) e2 e3
  let e5 : LowMeanIntegerExpr := .atom (9, 1)
  let e6 : LowMeanIntegerExpr := .atom (21, 10)
  let e7 : LowMeanIntegerExpr := .mul (189, 10) e5 e6
  let e8 : LowMeanIntegerExpr := .atom (2, 1)
  let e9 : LowMeanIntegerExpr := .atom (50, 1)
  let e10 : LowMeanIntegerExpr := .mul (100, 1) e8 e9
  let e11 : LowMeanIntegerExpr := .div (189, 1000) e7 e10
  let e12 : LowMeanIntegerExpr := .neg (-189, 1000) e11
  let e13 : LowMeanIntegerExpr := .add (111, 1000) e4 e12
  let e14 : LowMeanIntegerExpr := .atom (2, 5)
  let e15 : LowMeanIntegerExpr := .pow (4, 25) e14 2
  let e16 : LowMeanIntegerExpr := .neg (-4, 25) e15
  let e17 : LowMeanIntegerExpr := .add (21, 25) e0 e16
  let e18 : LowMeanIntegerExpr := .mul (42, 1) e17 e9
  let e19 : LowMeanIntegerExpr := .div (2, 525) e15 e18
  let e20 : LowMeanIntegerExpr := .neg (-2, 525) e19
  let e21 : LowMeanIntegerExpr := .add (2251, 21000) e13 e20
  e21

def fiberBudgetExpr_iota_50_52_strictGap : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 1)
  let e1 : LowMeanIntegerExpr := .atom (3, 10)
  let e2 : LowMeanIntegerExpr := .add (13, 10) e0 e1
  let e3 : LowMeanIntegerExpr := .neg (-1, 1) e0
  let e4 : LowMeanIntegerExpr := .add (3, 10) e2 e3
  let e5 : LowMeanIntegerExpr := .atom (9, 1)
  let e6 : LowMeanIntegerExpr := .atom (21, 10)
  let e7 : LowMeanIntegerExpr := .mul (189, 10) e5 e6
  let e8 : LowMeanIntegerExpr := .atom (2, 1)
  let e9 : LowMeanIntegerExpr := .atom (50, 1)
  let e10 : LowMeanIntegerExpr := .mul (100, 1) e8 e9
  let e11 : LowMeanIntegerExpr := .div (189, 1000) e7 e10
  let e12 : LowMeanIntegerExpr := .neg (-189, 1000) e11
  let e13 : LowMeanIntegerExpr := .add (111, 1000) e4 e12
  let e14 : LowMeanIntegerExpr := .atom (2, 5)
  let e15 : LowMeanIntegerExpr := .pow (4, 25) e14 2
  let e16 : LowMeanIntegerExpr := .neg (-4, 25) e15
  let e17 : LowMeanIntegerExpr := .add (21, 25) e0 e16
  let e18 : LowMeanIntegerExpr := .mul (42, 1) e17 e9
  let e19 : LowMeanIntegerExpr := .div (2, 525) e15 e18
  let e20 : LowMeanIntegerExpr := .neg (-2, 525) e19
  let e21 : LowMeanIntegerExpr := .add (2251, 21000) e13 e20
  let e22 : LowMeanIntegerExpr := .atom (107, 1000)
  let e23 : LowMeanIntegerExpr := .neg (-107, 1000) e22
  let e24 : LowMeanIntegerExpr := .add (1, 5250) e21 e23
  e24

def fiberBudgetExpr_iota_50_52_margin : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (107, 1000)
  let e1 : LowMeanIntegerExpr := .atom (3, 50)
  let e2 : LowMeanIntegerExpr := .neg (-3, 50) e1
  let e3 : LowMeanIntegerExpr := .add (47, 1000) e0 e2
  e3

def fiberBudgetExpr_iota_53_54_budget : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 1)
  let e1 : LowMeanIntegerExpr := .atom (3, 10)
  let e2 : LowMeanIntegerExpr := .add (13, 10) e0 e1
  let e3 : LowMeanIntegerExpr := .neg (-1, 1) e0
  let e4 : LowMeanIntegerExpr := .add (3, 10) e2 e3
  let e5 : LowMeanIntegerExpr := .atom (9, 1)
  let e6 : LowMeanIntegerExpr := .atom (21, 10)
  let e7 : LowMeanIntegerExpr := .mul (189, 10) e5 e6
  let e8 : LowMeanIntegerExpr := .atom (2, 1)
  let e9 : LowMeanIntegerExpr := .atom (50, 1)
  let e10 : LowMeanIntegerExpr := .mul (100, 1) e8 e9
  let e11 : LowMeanIntegerExpr := .div (189, 1000) e7 e10
  let e12 : LowMeanIntegerExpr := .neg (-189, 1000) e11
  let e13 : LowMeanIntegerExpr := .add (111, 1000) e4 e12
  let e14 : LowMeanIntegerExpr := .atom (2, 5)
  let e15 : LowMeanIntegerExpr := .pow (4, 25) e14 2
  let e16 : LowMeanIntegerExpr := .neg (-4, 25) e15
  let e17 : LowMeanIntegerExpr := .add (21, 25) e0 e16
  let e18 : LowMeanIntegerExpr := .mul (42, 1) e17 e9
  let e19 : LowMeanIntegerExpr := .div (2, 525) e15 e18
  let e20 : LowMeanIntegerExpr := .neg (-2, 525) e19
  let e21 : LowMeanIntegerExpr := .add (2251, 21000) e13 e20
  e21

def fiberBudgetExpr_iota_53_54_strictGap : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 1)
  let e1 : LowMeanIntegerExpr := .atom (3, 10)
  let e2 : LowMeanIntegerExpr := .add (13, 10) e0 e1
  let e3 : LowMeanIntegerExpr := .neg (-1, 1) e0
  let e4 : LowMeanIntegerExpr := .add (3, 10) e2 e3
  let e5 : LowMeanIntegerExpr := .atom (9, 1)
  let e6 : LowMeanIntegerExpr := .atom (21, 10)
  let e7 : LowMeanIntegerExpr := .mul (189, 10) e5 e6
  let e8 : LowMeanIntegerExpr := .atom (2, 1)
  let e9 : LowMeanIntegerExpr := .atom (50, 1)
  let e10 : LowMeanIntegerExpr := .mul (100, 1) e8 e9
  let e11 : LowMeanIntegerExpr := .div (189, 1000) e7 e10
  let e12 : LowMeanIntegerExpr := .neg (-189, 1000) e11
  let e13 : LowMeanIntegerExpr := .add (111, 1000) e4 e12
  let e14 : LowMeanIntegerExpr := .atom (2, 5)
  let e15 : LowMeanIntegerExpr := .pow (4, 25) e14 2
  let e16 : LowMeanIntegerExpr := .neg (-4, 25) e15
  let e17 : LowMeanIntegerExpr := .add (21, 25) e0 e16
  let e18 : LowMeanIntegerExpr := .mul (42, 1) e17 e9
  let e19 : LowMeanIntegerExpr := .div (2, 525) e15 e18
  let e20 : LowMeanIntegerExpr := .neg (-2, 525) e19
  let e21 : LowMeanIntegerExpr := .add (2251, 21000) e13 e20
  let e22 : LowMeanIntegerExpr := .atom (107, 1000)
  let e23 : LowMeanIntegerExpr := .neg (-107, 1000) e22
  let e24 : LowMeanIntegerExpr := .add (1, 5250) e21 e23
  e24

def fiberBudgetExpr_iota_53_54_margin : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (107, 1000)
  let e1 : LowMeanIntegerExpr := .atom (1, 10)
  let e2 : LowMeanIntegerExpr := .neg (-1, 10) e1
  let e3 : LowMeanIntegerExpr := .add (7, 1000) e0 e2
  e3

def fiberBudgetExpr : FiberBudgetIdentity → FiberBudgetRole → LowMeanIntegerExpr
  | .iota_0_5, .budget => fiberBudgetExpr_iota_0_5_budget
  | .iota_0_5, .strictGap => fiberBudgetExpr_iota_0_5_strictGap
  | .iota_0_5, .margin => fiberBudgetExpr_iota_0_5_margin
  | .iota_6_9, .budget => fiberBudgetExpr_iota_6_9_budget
  | .iota_6_9, .strictGap => fiberBudgetExpr_iota_6_9_strictGap
  | .iota_6_9, .margin => fiberBudgetExpr_iota_6_9_margin
  | .iota_10_10, .budget => fiberBudgetExpr_iota_10_10_budget
  | .iota_10_10, .strictGap => fiberBudgetExpr_iota_10_10_strictGap
  | .iota_10_10, .margin => fiberBudgetExpr_iota_10_10_margin
  | .iota_11_29, .budget => fiberBudgetExpr_iota_11_29_budget
  | .iota_11_29, .strictGap => fiberBudgetExpr_iota_11_29_strictGap
  | .iota_11_29, .margin => fiberBudgetExpr_iota_11_29_margin
  | .iota_30_36, .budget => fiberBudgetExpr_iota_30_36_budget
  | .iota_30_36, .strictGap => fiberBudgetExpr_iota_30_36_strictGap
  | .iota_30_36, .margin => fiberBudgetExpr_iota_30_36_margin
  | .iota_37_37, .budget => fiberBudgetExpr_iota_37_37_budget
  | .iota_37_37, .strictGap => fiberBudgetExpr_iota_37_37_strictGap
  | .iota_37_37, .margin => fiberBudgetExpr_iota_37_37_margin
  | .iota_38_39, .budget => fiberBudgetExpr_iota_38_39_budget
  | .iota_38_39, .strictGap => fiberBudgetExpr_iota_38_39_strictGap
  | .iota_38_39, .margin => fiberBudgetExpr_iota_38_39_margin
  | .iota_40_43, .budget => fiberBudgetExpr_iota_40_43_budget
  | .iota_40_43, .strictGap => fiberBudgetExpr_iota_40_43_strictGap
  | .iota_40_43, .margin => fiberBudgetExpr_iota_40_43_margin
  | .iota_44_44, .budget => fiberBudgetExpr_iota_44_44_budget
  | .iota_44_44, .strictGap => fiberBudgetExpr_iota_44_44_strictGap
  | .iota_44_44, .margin => fiberBudgetExpr_iota_44_44_margin
  | .iota_45_46, .budget => fiberBudgetExpr_iota_45_46_budget
  | .iota_45_46, .strictGap => fiberBudgetExpr_iota_45_46_strictGap
  | .iota_45_46, .margin => fiberBudgetExpr_iota_45_46_margin
  | .iota_47_49, .budget => fiberBudgetExpr_iota_47_49_budget
  | .iota_47_49, .strictGap => fiberBudgetExpr_iota_47_49_strictGap
  | .iota_47_49, .margin => fiberBudgetExpr_iota_47_49_margin
  | .iota_50_52, .budget => fiberBudgetExpr_iota_50_52_budget
  | .iota_50_52, .strictGap => fiberBudgetExpr_iota_50_52_strictGap
  | .iota_50_52, .margin => fiberBudgetExpr_iota_50_52_margin
  | .iota_53_54, .budget => fiberBudgetExpr_iota_53_54_budget
  | .iota_53_54, .strictGap => fiberBudgetExpr_iota_53_54_strictGap
  | .iota_53_54, .margin => fiberBudgetExpr_iota_53_54_margin

end Erdos993Lean.Analytic.V213
