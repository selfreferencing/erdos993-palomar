module

public import Erdos993Lean.Analytic.V213.LowMeanIntegerShape

/-!
Accepted F08 Eq93 records, keyed by printed A/B/D/H. Full canonical
rho-minus/k-plus/E-plus and all four strict gaps plus root comparisons
retain every source leaf and the actual N_f=m_f+2 association.
These reduced Int/Nat trees are data only until kernel/shape checking.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

inductive FiberRayIdentity where
  | a | b | d | h

inductive FiberRayRole where
  | rho | kappa | error | rhoGap | kappaGap | betaGap | squareGap | sqrtS | sqrtV

structure FiberRayRow where
  printed : String
  R : lowMeanFraction
  m_f : lowMeanFraction
  N_f : lowMeanFraction
  rho_f : lowMeanFraction
  k_f : lowMeanFraction
  beta_f : lowMeanFraction
  d_f : lowMeanFraction
  s : lowMeanFraction
  v : lowMeanFraction
  minimum_gap : lowMeanFraction
  rho_minus : lowMeanFraction
  k_plus : lowMeanFraction
  E_plus : lowMeanFraction

def fiberRayPrinted : FiberRayIdentity → String
  | .a => "F08:A"
  | .b => "F08:B"
  | .d => "F08:D"
  | .h => "F08:H"

def fiberRayById : FiberRayIdentity → FiberRayRow
  | .a => ⟨"F08:A", (1, 4), (8, 1), (10, 1), (63, 100), (17, 6), (24, 5), (21, 10), (19, 6), (19, 18), (7, 10000), (22699, 35640), (5722, 2025), (5329, 4050)⟩
  | .b => ⟨"F08:B", (1, 8), (8, 1), (10, 1), (69, 100), (14, 5), (13, 2), (13, 10), (19, 6), (19, 18), (3, 1000), (417559, 598752), (23698, 8505), (61097, 71442)⟩
  | .d => ⟨"F08:D", (1, 6), (8, 1), (10, 1), (17, 25), (14, 5), (6, 1), (29, 20), (19, 6), (19, 18), (1, 1000), (7088, 10395), (1468, 525), (2431, 2450)⟩
  | .h => ⟨"F08:H", (7, 25), (14, 1), (16, 1), (143, 200), (14, 5), (10, 1), (4, 5), (4, 1), (31, 30), (1, 1000), (78931613, 110160000), (231763, 82944), (788009, 442368)⟩

def fiberRayExpr_a_rho : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 1)
  let e1 : LowMeanIntegerExpr := .atom (1, 4)
  let e2 : LowMeanIntegerExpr := .pow (1, 16) e1 2
  let e3 : LowMeanIntegerExpr := .neg (-1, 16) e2
  let e4 : LowMeanIntegerExpr := .add (15, 16) e0 e3
  let e5 : LowMeanIntegerExpr := .atom (8, 1)
  let e6 : LowMeanIntegerExpr := .atom (2, 1)
  let e7 : LowMeanIntegerExpr := .add (10, 1) e5 e6
  let e8 : LowMeanIntegerExpr := .mul (75, 8) e4 e7
  let e9 : LowMeanIntegerExpr := .add (11, 1) e7 e0
  let e10 : LowMeanIntegerExpr := .div (75, 88) e8 e9
  let e11 : LowMeanIntegerExpr := .div (2, 11) e6 e9
  let e12 : LowMeanIntegerExpr := .atom (3, 1)
  let e13 : LowMeanIntegerExpr := .mul (45, 16) e12 e4
  let e14 : LowMeanIntegerExpr := .div (1, 45) e2 e13
  let e15 : LowMeanIntegerExpr := .add (101, 495) e11 e14
  let e16 : LowMeanIntegerExpr := .atom (19, 18)
  let e17 : LowMeanIntegerExpr := .mul (1919, 8910) e15 e16
  let e18 : LowMeanIntegerExpr := .neg (-1919, 8910) e17
  let e19 : LowMeanIntegerExpr := .add (22699, 35640) e10 e18
  e19

def fiberRayExpr_a_kappa : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (2, 1)
  let e1 : LowMeanIntegerExpr := .atom (8, 1)
  let e2 : LowMeanIntegerExpr := .add (10, 1) e1 e0
  let e3 : LowMeanIntegerExpr := .atom (1, 1)
  let e4 : LowMeanIntegerExpr := .add (11, 1) e2 e3
  let e5 : LowMeanIntegerExpr := .mul (22, 1) e0 e4
  let e6 : LowMeanIntegerExpr := .atom (19, 18)
  let e7 : LowMeanIntegerExpr := .mul (209, 9) e5 e6
  let e8 : LowMeanIntegerExpr := .atom (3, 1)
  let e9 : LowMeanIntegerExpr := .mul (30, 1) e8 e2
  let e10 : LowMeanIntegerExpr := .atom (1, 4)
  let e11 : LowMeanIntegerExpr := .pow (1, 16) e10 2
  let e12 : LowMeanIntegerExpr := .neg (-1, 16) e11
  let e13 : LowMeanIntegerExpr := .add (15, 16) e3 e12
  let e14 : LowMeanIntegerExpr := .mul (225, 8) e9 e13
  let e15 : LowMeanIntegerExpr := .div (1672, 2025) e7 e14
  let e16 : LowMeanIntegerExpr := .add (5722, 2025) e0 e15
  e16

def fiberRayExpr_a_error : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 2)
  let e1 : LowMeanIntegerExpr := .atom (5, 1)
  let e2 : LowMeanIntegerExpr := .atom (1, 4)
  let e3 : LowMeanIntegerExpr := .mul (5, 4) e1 e2
  let e4 : LowMeanIntegerExpr := .atom (19, 6)
  let e5 : LowMeanIntegerExpr := .mul (95, 24) e3 e4
  let e6 : LowMeanIntegerExpr := .atom (6, 1)
  let e7 : LowMeanIntegerExpr := .atom (1, 1)
  let e8 : LowMeanIntegerExpr := .pow (1, 16) e2 2
  let e9 : LowMeanIntegerExpr := .neg (-1, 16) e8
  let e10 : LowMeanIntegerExpr := .add (15, 16) e7 e9
  let e11 : LowMeanIntegerExpr := .mul (45, 8) e6 e10
  let e12 : LowMeanIntegerExpr := .div (19, 27) e5 e11
  let e13 : LowMeanIntegerExpr := .add (65, 54) e0 e12
  let e14 : LowMeanIntegerExpr := .atom (8, 1)
  let e15 : LowMeanIntegerExpr := .atom (2, 1)
  let e16 : LowMeanIntegerExpr := .add (10, 1) e14 e15
  let e17 : LowMeanIntegerExpr := .add (11, 1) e16 e7
  let e18 : LowMeanIntegerExpr := .mul (11, 16) e17 e8
  let e19 : LowMeanIntegerExpr := .pow (1, 64) e2 3
  let e20 : LowMeanIntegerExpr := .mul (5, 32) e19 e16
  let e21 : LowMeanIntegerExpr := .mul (95, 192) e20 e4
  let e22 : LowMeanIntegerExpr := .add (227, 192) e18 e21
  let e23 : LowMeanIntegerExpr := .atom (12, 1)
  let e24 : LowMeanIntegerExpr := .pow (225, 256) e10 2
  let e25 : LowMeanIntegerExpr := .mul (675, 64) e23 e24
  let e26 : LowMeanIntegerExpr := .div (227, 2025) e22 e25
  let e27 : LowMeanIntegerExpr := .add (5329, 4050) e13 e26
  e27

def fiberRayExpr_a_rhoGap : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 1)
  let e1 : LowMeanIntegerExpr := .atom (1, 4)
  let e2 : LowMeanIntegerExpr := .pow (1, 16) e1 2
  let e3 : LowMeanIntegerExpr := .neg (-1, 16) e2
  let e4 : LowMeanIntegerExpr := .add (15, 16) e0 e3
  let e5 : LowMeanIntegerExpr := .atom (8, 1)
  let e6 : LowMeanIntegerExpr := .atom (2, 1)
  let e7 : LowMeanIntegerExpr := .add (10, 1) e5 e6
  let e8 : LowMeanIntegerExpr := .mul (75, 8) e4 e7
  let e9 : LowMeanIntegerExpr := .add (11, 1) e7 e0
  let e10 : LowMeanIntegerExpr := .div (75, 88) e8 e9
  let e11 : LowMeanIntegerExpr := .div (2, 11) e6 e9
  let e12 : LowMeanIntegerExpr := .atom (3, 1)
  let e13 : LowMeanIntegerExpr := .mul (45, 16) e12 e4
  let e14 : LowMeanIntegerExpr := .div (1, 45) e2 e13
  let e15 : LowMeanIntegerExpr := .add (101, 495) e11 e14
  let e16 : LowMeanIntegerExpr := .atom (19, 18)
  let e17 : LowMeanIntegerExpr := .mul (1919, 8910) e15 e16
  let e18 : LowMeanIntegerExpr := .neg (-1919, 8910) e17
  let e19 : LowMeanIntegerExpr := .add (22699, 35640) e10 e18
  let e20 : LowMeanIntegerExpr := .atom (63, 100)
  let e21 : LowMeanIntegerExpr := .neg (-63, 100) e20
  let e22 : LowMeanIntegerExpr := .add (1229, 178200) e19 e21
  e22

def fiberRayExpr_a_kappaGap : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (17, 6)
  let e1 : LowMeanIntegerExpr := .atom (2, 1)
  let e2 : LowMeanIntegerExpr := .atom (8, 1)
  let e3 : LowMeanIntegerExpr := .add (10, 1) e2 e1
  let e4 : LowMeanIntegerExpr := .atom (1, 1)
  let e5 : LowMeanIntegerExpr := .add (11, 1) e3 e4
  let e6 : LowMeanIntegerExpr := .mul (22, 1) e1 e5
  let e7 : LowMeanIntegerExpr := .atom (19, 18)
  let e8 : LowMeanIntegerExpr := .mul (209, 9) e6 e7
  let e9 : LowMeanIntegerExpr := .atom (3, 1)
  let e10 : LowMeanIntegerExpr := .mul (30, 1) e9 e3
  let e11 : LowMeanIntegerExpr := .atom (1, 4)
  let e12 : LowMeanIntegerExpr := .pow (1, 16) e11 2
  let e13 : LowMeanIntegerExpr := .neg (-1, 16) e12
  let e14 : LowMeanIntegerExpr := .add (15, 16) e4 e13
  let e15 : LowMeanIntegerExpr := .mul (225, 8) e10 e14
  let e16 : LowMeanIntegerExpr := .div (1672, 2025) e8 e15
  let e17 : LowMeanIntegerExpr := .add (5722, 2025) e1 e16
  let e18 : LowMeanIntegerExpr := .neg (-5722, 2025) e17
  let e19 : LowMeanIntegerExpr := .add (31, 4050) e0 e18
  e19

def fiberRayExpr_a_betaGap : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (63, 100)
  let e1 : LowMeanIntegerExpr := .atom (8, 1)
  let e2 : LowMeanIntegerExpr := .atom (2, 1)
  let e3 : LowMeanIntegerExpr := .add (10, 1) e1 e2
  let e4 : LowMeanIntegerExpr := .atom (1, 1)
  let e5 : LowMeanIntegerExpr := .neg (-1, 1) e4
  let e6 : LowMeanIntegerExpr := .add (9, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .atom (24, 5)
  let e8 : LowMeanIntegerExpr := .neg (-24, 5) e7
  let e9 : LowMeanIntegerExpr := .add (21, 5) e6 e8
  let e10 : LowMeanIntegerExpr := .mul (1323, 500) e0 e9
  let e11 : LowMeanIntegerExpr := .atom (1, 2)
  let e12 : LowMeanIntegerExpr := .atom (5, 1)
  let e13 : LowMeanIntegerExpr := .atom (1, 4)
  let e14 : LowMeanIntegerExpr := .mul (5, 4) e12 e13
  let e15 : LowMeanIntegerExpr := .atom (19, 6)
  let e16 : LowMeanIntegerExpr := .mul (95, 24) e14 e15
  let e17 : LowMeanIntegerExpr := .atom (6, 1)
  let e18 : LowMeanIntegerExpr := .pow (1, 16) e13 2
  let e19 : LowMeanIntegerExpr := .neg (-1, 16) e18
  let e20 : LowMeanIntegerExpr := .add (15, 16) e4 e19
  let e21 : LowMeanIntegerExpr := .mul (45, 8) e17 e20
  let e22 : LowMeanIntegerExpr := .div (19, 27) e16 e21
  let e23 : LowMeanIntegerExpr := .add (65, 54) e11 e22
  let e24 : LowMeanIntegerExpr := .add (11, 1) e3 e4
  let e25 : LowMeanIntegerExpr := .mul (11, 16) e24 e18
  let e26 : LowMeanIntegerExpr := .pow (1, 64) e13 3
  let e27 : LowMeanIntegerExpr := .mul (5, 32) e26 e3
  let e28 : LowMeanIntegerExpr := .mul (95, 192) e27 e15
  let e29 : LowMeanIntegerExpr := .add (227, 192) e25 e28
  let e30 : LowMeanIntegerExpr := .atom (12, 1)
  let e31 : LowMeanIntegerExpr := .pow (225, 256) e20 2
  let e32 : LowMeanIntegerExpr := .mul (675, 64) e30 e31
  let e33 : LowMeanIntegerExpr := .div (227, 2025) e29 e32
  let e34 : LowMeanIntegerExpr := .add (5329, 4050) e23 e33
  let e35 : LowMeanIntegerExpr := .mul (5329, 2025) e2 e34
  let e36 : LowMeanIntegerExpr := .neg (-5329, 2025) e35
  let e37 : LowMeanIntegerExpr := .add (583, 40500) e10 e36
  e37

def fiberRayExpr_a_squareGap : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (21, 10)
  let e1 : LowMeanIntegerExpr := .atom (63, 100)
  let e2 : LowMeanIntegerExpr := .pow (3969, 10000) e1 2
  let e3 : LowMeanIntegerExpr := .mul (83349, 100000) e0 e2
  let e4 : LowMeanIntegerExpr := .atom (24, 5)
  let e5 : LowMeanIntegerExpr := .mul (250047, 62500) e3 e4
  let e6 : LowMeanIntegerExpr := .atom (4, 1)
  let e7 : LowMeanIntegerExpr := .neg (-4, 1) e6
  let e8 : LowMeanIntegerExpr := .add (47, 62500) e5 e7
  e8

def fiberRayExpr_a_sqrtS : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (19, 6)
  let e1 : LowMeanIntegerExpr := .pow (361, 36) e0 2
  let e2 : LowMeanIntegerExpr := .atom (8, 1)
  let e3 : LowMeanIntegerExpr := .atom (2, 1)
  let e4 : LowMeanIntegerExpr := .add (10, 1) e2 e3
  let e5 : LowMeanIntegerExpr := .neg (-10, 1) e4
  let e6 : LowMeanIntegerExpr := .add (1, 36) e1 e5
  e6

def fiberRayExpr_a_sqrtV : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (19, 18)
  let e1 : LowMeanIntegerExpr := .pow (361, 324) e0 2
  let e2 : LowMeanIntegerExpr := .atom (1, 1)
  let e3 : LowMeanIntegerExpr := .atom (8, 1)
  let e4 : LowMeanIntegerExpr := .atom (2, 1)
  let e5 : LowMeanIntegerExpr := .add (10, 1) e3 e4
  let e6 : LowMeanIntegerExpr := .div (1, 10) e2 e5
  let e7 : LowMeanIntegerExpr := .neg (-1, 10) e6
  let e8 : LowMeanIntegerExpr := .add (9, 10) e2 e7
  let e9 : LowMeanIntegerExpr := .mul (361, 360) e1 e8
  let e10 : LowMeanIntegerExpr := .neg (-1, 1) e2
  let e11 : LowMeanIntegerExpr := .add (1, 360) e9 e10
  e11

def fiberRayExpr_b_rho : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 1)
  let e1 : LowMeanIntegerExpr := .atom (1, 8)
  let e2 : LowMeanIntegerExpr := .pow (1, 64) e1 2
  let e3 : LowMeanIntegerExpr := .neg (-1, 64) e2
  let e4 : LowMeanIntegerExpr := .add (63, 64) e0 e3
  let e5 : LowMeanIntegerExpr := .atom (8, 1)
  let e6 : LowMeanIntegerExpr := .atom (2, 1)
  let e7 : LowMeanIntegerExpr := .add (10, 1) e5 e6
  let e8 : LowMeanIntegerExpr := .mul (315, 32) e4 e7
  let e9 : LowMeanIntegerExpr := .add (11, 1) e7 e0
  let e10 : LowMeanIntegerExpr := .div (315, 352) e8 e9
  let e11 : LowMeanIntegerExpr := .div (2, 11) e6 e9
  let e12 : LowMeanIntegerExpr := .atom (3, 1)
  let e13 : LowMeanIntegerExpr := .mul (189, 64) e12 e4
  let e14 : LowMeanIntegerExpr := .div (1, 189) e2 e13
  let e15 : LowMeanIntegerExpr := .add (389, 2079) e11 e14
  let e16 : LowMeanIntegerExpr := .atom (19, 18)
  let e17 : LowMeanIntegerExpr := .mul (7391, 37422) e15 e16
  let e18 : LowMeanIntegerExpr := .neg (-7391, 37422) e17
  let e19 : LowMeanIntegerExpr := .add (417559, 598752) e10 e18
  e19

def fiberRayExpr_b_kappa : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (2, 1)
  let e1 : LowMeanIntegerExpr := .atom (8, 1)
  let e2 : LowMeanIntegerExpr := .add (10, 1) e1 e0
  let e3 : LowMeanIntegerExpr := .atom (1, 1)
  let e4 : LowMeanIntegerExpr := .add (11, 1) e2 e3
  let e5 : LowMeanIntegerExpr := .mul (22, 1) e0 e4
  let e6 : LowMeanIntegerExpr := .atom (19, 18)
  let e7 : LowMeanIntegerExpr := .mul (209, 9) e5 e6
  let e8 : LowMeanIntegerExpr := .atom (3, 1)
  let e9 : LowMeanIntegerExpr := .mul (30, 1) e8 e2
  let e10 : LowMeanIntegerExpr := .atom (1, 8)
  let e11 : LowMeanIntegerExpr := .pow (1, 64) e10 2
  let e12 : LowMeanIntegerExpr := .neg (-1, 64) e11
  let e13 : LowMeanIntegerExpr := .add (63, 64) e3 e12
  let e14 : LowMeanIntegerExpr := .mul (945, 32) e9 e13
  let e15 : LowMeanIntegerExpr := .div (6688, 8505) e7 e14
  let e16 : LowMeanIntegerExpr := .add (23698, 8505) e0 e15
  e16

def fiberRayExpr_b_error : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 2)
  let e1 : LowMeanIntegerExpr := .atom (5, 1)
  let e2 : LowMeanIntegerExpr := .atom (1, 8)
  let e3 : LowMeanIntegerExpr := .mul (5, 8) e1 e2
  let e4 : LowMeanIntegerExpr := .atom (19, 6)
  let e5 : LowMeanIntegerExpr := .mul (95, 48) e3 e4
  let e6 : LowMeanIntegerExpr := .atom (6, 1)
  let e7 : LowMeanIntegerExpr := .atom (1, 1)
  let e8 : LowMeanIntegerExpr := .pow (1, 64) e2 2
  let e9 : LowMeanIntegerExpr := .neg (-1, 64) e8
  let e10 : LowMeanIntegerExpr := .add (63, 64) e7 e9
  let e11 : LowMeanIntegerExpr := .mul (189, 32) e6 e10
  let e12 : LowMeanIntegerExpr := .div (190, 567) e5 e11
  let e13 : LowMeanIntegerExpr := .add (947, 1134) e0 e12
  let e14 : LowMeanIntegerExpr := .atom (8, 1)
  let e15 : LowMeanIntegerExpr := .atom (2, 1)
  let e16 : LowMeanIntegerExpr := .add (10, 1) e14 e15
  let e17 : LowMeanIntegerExpr := .add (11, 1) e16 e7
  let e18 : LowMeanIntegerExpr := .mul (11, 64) e17 e8
  let e19 : LowMeanIntegerExpr := .pow (1, 512) e2 3
  let e20 : LowMeanIntegerExpr := .mul (5, 256) e19 e16
  let e21 : LowMeanIntegerExpr := .mul (95, 1536) e20 e4
  let e22 : LowMeanIntegerExpr := .add (359, 1536) e18 e21
  let e23 : LowMeanIntegerExpr := .atom (12, 1)
  let e24 : LowMeanIntegerExpr := .pow (3969, 4096) e10 2
  let e25 : LowMeanIntegerExpr := .mul (11907, 1024) e23 e24
  let e26 : LowMeanIntegerExpr := .div (718, 35721) e22 e25
  let e27 : LowMeanIntegerExpr := .add (61097, 71442) e13 e26
  e27

def fiberRayExpr_b_rhoGap : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 1)
  let e1 : LowMeanIntegerExpr := .atom (1, 8)
  let e2 : LowMeanIntegerExpr := .pow (1, 64) e1 2
  let e3 : LowMeanIntegerExpr := .neg (-1, 64) e2
  let e4 : LowMeanIntegerExpr := .add (63, 64) e0 e3
  let e5 : LowMeanIntegerExpr := .atom (8, 1)
  let e6 : LowMeanIntegerExpr := .atom (2, 1)
  let e7 : LowMeanIntegerExpr := .add (10, 1) e5 e6
  let e8 : LowMeanIntegerExpr := .mul (315, 32) e4 e7
  let e9 : LowMeanIntegerExpr := .add (11, 1) e7 e0
  let e10 : LowMeanIntegerExpr := .div (315, 352) e8 e9
  let e11 : LowMeanIntegerExpr := .div (2, 11) e6 e9
  let e12 : LowMeanIntegerExpr := .atom (3, 1)
  let e13 : LowMeanIntegerExpr := .mul (189, 64) e12 e4
  let e14 : LowMeanIntegerExpr := .div (1, 189) e2 e13
  let e15 : LowMeanIntegerExpr := .add (389, 2079) e11 e14
  let e16 : LowMeanIntegerExpr := .atom (19, 18)
  let e17 : LowMeanIntegerExpr := .mul (7391, 37422) e15 e16
  let e18 : LowMeanIntegerExpr := .neg (-7391, 37422) e17
  let e19 : LowMeanIntegerExpr := .add (417559, 598752) e10 e18
  let e20 : LowMeanIntegerExpr := .atom (69, 100)
  let e21 : LowMeanIntegerExpr := .neg (-69, 100) e20
  let e22 : LowMeanIntegerExpr := .add (110503, 14968800) e19 e21
  e22

def fiberRayExpr_b_kappaGap : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (14, 5)
  let e1 : LowMeanIntegerExpr := .atom (2, 1)
  let e2 : LowMeanIntegerExpr := .atom (8, 1)
  let e3 : LowMeanIntegerExpr := .add (10, 1) e2 e1
  let e4 : LowMeanIntegerExpr := .atom (1, 1)
  let e5 : LowMeanIntegerExpr := .add (11, 1) e3 e4
  let e6 : LowMeanIntegerExpr := .mul (22, 1) e1 e5
  let e7 : LowMeanIntegerExpr := .atom (19, 18)
  let e8 : LowMeanIntegerExpr := .mul (209, 9) e6 e7
  let e9 : LowMeanIntegerExpr := .atom (3, 1)
  let e10 : LowMeanIntegerExpr := .mul (30, 1) e9 e3
  let e11 : LowMeanIntegerExpr := .atom (1, 8)
  let e12 : LowMeanIntegerExpr := .pow (1, 64) e11 2
  let e13 : LowMeanIntegerExpr := .neg (-1, 64) e12
  let e14 : LowMeanIntegerExpr := .add (63, 64) e4 e13
  let e15 : LowMeanIntegerExpr := .mul (945, 32) e10 e14
  let e16 : LowMeanIntegerExpr := .div (6688, 8505) e8 e15
  let e17 : LowMeanIntegerExpr := .add (23698, 8505) e1 e16
  let e18 : LowMeanIntegerExpr := .neg (-23698, 8505) e17
  let e19 : LowMeanIntegerExpr := .add (116, 8505) e0 e18
  e19

def fiberRayExpr_b_betaGap : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (69, 100)
  let e1 : LowMeanIntegerExpr := .atom (8, 1)
  let e2 : LowMeanIntegerExpr := .atom (2, 1)
  let e3 : LowMeanIntegerExpr := .add (10, 1) e1 e2
  let e4 : LowMeanIntegerExpr := .atom (1, 1)
  let e5 : LowMeanIntegerExpr := .neg (-1, 1) e4
  let e6 : LowMeanIntegerExpr := .add (9, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .atom (13, 2)
  let e8 : LowMeanIntegerExpr := .neg (-13, 2) e7
  let e9 : LowMeanIntegerExpr := .add (5, 2) e6 e8
  let e10 : LowMeanIntegerExpr := .mul (69, 40) e0 e9
  let e11 : LowMeanIntegerExpr := .atom (1, 2)
  let e12 : LowMeanIntegerExpr := .atom (5, 1)
  let e13 : LowMeanIntegerExpr := .atom (1, 8)
  let e14 : LowMeanIntegerExpr := .mul (5, 8) e12 e13
  let e15 : LowMeanIntegerExpr := .atom (19, 6)
  let e16 : LowMeanIntegerExpr := .mul (95, 48) e14 e15
  let e17 : LowMeanIntegerExpr := .atom (6, 1)
  let e18 : LowMeanIntegerExpr := .pow (1, 64) e13 2
  let e19 : LowMeanIntegerExpr := .neg (-1, 64) e18
  let e20 : LowMeanIntegerExpr := .add (63, 64) e4 e19
  let e21 : LowMeanIntegerExpr := .mul (189, 32) e17 e20
  let e22 : LowMeanIntegerExpr := .div (190, 567) e16 e21
  let e23 : LowMeanIntegerExpr := .add (947, 1134) e11 e22
  let e24 : LowMeanIntegerExpr := .add (11, 1) e3 e4
  let e25 : LowMeanIntegerExpr := .mul (11, 64) e24 e18
  let e26 : LowMeanIntegerExpr := .pow (1, 512) e13 3
  let e27 : LowMeanIntegerExpr := .mul (5, 256) e26 e3
  let e28 : LowMeanIntegerExpr := .mul (95, 1536) e27 e15
  let e29 : LowMeanIntegerExpr := .add (359, 1536) e25 e28
  let e30 : LowMeanIntegerExpr := .atom (12, 1)
  let e31 : LowMeanIntegerExpr := .pow (3969, 4096) e20 2
  let e32 : LowMeanIntegerExpr := .mul (11907, 1024) e30 e31
  let e33 : LowMeanIntegerExpr := .div (718, 35721) e29 e32
  let e34 : LowMeanIntegerExpr := .add (61097, 71442) e23 e33
  let e35 : LowMeanIntegerExpr := .mul (61097, 35721) e2 e34
  let e36 : LowMeanIntegerExpr := .neg (-61097, 35721) e35
  let e37 : LowMeanIntegerExpr := .add (20869, 1428840) e10 e36
  e37

def fiberRayExpr_b_squareGap : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (13, 10)
  let e1 : LowMeanIntegerExpr := .atom (69, 100)
  let e2 : LowMeanIntegerExpr := .pow (4761, 10000) e1 2
  let e3 : LowMeanIntegerExpr := .mul (61893, 100000) e0 e2
  let e4 : LowMeanIntegerExpr := .atom (13, 2)
  let e5 : LowMeanIntegerExpr := .mul (804609, 200000) e3 e4
  let e6 : LowMeanIntegerExpr := .atom (4, 1)
  let e7 : LowMeanIntegerExpr := .neg (-4, 1) e6
  let e8 : LowMeanIntegerExpr := .add (4609, 200000) e5 e7
  e8

def fiberRayExpr_b_sqrtS : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (19, 6)
  let e1 : LowMeanIntegerExpr := .pow (361, 36) e0 2
  let e2 : LowMeanIntegerExpr := .atom (8, 1)
  let e3 : LowMeanIntegerExpr := .atom (2, 1)
  let e4 : LowMeanIntegerExpr := .add (10, 1) e2 e3
  let e5 : LowMeanIntegerExpr := .neg (-10, 1) e4
  let e6 : LowMeanIntegerExpr := .add (1, 36) e1 e5
  e6

def fiberRayExpr_b_sqrtV : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (19, 18)
  let e1 : LowMeanIntegerExpr := .pow (361, 324) e0 2
  let e2 : LowMeanIntegerExpr := .atom (1, 1)
  let e3 : LowMeanIntegerExpr := .atom (8, 1)
  let e4 : LowMeanIntegerExpr := .atom (2, 1)
  let e5 : LowMeanIntegerExpr := .add (10, 1) e3 e4
  let e6 : LowMeanIntegerExpr := .div (1, 10) e2 e5
  let e7 : LowMeanIntegerExpr := .neg (-1, 10) e6
  let e8 : LowMeanIntegerExpr := .add (9, 10) e2 e7
  let e9 : LowMeanIntegerExpr := .mul (361, 360) e1 e8
  let e10 : LowMeanIntegerExpr := .neg (-1, 1) e2
  let e11 : LowMeanIntegerExpr := .add (1, 360) e9 e10
  e11

def fiberRayExpr_d_rho : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 1)
  let e1 : LowMeanIntegerExpr := .atom (1, 6)
  let e2 : LowMeanIntegerExpr := .pow (1, 36) e1 2
  let e3 : LowMeanIntegerExpr := .neg (-1, 36) e2
  let e4 : LowMeanIntegerExpr := .add (35, 36) e0 e3
  let e5 : LowMeanIntegerExpr := .atom (8, 1)
  let e6 : LowMeanIntegerExpr := .atom (2, 1)
  let e7 : LowMeanIntegerExpr := .add (10, 1) e5 e6
  let e8 : LowMeanIntegerExpr := .mul (175, 18) e4 e7
  let e9 : LowMeanIntegerExpr := .add (11, 1) e7 e0
  let e10 : LowMeanIntegerExpr := .div (175, 198) e8 e9
  let e11 : LowMeanIntegerExpr := .div (2, 11) e6 e9
  let e12 : LowMeanIntegerExpr := .atom (3, 1)
  let e13 : LowMeanIntegerExpr := .mul (35, 12) e12 e4
  let e14 : LowMeanIntegerExpr := .div (1, 105) e2 e13
  let e15 : LowMeanIntegerExpr := .add (221, 1155) e11 e14
  let e16 : LowMeanIntegerExpr := .atom (19, 18)
  let e17 : LowMeanIntegerExpr := .mul (4199, 20790) e15 e16
  let e18 : LowMeanIntegerExpr := .neg (-4199, 20790) e17
  let e19 : LowMeanIntegerExpr := .add (7088, 10395) e10 e18
  e19

def fiberRayExpr_d_kappa : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (2, 1)
  let e1 : LowMeanIntegerExpr := .atom (8, 1)
  let e2 : LowMeanIntegerExpr := .add (10, 1) e1 e0
  let e3 : LowMeanIntegerExpr := .atom (1, 1)
  let e4 : LowMeanIntegerExpr := .add (11, 1) e2 e3
  let e5 : LowMeanIntegerExpr := .mul (22, 1) e0 e4
  let e6 : LowMeanIntegerExpr := .atom (19, 18)
  let e7 : LowMeanIntegerExpr := .mul (209, 9) e5 e6
  let e8 : LowMeanIntegerExpr := .atom (3, 1)
  let e9 : LowMeanIntegerExpr := .mul (30, 1) e8 e2
  let e10 : LowMeanIntegerExpr := .atom (1, 6)
  let e11 : LowMeanIntegerExpr := .pow (1, 36) e10 2
  let e12 : LowMeanIntegerExpr := .neg (-1, 36) e11
  let e13 : LowMeanIntegerExpr := .add (35, 36) e3 e12
  let e14 : LowMeanIntegerExpr := .mul (175, 6) e9 e13
  let e15 : LowMeanIntegerExpr := .div (418, 525) e7 e14
  let e16 : LowMeanIntegerExpr := .add (1468, 525) e0 e15
  e16

def fiberRayExpr_d_error : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 2)
  let e1 : LowMeanIntegerExpr := .atom (5, 1)
  let e2 : LowMeanIntegerExpr := .atom (1, 6)
  let e3 : LowMeanIntegerExpr := .mul (5, 6) e1 e2
  let e4 : LowMeanIntegerExpr := .atom (19, 6)
  let e5 : LowMeanIntegerExpr := .mul (95, 36) e3 e4
  let e6 : LowMeanIntegerExpr := .atom (6, 1)
  let e7 : LowMeanIntegerExpr := .atom (1, 1)
  let e8 : LowMeanIntegerExpr := .pow (1, 36) e2 2
  let e9 : LowMeanIntegerExpr := .neg (-1, 36) e8
  let e10 : LowMeanIntegerExpr := .add (35, 36) e7 e9
  let e11 : LowMeanIntegerExpr := .mul (35, 6) e6 e10
  let e12 : LowMeanIntegerExpr := .div (19, 42) e5 e11
  let e13 : LowMeanIntegerExpr := .add (20, 21) e0 e12
  let e14 : LowMeanIntegerExpr := .atom (8, 1)
  let e15 : LowMeanIntegerExpr := .atom (2, 1)
  let e16 : LowMeanIntegerExpr := .add (10, 1) e14 e15
  let e17 : LowMeanIntegerExpr := .add (11, 1) e16 e7
  let e18 : LowMeanIntegerExpr := .mul (11, 36) e17 e8
  let e19 : LowMeanIntegerExpr := .pow (1, 216) e2 3
  let e20 : LowMeanIntegerExpr := .mul (5, 108) e19 e16
  let e21 : LowMeanIntegerExpr := .mul (95, 648) e20 e4
  let e22 : LowMeanIntegerExpr := .add (293, 648) e18 e21
  let e23 : LowMeanIntegerExpr := .atom (12, 1)
  let e24 : LowMeanIntegerExpr := .pow (1225, 1296) e10 2
  let e25 : LowMeanIntegerExpr := .mul (1225, 108) e23 e24
  let e26 : LowMeanIntegerExpr := .div (293, 7350) e22 e25
  let e27 : LowMeanIntegerExpr := .add (2431, 2450) e13 e26
  e27

def fiberRayExpr_d_rhoGap : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 1)
  let e1 : LowMeanIntegerExpr := .atom (1, 6)
  let e2 : LowMeanIntegerExpr := .pow (1, 36) e1 2
  let e3 : LowMeanIntegerExpr := .neg (-1, 36) e2
  let e4 : LowMeanIntegerExpr := .add (35, 36) e0 e3
  let e5 : LowMeanIntegerExpr := .atom (8, 1)
  let e6 : LowMeanIntegerExpr := .atom (2, 1)
  let e7 : LowMeanIntegerExpr := .add (10, 1) e5 e6
  let e8 : LowMeanIntegerExpr := .mul (175, 18) e4 e7
  let e9 : LowMeanIntegerExpr := .add (11, 1) e7 e0
  let e10 : LowMeanIntegerExpr := .div (175, 198) e8 e9
  let e11 : LowMeanIntegerExpr := .div (2, 11) e6 e9
  let e12 : LowMeanIntegerExpr := .atom (3, 1)
  let e13 : LowMeanIntegerExpr := .mul (35, 12) e12 e4
  let e14 : LowMeanIntegerExpr := .div (1, 105) e2 e13
  let e15 : LowMeanIntegerExpr := .add (221, 1155) e11 e14
  let e16 : LowMeanIntegerExpr := .atom (19, 18)
  let e17 : LowMeanIntegerExpr := .mul (4199, 20790) e15 e16
  let e18 : LowMeanIntegerExpr := .neg (-4199, 20790) e17
  let e19 : LowMeanIntegerExpr := .add (7088, 10395) e10 e18
  let e20 : LowMeanIntegerExpr := .atom (17, 25)
  let e21 : LowMeanIntegerExpr := .neg (-17, 25) e20
  let e22 : LowMeanIntegerExpr := .add (97, 51975) e19 e21
  e22

def fiberRayExpr_d_kappaGap : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (14, 5)
  let e1 : LowMeanIntegerExpr := .atom (2, 1)
  let e2 : LowMeanIntegerExpr := .atom (8, 1)
  let e3 : LowMeanIntegerExpr := .add (10, 1) e2 e1
  let e4 : LowMeanIntegerExpr := .atom (1, 1)
  let e5 : LowMeanIntegerExpr := .add (11, 1) e3 e4
  let e6 : LowMeanIntegerExpr := .mul (22, 1) e1 e5
  let e7 : LowMeanIntegerExpr := .atom (19, 18)
  let e8 : LowMeanIntegerExpr := .mul (209, 9) e6 e7
  let e9 : LowMeanIntegerExpr := .atom (3, 1)
  let e10 : LowMeanIntegerExpr := .mul (30, 1) e9 e3
  let e11 : LowMeanIntegerExpr := .atom (1, 6)
  let e12 : LowMeanIntegerExpr := .pow (1, 36) e11 2
  let e13 : LowMeanIntegerExpr := .neg (-1, 36) e12
  let e14 : LowMeanIntegerExpr := .add (35, 36) e4 e13
  let e15 : LowMeanIntegerExpr := .mul (175, 6) e10 e14
  let e16 : LowMeanIntegerExpr := .div (418, 525) e8 e15
  let e17 : LowMeanIntegerExpr := .add (1468, 525) e1 e16
  let e18 : LowMeanIntegerExpr := .neg (-1468, 525) e17
  let e19 : LowMeanIntegerExpr := .add (2, 525) e0 e18
  e19

def fiberRayExpr_d_betaGap : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (17, 25)
  let e1 : LowMeanIntegerExpr := .atom (8, 1)
  let e2 : LowMeanIntegerExpr := .atom (2, 1)
  let e3 : LowMeanIntegerExpr := .add (10, 1) e1 e2
  let e4 : LowMeanIntegerExpr := .atom (1, 1)
  let e5 : LowMeanIntegerExpr := .neg (-1, 1) e4
  let e6 : LowMeanIntegerExpr := .add (9, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .atom (6, 1)
  let e8 : LowMeanIntegerExpr := .neg (-6, 1) e7
  let e9 : LowMeanIntegerExpr := .add (3, 1) e6 e8
  let e10 : LowMeanIntegerExpr := .mul (51, 25) e0 e9
  let e11 : LowMeanIntegerExpr := .atom (1, 2)
  let e12 : LowMeanIntegerExpr := .atom (5, 1)
  let e13 : LowMeanIntegerExpr := .atom (1, 6)
  let e14 : LowMeanIntegerExpr := .mul (5, 6) e12 e13
  let e15 : LowMeanIntegerExpr := .atom (19, 6)
  let e16 : LowMeanIntegerExpr := .mul (95, 36) e14 e15
  let e17 : LowMeanIntegerExpr := .pow (1, 36) e13 2
  let e18 : LowMeanIntegerExpr := .neg (-1, 36) e17
  let e19 : LowMeanIntegerExpr := .add (35, 36) e4 e18
  let e20 : LowMeanIntegerExpr := .mul (35, 6) e7 e19
  let e21 : LowMeanIntegerExpr := .div (19, 42) e16 e20
  let e22 : LowMeanIntegerExpr := .add (20, 21) e11 e21
  let e23 : LowMeanIntegerExpr := .add (11, 1) e3 e4
  let e24 : LowMeanIntegerExpr := .mul (11, 36) e23 e17
  let e25 : LowMeanIntegerExpr := .pow (1, 216) e13 3
  let e26 : LowMeanIntegerExpr := .mul (5, 108) e25 e3
  let e27 : LowMeanIntegerExpr := .mul (95, 648) e26 e15
  let e28 : LowMeanIntegerExpr := .add (293, 648) e24 e27
  let e29 : LowMeanIntegerExpr := .atom (12, 1)
  let e30 : LowMeanIntegerExpr := .pow (1225, 1296) e19 2
  let e31 : LowMeanIntegerExpr := .mul (1225, 108) e29 e30
  let e32 : LowMeanIntegerExpr := .div (293, 7350) e28 e31
  let e33 : LowMeanIntegerExpr := .add (2431, 2450) e22 e32
  let e34 : LowMeanIntegerExpr := .mul (2431, 1225) e2 e33
  let e35 : LowMeanIntegerExpr := .neg (-2431, 1225) e34
  let e36 : LowMeanIntegerExpr := .add (68, 1225) e10 e35
  e36

def fiberRayExpr_d_squareGap : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (29, 20)
  let e1 : LowMeanIntegerExpr := .atom (17, 25)
  let e2 : LowMeanIntegerExpr := .pow (289, 625) e1 2
  let e3 : LowMeanIntegerExpr := .mul (8381, 12500) e0 e2
  let e4 : LowMeanIntegerExpr := .atom (6, 1)
  let e5 : LowMeanIntegerExpr := .mul (25143, 6250) e3 e4
  let e6 : LowMeanIntegerExpr := .atom (4, 1)
  let e7 : LowMeanIntegerExpr := .neg (-4, 1) e6
  let e8 : LowMeanIntegerExpr := .add (143, 6250) e5 e7
  e8

def fiberRayExpr_d_sqrtS : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (19, 6)
  let e1 : LowMeanIntegerExpr := .pow (361, 36) e0 2
  let e2 : LowMeanIntegerExpr := .atom (8, 1)
  let e3 : LowMeanIntegerExpr := .atom (2, 1)
  let e4 : LowMeanIntegerExpr := .add (10, 1) e2 e3
  let e5 : LowMeanIntegerExpr := .neg (-10, 1) e4
  let e6 : LowMeanIntegerExpr := .add (1, 36) e1 e5
  e6

def fiberRayExpr_d_sqrtV : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (19, 18)
  let e1 : LowMeanIntegerExpr := .pow (361, 324) e0 2
  let e2 : LowMeanIntegerExpr := .atom (1, 1)
  let e3 : LowMeanIntegerExpr := .atom (8, 1)
  let e4 : LowMeanIntegerExpr := .atom (2, 1)
  let e5 : LowMeanIntegerExpr := .add (10, 1) e3 e4
  let e6 : LowMeanIntegerExpr := .div (1, 10) e2 e5
  let e7 : LowMeanIntegerExpr := .neg (-1, 10) e6
  let e8 : LowMeanIntegerExpr := .add (9, 10) e2 e7
  let e9 : LowMeanIntegerExpr := .mul (361, 360) e1 e8
  let e10 : LowMeanIntegerExpr := .neg (-1, 1) e2
  let e11 : LowMeanIntegerExpr := .add (1, 360) e9 e10
  e11

def fiberRayExpr_h_rho : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 1)
  let e1 : LowMeanIntegerExpr := .atom (7, 25)
  let e2 : LowMeanIntegerExpr := .pow (49, 625) e1 2
  let e3 : LowMeanIntegerExpr := .neg (-49, 625) e2
  let e4 : LowMeanIntegerExpr := .add (576, 625) e0 e3
  let e5 : LowMeanIntegerExpr := .atom (14, 1)
  let e6 : LowMeanIntegerExpr := .atom (2, 1)
  let e7 : LowMeanIntegerExpr := .add (16, 1) e5 e6
  let e8 : LowMeanIntegerExpr := .mul (9216, 625) e4 e7
  let e9 : LowMeanIntegerExpr := .add (17, 1) e7 e0
  let e10 : LowMeanIntegerExpr := .div (9216, 10625) e8 e9
  let e11 : LowMeanIntegerExpr := .div (2, 17) e6 e9
  let e12 : LowMeanIntegerExpr := .atom (3, 1)
  let e13 : LowMeanIntegerExpr := .mul (1728, 625) e12 e4
  let e14 : LowMeanIntegerExpr := .div (49, 1728) e2 e13
  let e15 : LowMeanIntegerExpr := .add (4289, 29376) e11 e14
  let e16 : LowMeanIntegerExpr := .atom (31, 30)
  let e17 : LowMeanIntegerExpr := .mul (132959, 881280) e15 e16
  let e18 : LowMeanIntegerExpr := .neg (-132959, 881280) e17
  let e19 : LowMeanIntegerExpr := .add (78931613, 110160000) e10 e18
  e19

def fiberRayExpr_h_kappa : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (2, 1)
  let e1 : LowMeanIntegerExpr := .atom (14, 1)
  let e2 : LowMeanIntegerExpr := .add (16, 1) e1 e0
  let e3 : LowMeanIntegerExpr := .atom (1, 1)
  let e4 : LowMeanIntegerExpr := .add (17, 1) e2 e3
  let e5 : LowMeanIntegerExpr := .mul (34, 1) e0 e4
  let e6 : LowMeanIntegerExpr := .atom (31, 30)
  let e7 : LowMeanIntegerExpr := .mul (527, 15) e5 e6
  let e8 : LowMeanIntegerExpr := .atom (3, 1)
  let e9 : LowMeanIntegerExpr := .mul (48, 1) e8 e2
  let e10 : LowMeanIntegerExpr := .atom (7, 25)
  let e11 : LowMeanIntegerExpr := .pow (49, 625) e10 2
  let e12 : LowMeanIntegerExpr := .neg (-49, 625) e11
  let e13 : LowMeanIntegerExpr := .add (576, 625) e3 e12
  let e14 : LowMeanIntegerExpr := .mul (27648, 625) e9 e13
  let e15 : LowMeanIntegerExpr := .div (65875, 82944) e7 e14
  let e16 : LowMeanIntegerExpr := .add (231763, 82944) e0 e15
  e16

def fiberRayExpr_h_error : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 2)
  let e1 : LowMeanIntegerExpr := .atom (5, 1)
  let e2 : LowMeanIntegerExpr := .atom (7, 25)
  let e3 : LowMeanIntegerExpr := .mul (7, 5) e1 e2
  let e4 : LowMeanIntegerExpr := .atom (4, 1)
  let e5 : LowMeanIntegerExpr := .mul (28, 5) e3 e4
  let e6 : LowMeanIntegerExpr := .atom (6, 1)
  let e7 : LowMeanIntegerExpr := .atom (1, 1)
  let e8 : LowMeanIntegerExpr := .pow (49, 625) e2 2
  let e9 : LowMeanIntegerExpr := .neg (-49, 625) e8
  let e10 : LowMeanIntegerExpr := .add (576, 625) e7 e9
  let e11 : LowMeanIntegerExpr := .mul (3456, 625) e6 e10
  let e12 : LowMeanIntegerExpr := .div (875, 864) e5 e11
  let e13 : LowMeanIntegerExpr := .add (1307, 864) e0 e12
  let e14 : LowMeanIntegerExpr := .atom (14, 1)
  let e15 : LowMeanIntegerExpr := .atom (2, 1)
  let e16 : LowMeanIntegerExpr := .add (16, 1) e14 e15
  let e17 : LowMeanIntegerExpr := .add (17, 1) e16 e7
  let e18 : LowMeanIntegerExpr := .mul (833, 625) e17 e8
  let e19 : LowMeanIntegerExpr := .pow (343, 15625) e2 3
  let e20 : LowMeanIntegerExpr := .mul (5488, 15625) e19 e16
  let e21 : LowMeanIntegerExpr := .mul (21952, 15625) e20 e4
  let e22 : LowMeanIntegerExpr := .add (42777, 15625) e18 e21
  let e23 : LowMeanIntegerExpr := .atom (12, 1)
  let e24 : LowMeanIntegerExpr := .pow (331776, 390625) e10 2
  let e25 : LowMeanIntegerExpr := .mul (3981312, 390625) e23 e24
  let e26 : LowMeanIntegerExpr := .div (118825, 442368) e22 e25
  let e27 : LowMeanIntegerExpr := .add (788009, 442368) e13 e26
  e27

def fiberRayExpr_h_rhoGap : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 1)
  let e1 : LowMeanIntegerExpr := .atom (7, 25)
  let e2 : LowMeanIntegerExpr := .pow (49, 625) e1 2
  let e3 : LowMeanIntegerExpr := .neg (-49, 625) e2
  let e4 : LowMeanIntegerExpr := .add (576, 625) e0 e3
  let e5 : LowMeanIntegerExpr := .atom (14, 1)
  let e6 : LowMeanIntegerExpr := .atom (2, 1)
  let e7 : LowMeanIntegerExpr := .add (16, 1) e5 e6
  let e8 : LowMeanIntegerExpr := .mul (9216, 625) e4 e7
  let e9 : LowMeanIntegerExpr := .add (17, 1) e7 e0
  let e10 : LowMeanIntegerExpr := .div (9216, 10625) e8 e9
  let e11 : LowMeanIntegerExpr := .div (2, 17) e6 e9
  let e12 : LowMeanIntegerExpr := .atom (3, 1)
  let e13 : LowMeanIntegerExpr := .mul (1728, 625) e12 e4
  let e14 : LowMeanIntegerExpr := .div (49, 1728) e2 e13
  let e15 : LowMeanIntegerExpr := .add (4289, 29376) e11 e14
  let e16 : LowMeanIntegerExpr := .atom (31, 30)
  let e17 : LowMeanIntegerExpr := .mul (132959, 881280) e15 e16
  let e18 : LowMeanIntegerExpr := .neg (-132959, 881280) e17
  let e19 : LowMeanIntegerExpr := .add (78931613, 110160000) e10 e18
  let e20 : LowMeanIntegerExpr := .atom (143, 200)
  let e21 : LowMeanIntegerExpr := .neg (-143, 200) e20
  let e22 : LowMeanIntegerExpr := .add (167213, 110160000) e19 e21
  e22

def fiberRayExpr_h_kappaGap : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (14, 5)
  let e1 : LowMeanIntegerExpr := .atom (2, 1)
  let e2 : LowMeanIntegerExpr := .atom (14, 1)
  let e3 : LowMeanIntegerExpr := .add (16, 1) e2 e1
  let e4 : LowMeanIntegerExpr := .atom (1, 1)
  let e5 : LowMeanIntegerExpr := .add (17, 1) e3 e4
  let e6 : LowMeanIntegerExpr := .mul (34, 1) e1 e5
  let e7 : LowMeanIntegerExpr := .atom (31, 30)
  let e8 : LowMeanIntegerExpr := .mul (527, 15) e6 e7
  let e9 : LowMeanIntegerExpr := .atom (3, 1)
  let e10 : LowMeanIntegerExpr := .mul (48, 1) e9 e3
  let e11 : LowMeanIntegerExpr := .atom (7, 25)
  let e12 : LowMeanIntegerExpr := .pow (49, 625) e11 2
  let e13 : LowMeanIntegerExpr := .neg (-49, 625) e12
  let e14 : LowMeanIntegerExpr := .add (576, 625) e4 e13
  let e15 : LowMeanIntegerExpr := .mul (27648, 625) e10 e14
  let e16 : LowMeanIntegerExpr := .div (65875, 82944) e8 e15
  let e17 : LowMeanIntegerExpr := .add (231763, 82944) e1 e16
  let e18 : LowMeanIntegerExpr := .neg (-231763, 82944) e17
  let e19 : LowMeanIntegerExpr := .add (2401, 414720) e0 e18
  e19

def fiberRayExpr_h_betaGap : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (143, 200)
  let e1 : LowMeanIntegerExpr := .atom (14, 1)
  let e2 : LowMeanIntegerExpr := .atom (2, 1)
  let e3 : LowMeanIntegerExpr := .add (16, 1) e1 e2
  let e4 : LowMeanIntegerExpr := .atom (1, 1)
  let e5 : LowMeanIntegerExpr := .neg (-1, 1) e4
  let e6 : LowMeanIntegerExpr := .add (15, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .atom (10, 1)
  let e8 : LowMeanIntegerExpr := .neg (-10, 1) e7
  let e9 : LowMeanIntegerExpr := .add (5, 1) e6 e8
  let e10 : LowMeanIntegerExpr := .mul (143, 40) e0 e9
  let e11 : LowMeanIntegerExpr := .atom (1, 2)
  let e12 : LowMeanIntegerExpr := .atom (5, 1)
  let e13 : LowMeanIntegerExpr := .atom (7, 25)
  let e14 : LowMeanIntegerExpr := .mul (7, 5) e12 e13
  let e15 : LowMeanIntegerExpr := .atom (4, 1)
  let e16 : LowMeanIntegerExpr := .mul (28, 5) e14 e15
  let e17 : LowMeanIntegerExpr := .atom (6, 1)
  let e18 : LowMeanIntegerExpr := .pow (49, 625) e13 2
  let e19 : LowMeanIntegerExpr := .neg (-49, 625) e18
  let e20 : LowMeanIntegerExpr := .add (576, 625) e4 e19
  let e21 : LowMeanIntegerExpr := .mul (3456, 625) e17 e20
  let e22 : LowMeanIntegerExpr := .div (875, 864) e16 e21
  let e23 : LowMeanIntegerExpr := .add (1307, 864) e11 e22
  let e24 : LowMeanIntegerExpr := .add (17, 1) e3 e4
  let e25 : LowMeanIntegerExpr := .mul (833, 625) e24 e18
  let e26 : LowMeanIntegerExpr := .pow (343, 15625) e13 3
  let e27 : LowMeanIntegerExpr := .mul (5488, 15625) e26 e3
  let e28 : LowMeanIntegerExpr := .mul (21952, 15625) e27 e15
  let e29 : LowMeanIntegerExpr := .add (42777, 15625) e25 e28
  let e30 : LowMeanIntegerExpr := .atom (12, 1)
  let e31 : LowMeanIntegerExpr := .pow (331776, 390625) e20 2
  let e32 : LowMeanIntegerExpr := .mul (3981312, 390625) e30 e31
  let e33 : LowMeanIntegerExpr := .div (118825, 442368) e29 e32
  let e34 : LowMeanIntegerExpr := .add (788009, 442368) e23 e33
  let e35 : LowMeanIntegerExpr := .mul (788009, 221184) e2 e34
  let e36 : LowMeanIntegerExpr := .neg (-788009, 221184) e35
  let e37 : LowMeanIntegerExpr := .add (13619, 1105920) e10 e36
  e37

def fiberRayExpr_h_squareGap : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (4, 5)
  let e1 : LowMeanIntegerExpr := .atom (143, 200)
  let e2 : LowMeanIntegerExpr := .pow (20449, 40000) e1 2
  let e3 : LowMeanIntegerExpr := .mul (20449, 50000) e0 e2
  let e4 : LowMeanIntegerExpr := .atom (10, 1)
  let e5 : LowMeanIntegerExpr := .mul (20449, 5000) e3 e4
  let e6 : LowMeanIntegerExpr := .atom (4, 1)
  let e7 : LowMeanIntegerExpr := .neg (-4, 1) e6
  let e8 : LowMeanIntegerExpr := .add (449, 5000) e5 e7
  e8

def fiberRayExpr_h_sqrtS : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (4, 1)
  let e1 : LowMeanIntegerExpr := .pow (16, 1) e0 2
  let e2 : LowMeanIntegerExpr := .atom (14, 1)
  let e3 : LowMeanIntegerExpr := .atom (2, 1)
  let e4 : LowMeanIntegerExpr := .add (16, 1) e2 e3
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (0, 1) e1 e5
  e6

def fiberRayExpr_h_sqrtV : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (31, 30)
  let e1 : LowMeanIntegerExpr := .pow (961, 900) e0 2
  let e2 : LowMeanIntegerExpr := .atom (1, 1)
  let e3 : LowMeanIntegerExpr := .atom (14, 1)
  let e4 : LowMeanIntegerExpr := .atom (2, 1)
  let e5 : LowMeanIntegerExpr := .add (16, 1) e3 e4
  let e6 : LowMeanIntegerExpr := .div (1, 16) e2 e5
  let e7 : LowMeanIntegerExpr := .neg (-1, 16) e6
  let e8 : LowMeanIntegerExpr := .add (15, 16) e2 e7
  let e9 : LowMeanIntegerExpr := .mul (961, 960) e1 e8
  let e10 : LowMeanIntegerExpr := .neg (-1, 1) e2
  let e11 : LowMeanIntegerExpr := .add (1, 960) e9 e10
  e11

def fiberRayExpr : FiberRayIdentity → FiberRayRole → LowMeanIntegerExpr
  | .a, .rho => fiberRayExpr_a_rho
  | .a, .kappa => fiberRayExpr_a_kappa
  | .a, .error => fiberRayExpr_a_error
  | .a, .rhoGap => fiberRayExpr_a_rhoGap
  | .a, .kappaGap => fiberRayExpr_a_kappaGap
  | .a, .betaGap => fiberRayExpr_a_betaGap
  | .a, .squareGap => fiberRayExpr_a_squareGap
  | .a, .sqrtS => fiberRayExpr_a_sqrtS
  | .a, .sqrtV => fiberRayExpr_a_sqrtV
  | .b, .rho => fiberRayExpr_b_rho
  | .b, .kappa => fiberRayExpr_b_kappa
  | .b, .error => fiberRayExpr_b_error
  | .b, .rhoGap => fiberRayExpr_b_rhoGap
  | .b, .kappaGap => fiberRayExpr_b_kappaGap
  | .b, .betaGap => fiberRayExpr_b_betaGap
  | .b, .squareGap => fiberRayExpr_b_squareGap
  | .b, .sqrtS => fiberRayExpr_b_sqrtS
  | .b, .sqrtV => fiberRayExpr_b_sqrtV
  | .d, .rho => fiberRayExpr_d_rho
  | .d, .kappa => fiberRayExpr_d_kappa
  | .d, .error => fiberRayExpr_d_error
  | .d, .rhoGap => fiberRayExpr_d_rhoGap
  | .d, .kappaGap => fiberRayExpr_d_kappaGap
  | .d, .betaGap => fiberRayExpr_d_betaGap
  | .d, .squareGap => fiberRayExpr_d_squareGap
  | .d, .sqrtS => fiberRayExpr_d_sqrtS
  | .d, .sqrtV => fiberRayExpr_d_sqrtV
  | .h, .rho => fiberRayExpr_h_rho
  | .h, .kappa => fiberRayExpr_h_kappa
  | .h, .error => fiberRayExpr_h_error
  | .h, .rhoGap => fiberRayExpr_h_rhoGap
  | .h, .kappaGap => fiberRayExpr_h_kappaGap
  | .h, .betaGap => fiberRayExpr_h_betaGap
  | .h, .squareGap => fiberRayExpr_h_squareGap
  | .h, .sqrtS => fiberRayExpr_h_sqrtS
  | .h, .sqrtV => fiberRayExpr_h_sqrtV

def fiberRayIdentityAt : ℕ → FiberRayIdentity
  | 0 => .a
  | 1 => .b
  | 2 => .d
  | _ => .h

def fiberRayRoleAt : ℕ → FiberRayRole
  | 0 => .rho
  | 1 => .kappa
  | 2 => .error
  | 3 => .rhoGap
  | 4 => .kappaGap
  | 5 => .betaGap
  | 6 => .squareGap
  | 7 => .sqrtS
  | _ => .sqrtV

end Erdos993Lean.Analytic.V213
