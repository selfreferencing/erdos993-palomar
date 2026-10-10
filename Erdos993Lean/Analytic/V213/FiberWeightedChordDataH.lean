module

public import Erdos993Lean.Analytic.V213.FiberWeightedChordDataG

/-!
All eighteen accepted F12 weighted-chord identities. Canonical trees
retain actual F10 chord/F11 weight leaves; reduced Int/Nat nodes are
untrusted data until the separate shape/checker consumes them.
Source: Eq89.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

def fiberWeightedChordExpr_h_third_p038_logarithm : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1733, 1)
  let e1 : LowMeanIntegerExpr := .atom (4, 1)
  let e2 : LowMeanIntegerExpr := .mul (6932, 1) e0 e1
  let e3 : LowMeanIntegerExpr := .atom (2500, 1)
  let e4 : LowMeanIntegerExpr := .div (1733, 625) e2 e3
  let e5 : LowMeanIntegerExpr := .atom (2, 1)
  let e6 : LowMeanIntegerExpr := .atom (26, 25)
  let e7 : LowMeanIntegerExpr := .atom (17, 500)
  let e8 : LowMeanIntegerExpr := .div (520, 17) e6 e7
  let e9 : LowMeanIntegerExpr := .pow (16, 1) e5 4
  let e10 : LowMeanIntegerExpr := .div (65, 34) e8 e9
  let e11 : LowMeanIntegerExpr := .atom (1, 1)
  let e12 : LowMeanIntegerExpr := .neg (-1, 1) e11
  let e13 : LowMeanIntegerExpr := .add (31, 34) e10 e12
  let e14 : LowMeanIntegerExpr := .add (99, 34) e10 e11
  let e15 : LowMeanIntegerExpr := .div (31, 99) e13 e14
  let e16 : LowMeanIntegerExpr := .pow (29791, 970299) e15 3
  let e17 : LowMeanIntegerExpr := .atom (3, 1)
  let e18 : LowMeanIntegerExpr := .div (29791, 2910897) e16 e17
  let e19 : LowMeanIntegerExpr := .add (941284, 2910897) e15 e18
  let e20 : LowMeanIntegerExpr := .pow (28629151, 9509900499) e15 5
  let e21 : LowMeanIntegerExpr := .atom (5, 1)
  let e22 : LowMeanIntegerExpr := .div (28629151, 47549502495) e20 e21
  let e23 : LowMeanIntegerExpr := .add (15404503291, 47549502495) e19 e22
  let e24 : LowMeanIntegerExpr := .mul (30809006582, 47549502495) e5 e23
  let e25 : LowMeanIntegerExpr := .pow (27512614111, 93206534790699) e15 7
  let e26 : LowMeanIntegerExpr := .mul (55025228222, 93206534790699) e5 e25
  let e27 : LowMeanIntegerExpr := .atom (7, 1)
  let e28 : LowMeanIntegerExpr := .pow (961, 9801) e15 2
  let e29 : LowMeanIntegerExpr := .neg (-961, 9801) e28
  let e30 : LowMeanIntegerExpr := .add (8840, 9801) e11 e29
  let e31 : LowMeanIntegerExpr := .mul (61880, 9801) e27 e30
  let e32 : LowMeanIntegerExpr := .div (27512614111, 294236321439060) e26 e31
  let e33 : LowMeanIntegerExpr := .add (190673645343527, 294236321439060) e24 e32
  let e34 : LowMeanIntegerExpr := .add (125816514678719071, 36779540179882500) e4 e33
  e34

def fiberWeightedChordExpr_h_third_p038_gap : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (40, 1)
  let e1 : LowMeanIntegerExpr := .atom (294, 625)
  let e2 : LowMeanIntegerExpr := .mul (2352, 125) e0 e1
  let e3 : LowMeanIntegerExpr := .atom (101161, 100000)
  let e4 : LowMeanIntegerExpr := .mul (101161, 2500) e0 e3
  let e5 : LowMeanIntegerExpr := .atom (19, 50)
  let e6 : LowMeanIntegerExpr := .mul (1922059, 125000) e4 e5
  let e7 : LowMeanIntegerExpr := .neg (-1922059, 125000) e6
  let e8 : LowMeanIntegerExpr := .add (429941, 125000) e2 e7
  let e9 : LowMeanIntegerExpr := .atom (1733, 1)
  let e10 : LowMeanIntegerExpr := .atom (4, 1)
  let e11 : LowMeanIntegerExpr := .mul (6932, 1) e9 e10
  let e12 : LowMeanIntegerExpr := .atom (2500, 1)
  let e13 : LowMeanIntegerExpr := .div (1733, 625) e11 e12
  let e14 : LowMeanIntegerExpr := .atom (2, 1)
  let e15 : LowMeanIntegerExpr := .atom (26, 25)
  let e16 : LowMeanIntegerExpr := .atom (17, 500)
  let e17 : LowMeanIntegerExpr := .div (520, 17) e15 e16
  let e18 : LowMeanIntegerExpr := .pow (16, 1) e14 4
  let e19 : LowMeanIntegerExpr := .div (65, 34) e17 e18
  let e20 : LowMeanIntegerExpr := .atom (1, 1)
  let e21 : LowMeanIntegerExpr := .neg (-1, 1) e20
  let e22 : LowMeanIntegerExpr := .add (31, 34) e19 e21
  let e23 : LowMeanIntegerExpr := .add (99, 34) e19 e20
  let e24 : LowMeanIntegerExpr := .div (31, 99) e22 e23
  let e25 : LowMeanIntegerExpr := .pow (29791, 970299) e24 3
  let e26 : LowMeanIntegerExpr := .atom (3, 1)
  let e27 : LowMeanIntegerExpr := .div (29791, 2910897) e25 e26
  let e28 : LowMeanIntegerExpr := .add (941284, 2910897) e24 e27
  let e29 : LowMeanIntegerExpr := .pow (28629151, 9509900499) e24 5
  let e30 : LowMeanIntegerExpr := .atom (5, 1)
  let e31 : LowMeanIntegerExpr := .div (28629151, 47549502495) e29 e30
  let e32 : LowMeanIntegerExpr := .add (15404503291, 47549502495) e28 e31
  let e33 : LowMeanIntegerExpr := .mul (30809006582, 47549502495) e14 e32
  let e34 : LowMeanIntegerExpr := .pow (27512614111, 93206534790699) e24 7
  let e35 : LowMeanIntegerExpr := .mul (55025228222, 93206534790699) e14 e34
  let e36 : LowMeanIntegerExpr := .atom (7, 1)
  let e37 : LowMeanIntegerExpr := .pow (961, 9801) e24 2
  let e38 : LowMeanIntegerExpr := .neg (-961, 9801) e37
  let e39 : LowMeanIntegerExpr := .add (8840, 9801) e20 e38
  let e40 : LowMeanIntegerExpr := .mul (61880, 9801) e36 e39
  let e41 : LowMeanIntegerExpr := .div (27512614111, 294236321439060) e35 e40
  let e42 : LowMeanIntegerExpr := .add (190673645343527, 294236321439060) e33 e41
  let e43 : LowMeanIntegerExpr := .add (125816514678719071, 36779540179882500) e13 e42
  let e44 : LowMeanIntegerExpr := .neg (-125816514678719071, 36779540179882500) e43
  let e45 : LowMeanIntegerExpr := .add (34387179855591223, 1838977008994125000) e8 e44
  e45

end Erdos993Lean.Analytic.V213
