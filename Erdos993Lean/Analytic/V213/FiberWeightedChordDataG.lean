module

public import Erdos993Lean.Analytic.V213.FiberWeightedChordDataF

/-!
All eighteen accepted F12 weighted-chord identities. Canonical trees
retain actual F10 chord/F11 weight leaves; reduced Int/Nat nodes are
untrusted data until the separate shape/checker consumes them.
Source: Eq89.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

def fiberWeightedChordExpr_g_third_p042_logarithm : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1733, 1)
  let e1 : LowMeanIntegerExpr := .atom (1, 1)
  let e2 : LowMeanIntegerExpr := .mul (1733, 1) e0 e1
  let e3 : LowMeanIntegerExpr := .atom (2500, 1)
  let e4 : LowMeanIntegerExpr := .div (1733, 2500) e2 e3
  let e5 : LowMeanIntegerExpr := .atom (2, 1)
  let e6 : LowMeanIntegerExpr := .atom (7, 3)
  let e7 : LowMeanIntegerExpr := .atom (17, 25)
  let e8 : LowMeanIntegerExpr := .neg (-17, 25) e7
  let e9 : LowMeanIntegerExpr := .add (124, 75) e6 e8
  let e10 : LowMeanIntegerExpr := .atom (21, 50)
  let e11 : LowMeanIntegerExpr := .atom (1, 3)
  let e12 : LowMeanIntegerExpr := .neg (-1, 3) e11
  let e13 : LowMeanIntegerExpr := .add (13, 150) e10 e12
  let e14 : LowMeanIntegerExpr := .div (248, 13) e9 e13
  let e15 : LowMeanIntegerExpr := .atom (50, 1)
  let e16 : LowMeanIntegerExpr := .atom (2986, 3125)
  let e17 : LowMeanIntegerExpr := .mul (5972, 125) e15 e16
  let e18 : LowMeanIntegerExpr := .atom (3, 25)
  let e19 : LowMeanIntegerExpr := .mul (17916, 3125) e17 e18
  let e20 : LowMeanIntegerExpr := .div (193750, 58227) e14 e19
  let e21 : LowMeanIntegerExpr := .pow (2, 1) e5 1
  let e22 : LowMeanIntegerExpr := .div (96875, 58227) e20 e21
  let e23 : LowMeanIntegerExpr := .neg (-1, 1) e1
  let e24 : LowMeanIntegerExpr := .add (38648, 58227) e22 e23
  let e25 : LowMeanIntegerExpr := .add (155102, 58227) e22 e1
  let e26 : LowMeanIntegerExpr := .div (19324, 77551) e24 e25
  let e27 : LowMeanIntegerExpr := .pow (7215909644224, 466403936115151) e26 3
  let e28 : LowMeanIntegerExpr := .atom (3, 1)
  let e29 : LowMeanIntegerExpr := .div (7215909644224, 1399211808345453) e27 e28
  let e30 : LowMeanIntegerExpr := .add (355868654089396, 1399211808345453) e26 e29
  let e31 : LowMeanIntegerExpr := .pow (2694543158435361946624, 2805026777523253797912751) e26 5
  let e32 : LowMeanIntegerExpr := .atom (5, 1)
  let e33 : LowMeanIntegerExpr := .div (2694543158435361946624, 14025133887616268989563755) e31 e32
  let e34 : LowMeanIntegerExpr := .add (10709334484222209520334852, 42075401662848806968691265) e30 e33
  let e35 : LowMeanIntegerExpr := .mul (21418668968444419040669704, 42075401662848806968691265) e5 e34
  let e36 : LowMeanIntegerExpr := .pow (1006188157924421749573807489024, 16869873115050012782969089361470351) e26 7
  let e37 : LowMeanIntegerExpr := .mul (2012376315848843499147614978048, 16869873115050012782969089361470351) e5 e36
  let e38 : LowMeanIntegerExpr := .atom (7, 1)
  let e39 : LowMeanIntegerExpr := .pow (373416976, 6014157601) e26 2
  let e40 : LowMeanIntegerExpr := .neg (-373416976, 6014157601) e39
  let e41 : LowMeanIntegerExpr := .add (5640740625, 6014157601) e1 e40
  let e42 : LowMeanIntegerExpr := .mul (39485184375, 6014157601) e38 e41
  let e43 : LowMeanIntegerExpr := .div (2012376315848843499147614978048, 110756999487317782060503963398465625) e37 e42
  let e44 : LowMeanIntegerExpr := .add (56383351928723778360872740009423048, 110756999487317782060503963398465625) e35 e43
  let e45 : LowMeanIntegerExpr := .add (532640415893329859540856349748957677, 443027997949271128242015853593862500) e4 e44
  e45

def fiberWeightedChordExpr_g_third_p042_gap : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (50, 1)
  let e1 : LowMeanIntegerExpr := .atom (903, 2000)
  let e2 : LowMeanIntegerExpr := .mul (903, 40) e0 e1
  let e3 : LowMeanIntegerExpr := .atom (1, 1)
  let e4 : LowMeanIntegerExpr := .add (943, 40) e2 e3
  let e5 : LowMeanIntegerExpr := .atom (2986, 3125)
  let e6 : LowMeanIntegerExpr := .mul (5972, 125) e0 e5
  let e7 : LowMeanIntegerExpr := .atom (1, 3)
  let e8 : LowMeanIntegerExpr := .atom (7, 3)
  let e9 : LowMeanIntegerExpr := .atom (17, 25)
  let e10 : LowMeanIntegerExpr := .neg (-17, 25) e9
  let e11 : LowMeanIntegerExpr := .add (124, 75) e8 e10
  let e12 : LowMeanIntegerExpr := .atom (21, 50)
  let e13 : LowMeanIntegerExpr := .neg (-1, 3) e7
  let e14 : LowMeanIntegerExpr := .add (13, 150) e12 e13
  let e15 : LowMeanIntegerExpr := .div (248, 13) e11 e14
  let e16 : LowMeanIntegerExpr := .div (91, 744) e8 e15
  let e17 : LowMeanIntegerExpr := .add (113, 248) e7 e16
  let e18 : LowMeanIntegerExpr := .mul (168709, 7750) e6 e17
  let e19 : LowMeanIntegerExpr := .neg (-168709, 7750) e18
  let e20 : LowMeanIntegerExpr := .add (55989, 31000) e4 e19
  let e21 : LowMeanIntegerExpr := .atom (1733, 1)
  let e22 : LowMeanIntegerExpr := .mul (1733, 1) e21 e3
  let e23 : LowMeanIntegerExpr := .atom (2500, 1)
  let e24 : LowMeanIntegerExpr := .div (1733, 2500) e22 e23
  let e25 : LowMeanIntegerExpr := .atom (2, 1)
  let e26 : LowMeanIntegerExpr := .atom (3, 25)
  let e27 : LowMeanIntegerExpr := .mul (17916, 3125) e6 e26
  let e28 : LowMeanIntegerExpr := .div (193750, 58227) e15 e27
  let e29 : LowMeanIntegerExpr := .pow (2, 1) e25 1
  let e30 : LowMeanIntegerExpr := .div (96875, 58227) e28 e29
  let e31 : LowMeanIntegerExpr := .neg (-1, 1) e3
  let e32 : LowMeanIntegerExpr := .add (38648, 58227) e30 e31
  let e33 : LowMeanIntegerExpr := .add (155102, 58227) e30 e3
  let e34 : LowMeanIntegerExpr := .div (19324, 77551) e32 e33
  let e35 : LowMeanIntegerExpr := .pow (7215909644224, 466403936115151) e34 3
  let e36 : LowMeanIntegerExpr := .atom (3, 1)
  let e37 : LowMeanIntegerExpr := .div (7215909644224, 1399211808345453) e35 e36
  let e38 : LowMeanIntegerExpr := .add (355868654089396, 1399211808345453) e34 e37
  let e39 : LowMeanIntegerExpr := .pow (2694543158435361946624, 2805026777523253797912751) e34 5
  let e40 : LowMeanIntegerExpr := .atom (5, 1)
  let e41 : LowMeanIntegerExpr := .div (2694543158435361946624, 14025133887616268989563755) e39 e40
  let e42 : LowMeanIntegerExpr := .add (10709334484222209520334852, 42075401662848806968691265) e38 e41
  let e43 : LowMeanIntegerExpr := .mul (21418668968444419040669704, 42075401662848806968691265) e25 e42
  let e44 : LowMeanIntegerExpr := .pow (1006188157924421749573807489024, 16869873115050012782969089361470351) e34 7
  let e45 : LowMeanIntegerExpr := .mul (2012376315848843499147614978048, 16869873115050012782969089361470351) e25 e44
  let e46 : LowMeanIntegerExpr := .atom (7, 1)
  let e47 : LowMeanIntegerExpr := .pow (373416976, 6014157601) e34 2
  let e48 : LowMeanIntegerExpr := .neg (-373416976, 6014157601) e47
  let e49 : LowMeanIntegerExpr := .add (5640740625, 6014157601) e3 e48
  let e50 : LowMeanIntegerExpr := .mul (39485184375, 6014157601) e46 e49
  let e51 : LowMeanIntegerExpr := .div (2012376315848843499147614978048, 110756999487317782060503963398465625) e45 e50
  let e52 : LowMeanIntegerExpr := .add (56383351928723778360872740009423048, 110756999487317782060503963398465625) e43 e51
  let e53 : LowMeanIntegerExpr := .add (532640415893329859540856349748957677, 443027997949271128242015853593862500) e24 e52
  let e54 : LowMeanIntegerExpr := .neg (-532640415893329859540856349748957677, 443027997949271128242015853593862500) e53
  let e55 : LowMeanIntegerExpr := .add (535022044160549390540366373203166421, 886055995898542256484031707187725000) e20 e54
  e55

def fiberWeightedChordExpr_g_p042_p044_logarithm : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1733, 1)
  let e1 : LowMeanIntegerExpr := .atom (2, 1)
  let e2 : LowMeanIntegerExpr := .mul (3466, 1) e0 e1
  let e3 : LowMeanIntegerExpr := .atom (2500, 1)
  let e4 : LowMeanIntegerExpr := .div (1733, 1250) e2 e3
  let e5 : LowMeanIntegerExpr := .atom (49, 100)
  let e6 : LowMeanIntegerExpr := .atom (3, 25)
  let e7 : LowMeanIntegerExpr := .div (49, 12) e5 e6
  let e8 : LowMeanIntegerExpr := .pow (4, 1) e1 2
  let e9 : LowMeanIntegerExpr := .div (49, 48) e7 e8
  let e10 : LowMeanIntegerExpr := .atom (1, 1)
  let e11 : LowMeanIntegerExpr := .neg (-1, 1) e10
  let e12 : LowMeanIntegerExpr := .add (1, 48) e9 e11
  let e13 : LowMeanIntegerExpr := .add (97, 48) e9 e10
  let e14 : LowMeanIntegerExpr := .div (1, 97) e12 e13
  let e15 : LowMeanIntegerExpr := .pow (1, 912673) e14 3
  let e16 : LowMeanIntegerExpr := .atom (3, 1)
  let e17 : LowMeanIntegerExpr := .div (1, 2738019) e15 e16
  let e18 : LowMeanIntegerExpr := .add (28228, 2738019) e14 e17
  let e19 : LowMeanIntegerExpr := .pow (1, 8587340257) e14 5
  let e20 : LowMeanIntegerExpr := .atom (5, 1)
  let e21 : LowMeanIntegerExpr := .div (1, 42936701285) e19 e20
  let e22 : LowMeanIntegerExpr := .add (1327986263, 128810103855) e18 e21
  let e23 : LowMeanIntegerExpr := .mul (2655972526, 128810103855) e1 e22
  let e24 : LowMeanIntegerExpr := .pow (1, 80798284478113) e14 7
  let e25 : LowMeanIntegerExpr := .mul (2, 80798284478113) e1 e24
  let e26 : LowMeanIntegerExpr := .atom (7, 1)
  let e27 : LowMeanIntegerExpr := .pow (1, 9409) e14 2
  let e28 : LowMeanIntegerExpr := .neg (-1, 9409) e27
  let e29 : LowMeanIntegerExpr := .add (9408, 9409) e10 e28
  let e30 : LowMeanIntegerExpr := .mul (65856, 9409) e26 e29
  let e31 : LowMeanIntegerExpr := .div (1, 282763939982496) e25 e30
  let e32 : LowMeanIntegerExpr := .add (29151954445381, 1413819699912480) e23 e31
  let e33 : LowMeanIntegerExpr := .add (248658948300505409, 176727462489060000) e4 e32
  e33

def fiberWeightedChordExpr_g_p042_p044_gap : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (50, 1)
  let e1 : LowMeanIntegerExpr := .atom (903, 2000)
  let e2 : LowMeanIntegerExpr := .mul (903, 40) e0 e1
  let e3 : LowMeanIntegerExpr := .atom (2986, 3125)
  let e4 : LowMeanIntegerExpr := .mul (5972, 125) e0 e3
  let e5 : LowMeanIntegerExpr := .atom (11, 25)
  let e6 : LowMeanIntegerExpr := .mul (65692, 3125) e4 e5
  let e7 : LowMeanIntegerExpr := .neg (-65692, 3125) e6
  let e8 : LowMeanIntegerExpr := .add (38839, 25000) e2 e7
  let e9 : LowMeanIntegerExpr := .atom (1733, 1)
  let e10 : LowMeanIntegerExpr := .atom (2, 1)
  let e11 : LowMeanIntegerExpr := .mul (3466, 1) e9 e10
  let e12 : LowMeanIntegerExpr := .atom (2500, 1)
  let e13 : LowMeanIntegerExpr := .div (1733, 1250) e11 e12
  let e14 : LowMeanIntegerExpr := .atom (49, 100)
  let e15 : LowMeanIntegerExpr := .atom (3, 25)
  let e16 : LowMeanIntegerExpr := .div (49, 12) e14 e15
  let e17 : LowMeanIntegerExpr := .pow (4, 1) e10 2
  let e18 : LowMeanIntegerExpr := .div (49, 48) e16 e17
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-1, 1) e19
  let e21 : LowMeanIntegerExpr := .add (1, 48) e18 e20
  let e22 : LowMeanIntegerExpr := .add (97, 48) e18 e19
  let e23 : LowMeanIntegerExpr := .div (1, 97) e21 e22
  let e24 : LowMeanIntegerExpr := .pow (1, 912673) e23 3
  let e25 : LowMeanIntegerExpr := .atom (3, 1)
  let e26 : LowMeanIntegerExpr := .div (1, 2738019) e24 e25
  let e27 : LowMeanIntegerExpr := .add (28228, 2738019) e23 e26
  let e28 : LowMeanIntegerExpr := .pow (1, 8587340257) e23 5
  let e29 : LowMeanIntegerExpr := .atom (5, 1)
  let e30 : LowMeanIntegerExpr := .div (1, 42936701285) e28 e29
  let e31 : LowMeanIntegerExpr := .add (1327986263, 128810103855) e27 e30
  let e32 : LowMeanIntegerExpr := .mul (2655972526, 128810103855) e10 e31
  let e33 : LowMeanIntegerExpr := .pow (1, 80798284478113) e23 7
  let e34 : LowMeanIntegerExpr := .mul (2, 80798284478113) e10 e33
  let e35 : LowMeanIntegerExpr := .atom (7, 1)
  let e36 : LowMeanIntegerExpr := .pow (1, 9409) e23 2
  let e37 : LowMeanIntegerExpr := .neg (-1, 9409) e36
  let e38 : LowMeanIntegerExpr := .add (9408, 9409) e19 e37
  let e39 : LowMeanIntegerExpr := .mul (65856, 9409) e35 e38
  let e40 : LowMeanIntegerExpr := .div (1, 282763939982496) e34 e39
  let e41 : LowMeanIntegerExpr := .add (29151954445381, 1413819699912480) e32 e40
  let e42 : LowMeanIntegerExpr := .add (248658948300505409, 176727462489060000) e13 e41
  let e43 : LowMeanIntegerExpr := .neg (-248658948300505409, 176727462489060000) e42
  let e44 : LowMeanIntegerExpr := .add (129488841619993223, 883637312445300000) e8 e43
  e44

end Erdos993Lean.Analytic.V213
