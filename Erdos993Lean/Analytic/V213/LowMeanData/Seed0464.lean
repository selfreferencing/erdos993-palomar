module

public import Erdos993Lean.Analytic.V213.LowMeanCoreAll
public import Erdos993Lean.Analytic.V213.LowMeanData.Seed0400
public import Erdos993Lean.Analytic.V213.LowMeanFiberSeed
public import Erdos993Lean.Analytic.V213.LowMeanIntegerExpr
public import Erdos993Lean.Analytic.V213.LowMeanSeedGeometry
public import Erdos993Lean.Analytic.V213.LowMeanWidthData
public import Erdos993Lean.Ceiling.Prefix
public import Erdos993Lean.Ceiling.Statement

/-! Exact core/budget keys and equation-51 targets for the direct fibers. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanSeedTargetExpr0464 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (84077, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (129, 100000)
  let e3 : LowMeanIntegerExpr := .atom (23, 1)
  let e4 : LowMeanIntegerExpr := .atom (57, 2)
  let e5 : LowMeanIntegerExpr := .neg (-57, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-11, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1419, 200000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (38491, 500000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (137, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (121, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (16577, 4000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-16577, 4000000) e11
  let e13 : LowMeanIntegerExpr := .add (291351, 4000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (2773, 500000)
  let e15 : LowMeanIntegerExpr := .atom (8, 13)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (19, 29)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-8, 13) e15
  let e21 : LowMeanIntegerExpr := .add (5, 13) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (40, 169) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-19, 29) e17
  let e24 : LowMeanIntegerExpr := .add (10, 29) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (190, 841) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (40, 169) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (40, 169) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2773, 2112500) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (63779, 2112500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (69647599, 676000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (79, 20)
  let e33 : LowMeanIntegerExpr := .pow (11920928955078125, 41753905413413116367045797) e21 23
  let e34 : LowMeanIntegerExpr := .mul (188350677490234375, 167015621653652465468183188) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-188350677490234375, 167015621653652465468183188) e34
  let e36 : LowMeanIntegerExpr := .add (17207451059680837007235107154387, 167015621653652465468183188000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (17209121215897373531889788986267, 167015621653652465468183188000000) e0 e36
  let e38 : LowMeanIntegerExpr := .atom (21, 1)
  let e39 : LowMeanIntegerExpr := .add (-15, 2) e38 e5
  let e40 : LowMeanIntegerExpr := .mul (-387, 40000) e2 e39
  let e41 : LowMeanIntegerExpr := .add (37201, 500000) e1 e40
  let e42 : LowMeanIntegerExpr := .pow (225, 4) e39 2
  let e43 : LowMeanIntegerExpr := .mul (1233, 160000) e9 e42
  let e44 : LowMeanIntegerExpr := .neg (-1233, 160000) e43
  let e45 : LowMeanIntegerExpr := .add (266783, 4000000) e41 e44
  let e46 : LowMeanIntegerExpr := .mul (58233, 2112500) e29 e38
  let e47 : LowMeanIntegerExpr := .add (63720887, 676000000) e45 e46
  let e48 : LowMeanIntegerExpr := .pow (476837158203125, 247064529073450392704413) e21 21
  let e49 : LowMeanIntegerExpr := .mul (7534027099609375, 988258116293801570817652) e32 e48
  let e50 : LowMeanIntegerExpr := .neg (-7534027099609375, 988258116293801570817652) e49
  let e51 : LowMeanIntegerExpr := .add (93154850091993889583663610499, 988258116293801570817652000000) e47 e50
  let e52 : LowMeanIntegerExpr := .neg (-93154850091993889583663610499, 988258116293801570817652000000) e51
  let e53 : LowMeanIntegerExpr := .add (45810985948450193507832462873, 5219238176676639545880724625000) e37 e52
  e53

noncomputable def lowMeanSeedRecord0464 : LowMeanDirectSeedInput :=
  { record := 464, positions := [{ j := 11, mode := 0, left := 957, right := 0 }, { j := 17, mode := 0, left := 958, right := 0 }, { j := 18, mode := 0, left := 959, right := 0 }], target := { R := 23, expr := lowMeanSeedTargetExpr0464 } }

noncomputable def lowMeanSeedTargetExpr0465 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (84077, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (129, 100000)
  let e3 : LowMeanIntegerExpr := .atom (26, 1)
  let e4 : LowMeanIntegerExpr := .atom (57, 2)
  let e5 : LowMeanIntegerExpr := .neg (-57, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-5, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-129, 40000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (20213, 250000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (137, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (25, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (137, 160000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-137, 160000) e11
  let e13 : LowMeanIntegerExpr := .add (319983, 4000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (2773, 500000)
  let e15 : LowMeanIntegerExpr := .atom (8, 13)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (19, 29)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-8, 13) e15
  let e21 : LowMeanIntegerExpr := .add (5, 13) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (40, 169) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-19, 29) e17
  let e24 : LowMeanIntegerExpr := .add (10, 29) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (190, 841) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (40, 169) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (40, 169) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2773, 2112500) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (2773, 81250) e29 e3
  let e31 : LowMeanIntegerExpr := .add (5934499, 52000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (79, 20)
  let e33 : LowMeanIntegerExpr := .pow (1490116119384765625, 91733330193268616658399616009) e21 26
  let e34 : LowMeanIntegerExpr := .mul (23543834686279296875, 366933320773074466633598464036) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-23543834686279296875, 366933320773074466633598464036) e34
  let e36 : LowMeanIntegerExpr := .add (41876258153273273951463461802368807, 366933320773074466633598464036000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (41879927486481004696129797787009167, 366933320773074466633598464036000000) e0 e36
  let e38 : LowMeanIntegerExpr := .atom (24, 1)
  let e39 : LowMeanIntegerExpr := .add (-9, 2) e38 e5
  let e40 : LowMeanIntegerExpr := .mul (-1161, 200000) e2 e39
  let e41 : LowMeanIntegerExpr := .add (1223, 15625) e1 e40
  let e42 : LowMeanIntegerExpr := .pow (81, 4) e39 2
  let e43 : LowMeanIntegerExpr := .mul (11097, 4000000) e9 e42
  let e44 : LowMeanIntegerExpr := .neg (-11097, 4000000) e43
  let e45 : LowMeanIntegerExpr := .add (301991, 4000000) e41 e44
  let e46 : LowMeanIntegerExpr := .mul (16638, 528125) e29 e38
  let e47 : LowMeanIntegerExpr := .add (72333119, 676000000) e45 e46
  let e48 : LowMeanIntegerExpr := .pow (59604644775390625, 542800770374370512771595361) e21 24
  let e49 : LowMeanIntegerExpr := .mul (941753387451171875, 2171203081497482051086381444) e32 e48
  let e50 : LowMeanIntegerExpr := .neg (-941753387451171875, 2171203081497482051086381444) e49
  let e51 : LowMeanIntegerExpr := .add (232322322826181623497933610603911, 2171203081497482051086381444000000) e47 e50
  let e52 : LowMeanIntegerExpr := .neg (-232322322826181623497933610603911, 2171203081497482051086381444000000) e51
  let e53 : LowMeanIntegerExpr := .add (163590933053519395311188599684263, 22933332548317154164599904002250000) e37 e52
  e53

noncomputable def lowMeanSeedRecord0465 : LowMeanDirectSeedInput :=
  { record := 465, positions := [{ j := 13, mode := 0, left := 960, right := 0 }, { j := 14, mode := 0, left := 961, right := 0 }, { j := 18, mode := 0, left := 962, right := 0 }, { j := 19, mode := 0, left := 963, right := 0 }, { j := 20, mode := 0, left := 964, right := 0 }], target := { R := 26, expr := lowMeanSeedTargetExpr0465 } }

noncomputable def lowMeanSeedTargetExpr0466 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (84077, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (129, 100000)
  let e3 : LowMeanIntegerExpr := .atom (28, 1)
  let e4 : LowMeanIntegerExpr := .atom (57, 2)
  let e5 : LowMeanIntegerExpr := .neg (-57, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-1, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-129, 200000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (10429, 125000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (137, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (1, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (137, 4000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-137, 4000000) e11
  let e13 : LowMeanIntegerExpr := .add (333591, 4000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (2773, 500000)
  let e15 : LowMeanIntegerExpr := .atom (8, 13)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (19, 29)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-8, 13) e15
  let e21 : LowMeanIntegerExpr := .add (5, 13) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (40, 169) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-19, 29) e17
  let e24 : LowMeanIntegerExpr := .add (10, 29) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (190, 841) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (40, 169) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (40, 169) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2773, 2112500) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (19411, 528125) e29 e3
  let e31 : LowMeanIntegerExpr := .add (81222959, 676000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (79, 20)
  let e33 : LowMeanIntegerExpr := .pow (37252902984619140625, 15502932802662396215269535105521) e21 28
  let e34 : LowMeanIntegerExpr := .mul (588595867156982421875, 62011731210649584861078140422084) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-588595867156982421875, 62011731210649584861078140422084) e34
  let e36 : LowMeanIntegerExpr := .add (7450852516632723059674926594839750631, 62011731210649584861078140422084000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (7451472633944829555523537376243971471, 62011731210649584861078140422084000000) e0 e36
  let e38 : LowMeanIntegerExpr := .atom (27, 1)
  let e39 : LowMeanIntegerExpr := .add (-3, 2) e38 e5
  let e40 : LowMeanIntegerExpr := .mul (-387, 200000) e2 e39
  let e41 : LowMeanIntegerExpr := .add (41071, 500000) e1 e40
  let e42 : LowMeanIntegerExpr := .pow (9, 4) e39 2
  let e43 : LowMeanIntegerExpr := .mul (1233, 4000000) e9 e42
  let e44 : LowMeanIntegerExpr := .neg (-1233, 4000000) e43
  let e45 : LowMeanIntegerExpr := .add (65467, 800000) e41 e44
  let e46 : LowMeanIntegerExpr := .mul (74871, 2112500) e29 e38
  let e47 : LowMeanIntegerExpr := .add (15855667, 135200000) e45 e46
  let e48 : LowMeanIntegerExpr := .pow (7450580596923828125, 1192533292512492016559195008117) e21 27
  let e49 : LowMeanIntegerExpr := .mul (117719173431396484375, 4770133170049968066236780032468) e32 e48
  let e50 : LowMeanIntegerExpr := .neg (-117719173431396484375, 4770133170049968066236780032468) e49
  let e51 : LowMeanIntegerExpr := .add (111884087387649459720354323460890231, 954026634009993613247356006493600000) e47 e50
  let e52 : LowMeanIntegerExpr := .neg (-111884087387649459720354323460890231, 954026634009993613247356006493600000) e51
  let e53 : LowMeanIntegerExpr := .add (22375869218451834212563293910763307, 7751466401331198107634767552760500000) e37 e52
  e53

noncomputable def lowMeanSeedRecord0466 : LowMeanDirectSeedInput :=
  { record := 466, positions := [{ j := 15, mode := 0, left := 965, right := 0 }, { j := 16, mode := 0, left := 966, right := 0 }, { j := 20, mode := 0, left := 967, right := 0 }, { j := 21, mode := 0, left := 968, right := 0 }, { j := 22, mode := 0, left := 969, right := 0 }], target := { R := 28, expr := lowMeanSeedTargetExpr0466 } }

noncomputable def lowMeanSeedTargetExpr0467 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (84077, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (129, 100000)
  let e3 : LowMeanIntegerExpr := .atom (30, 1)
  let e4 : LowMeanIntegerExpr := .atom (57, 2)
  let e5 : LowMeanIntegerExpr := .neg (-57, 2) e4
  let e6 : LowMeanIntegerExpr := .add (3, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (387, 200000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (21503, 250000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (137, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (9, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1233, 4000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1233, 4000000) e11
  let e13 : LowMeanIntegerExpr := .add (68563, 800000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (2773, 500000)
  let e15 : LowMeanIntegerExpr := .atom (8, 13)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (19, 29)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-8, 13) e15
  let e21 : LowMeanIntegerExpr := .add (5, 13) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (40, 169) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-19, 29) e17
  let e24 : LowMeanIntegerExpr := .add (10, 29) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (190, 841) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (40, 169) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (40, 169) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2773, 2112500) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (8319, 211250) e29 e3
  let e31 : LowMeanIntegerExpr := .add (16911307, 135200000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (79, 20)
  let e33 : LowMeanIntegerExpr := .pow (931322574615478515625, 2619995643649944960380551432833049) e21 30
  let e34 : LowMeanIntegerExpr := .mul (14714896678924560546875, 10479982574599779841522205731332196) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-14714896678924560546875, 10479982574599779841522205731332196) e34
  let e36 : LowMeanIntegerExpr := .add (262174856023251220416276283807368025947, 2095996514919955968304441146266439200000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (262195815988400419975959328218830690339, 2095996514919955968304441146266439200000) e0 e36
  let e38 : LowMeanIntegerExpr := .atom (29, 1)
  let e39 : LowMeanIntegerExpr := .add (1, 2) e38 e5
  let e40 : LowMeanIntegerExpr := .mul (129, 200000) e2 e39
  let e41 : LowMeanIntegerExpr := .add (42361, 500000) e1 e40
  let e42 : LowMeanIntegerExpr := .pow (1, 4) e39 2
  let e43 : LowMeanIntegerExpr := .mul (137, 4000000) e9 e42
  let e44 : LowMeanIntegerExpr := .neg (-137, 4000000) e43
  let e45 : LowMeanIntegerExpr := .add (338751, 4000000) e41 e44
  let e46 : LowMeanIntegerExpr := .mul (80417, 2112500) e29 e38
  let e47 : LowMeanIntegerExpr := .add (82982359, 676000000) e45 e46
  let e48 : LowMeanIntegerExpr := .pow (186264514923095703125, 201538126434611150798503956371773) e21 29
  let e49 : LowMeanIntegerExpr := .mul (2942979335784912109375, 806152505738444603194015825487092) e32 e48
  let e50 : LowMeanIntegerExpr := .neg (-2942979335784912109375, 806152505738444603194015825487092) e49
  let e51 : LowMeanIntegerExpr := .add (98959225795780645166964152805197808003, 806152505738444603194015825487092000000) e47 e50
  let e52 : LowMeanIntegerExpr := .neg (-98959225795780645166964152805197808003, 806152505738444603194015825487092000000) e51
  let e53 : LowMeanIntegerExpr := .add (3063643074606714088657831828322743457, 1309997821824972480190275716416524500000) e37 e52
  e53

noncomputable def lowMeanSeedRecord0467 : LowMeanDirectSeedInput :=
  { record := 467, positions := [{ j := 16, mode := 0, left := 970, right := 0 }, { j := 17, mode := 0, left := 971, right := 0 }, { j := 21, mode := 0, left := 972, right := 0 }, { j := 22, mode := 0, left := 973, right := 0 }, { j := 23, mode := 0, left := 974, right := 0 }, { j := 24, mode := 0, left := 975, right := 0 }], target := { R := 30, expr := lowMeanSeedTargetExpr0467 } }

noncomputable def lowMeanSeedTargetExpr0468 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (84077, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (129, 100000)
  let e3 : LowMeanIntegerExpr := .atom (31, 1)
  let e4 : LowMeanIntegerExpr := .atom (57, 2)
  let e5 : LowMeanIntegerExpr := .neg (-57, 2) e4
  let e6 : LowMeanIntegerExpr := .add (5, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (129, 40000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (43651, 500000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (137, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (25, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (137, 160000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-137, 160000) e11
  let e13 : LowMeanIntegerExpr := .add (345783, 4000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (2773, 500000)
  let e15 : LowMeanIntegerExpr := .atom (8, 13)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (19, 29)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-8, 13) e15
  let e21 : LowMeanIntegerExpr := .add (5, 13) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (40, 169) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-19, 29) e17
  let e24 : LowMeanIntegerExpr := .add (10, 29) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (190, 841) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (40, 169) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (40, 169) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2773, 2112500) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (85963, 2112500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (85945487, 676000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (79, 20)
  let e33 : LowMeanIntegerExpr := .pow (4656612873077392578125, 34059943367449284484947168626829637) e21 31
  let e34 : LowMeanIntegerExpr := .mul (73574483394622802734375, 136239773469797137939788674507318548) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-73574483394622802734375, 136239773469797137939788674507318548) e34
  let e36 : LowMeanIntegerExpr := .add (17321292425416654527613238599064408538451, 136239773469797137939788674507318548000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (17322654823151352498992636485809481723931, 136239773469797137939788674507318548000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-17321292425416654527613238599064408538451, 136239773469797137939788674507318548000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0468 : LowMeanDirectSeedInput :=
  { record := 468, positions := [{ j := 17, mode := 0, left := 976, right := 0 }, { j := 18, mode := 0, left := 977, right := 0 }, { j := 19, mode := 0, left := 978, right := 0 }, { j := 22, mode := 0, left := 979, right := 0 }, { j := 23, mode := 0, left := 980, right := 0 }, { j := 24, mode := 0, left := 981, right := 0 }, { j := 25, mode := 0, left := 982, right := 0 }], target := { R := 31, expr := lowMeanSeedTargetExpr0468 } }

noncomputable def lowMeanSeedTargetExpr0469 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (84077, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (129, 100000)
  let e3 : LowMeanIntegerExpr := .atom (32, 1)
  let e4 : LowMeanIntegerExpr := .atom (57, 2)
  let e5 : LowMeanIntegerExpr := .neg (-57, 2) e4
  let e6 : LowMeanIntegerExpr := .add (7, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (903, 200000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (5537, 62500) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (137, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (49, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (6713, 4000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-6713, 4000000) e11
  let e13 : LowMeanIntegerExpr := .add (69531, 800000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (2773, 500000)
  let e15 : LowMeanIntegerExpr := .atom (8, 13)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (19, 29)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-8, 13) e15
  let e21 : LowMeanIntegerExpr := .add (5, 13) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (40, 169) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-19, 29) e17
  let e24 : LowMeanIntegerExpr := .add (10, 29) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (190, 841) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (40, 169) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (40, 169) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2773, 2112500) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (22184, 528125) e29 e3
  let e31 : LowMeanIntegerExpr := .add (17429843, 135200000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (79, 20)
  let e33 : LowMeanIntegerExpr := .pow (23283064365386962890625, 442779263776840698304313192148785281) e21 32
  let e34 : LowMeanIntegerExpr := .mul (367872416973114013671875, 1771117055107362793217252768595141124) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-367872416973114013671875, 1771117055107362793217252768595141124) e34
  let e36 : LowMeanIntegerExpr := .add (45666112729428913134679608924970714281307, 354223411021472558643450553719028224800000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (9133930992707825572053208686101580912711, 70844682204294511728690110743805644960000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-45666112729428913134679608924970714281307, 354223411021472558643450553719028224800000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0469 : LowMeanDirectSeedInput :=
  { record := 469, positions := [{ j := 18, mode := 0, left := 983, right := 0 }, { j := 19, mode := 0, left := 984, right := 0 }, { j := 22, mode := 0, left := 985, right := 0 }, { j := 23, mode := 0, left := 986, right := 0 }, { j := 24, mode := 0, left := 987, right := 0 }, { j := 25, mode := 0, left := 988, right := 0 }, { j := 26, mode := 0, left := 989, right := 0 }], target := { R := 32, expr := lowMeanSeedTargetExpr0469 } }

noncomputable def lowMeanSeedTargetExpr0470 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (84077, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (129, 100000)
  let e3 : LowMeanIntegerExpr := .atom (33, 1)
  let e4 : LowMeanIntegerExpr := .atom (57, 2)
  let e5 : LowMeanIntegerExpr := .neg (-57, 2) e4
  let e6 : LowMeanIntegerExpr := .add (9, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (1161, 200000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (44941, 500000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (137, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (81, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (11097, 4000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-11097, 4000000) e11
  let e13 : LowMeanIntegerExpr := .add (348431, 4000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (2773, 500000)
  let e15 : LowMeanIntegerExpr := .atom (8, 13)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (19, 29)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-8, 13) e15
  let e21 : LowMeanIntegerExpr := .add (5, 13) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (40, 169) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-19, 29) e17
  let e24 : LowMeanIntegerExpr := .add (10, 29) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (190, 841) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (40, 169) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (40, 169) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2773, 2112500) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (91509, 2112500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (88167719, 676000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (79, 20)
  let e33 : LowMeanIntegerExpr := .pow (116415321826934814453125, 5756130429098929077956071497934208653) e21 33
  let e34 : LowMeanIntegerExpr := .mul (1839362084865570068359375, 23024521716395716311824285991736834612) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1839362084865570068359375, 23024521716395716311824285991736834612) e34
  let e36 : LowMeanIntegerExpr := .add (3002987515975342899135016123267571920888003, 23024521716395716311824285991736834612000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (3003217761192506856298134366127489289234123, 23024521716395716311824285991736834612000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-3002987515975342899135016123267571920888003, 23024521716395716311824285991736834612000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0470 : LowMeanDirectSeedInput :=
  { record := 470, positions := [{ j := 18, mode := 0, left := 990, right := 0 }, { j := 19, mode := 0, left := 991, right := 0 }, { j := 20, mode := 0, left := 992, right := 0 }, { j := 23, mode := 0, left := 993, right := 0 }, { j := 24, mode := 0, left := 994, right := 0 }, { j := 25, mode := 0, left := 995, right := 0 }, { j := 26, mode := 0, left := 996, right := 0 }], target := { R := 33, expr := lowMeanSeedTargetExpr0470 } }

noncomputable def lowMeanSeedTargetExpr0471 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (84077, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (129, 100000)
  let e3 : LowMeanIntegerExpr := .atom (34, 1)
  let e4 : LowMeanIntegerExpr := .atom (57, 2)
  let e5 : LowMeanIntegerExpr := .neg (-57, 2) e4
  let e6 : LowMeanIntegerExpr := .add (11, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (1419, 200000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (22793, 250000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (137, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (121, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (16577, 4000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-16577, 4000000) e11
  let e13 : LowMeanIntegerExpr := .add (348111, 4000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (2773, 500000)
  let e15 : LowMeanIntegerExpr := .atom (8, 13)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (19, 29)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-8, 13) e15
  let e21 : LowMeanIntegerExpr := .add (5, 13) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (40, 169) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-19, 29) e17
  let e24 : LowMeanIntegerExpr := .add (10, 29) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (190, 841) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (40, 169) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (40, 169) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2773, 2112500) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (47141, 1056250) e29 e3
  let e31 : LowMeanIntegerExpr := .add (89000999, 676000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (79, 20)
  let e33 : LowMeanIntegerExpr := .pow (582076609134674072265625, 74829695578286078013428929473144712489) e21 34
  let e34 : LowMeanIntegerExpr := .mul (9196810424327850341796875, 299318782313144312053715717892578849956) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-9196810424327850341796875, 299318782313144312053715717892578849956) e34
  let e36 : LowMeanIntegerExpr := .add (39407796812614138402517152259779049770495719, 299318782313144312053715717892578849956000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (39410790000437269845637689416957975558995279, 299318782313144312053715717892578849956000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-39407796812614138402517152259779049770495719, 299318782313144312053715717892578849956000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0471 : LowMeanDirectSeedInput :=
  { record := 471, positions := [{ j := 19, mode := 0, left := 997, right := 0 }, { j := 20, mode := 0, left := 998, right := 0 }, { j := 21, mode := 0, left := 999, right := 0 }, { j := 23, mode := 0, left := 1000, right := 0 }, { j := 24, mode := 0, left := 1001, right := 0 }, { j := 25, mode := 0, left := 1002, right := 0 }, { j := 26, mode := 0, left := 1003, right := 0 }, { j := 27, mode := 0, left := 1004, right := 0 }], target := { R := 34, expr := lowMeanSeedTargetExpr0471 } }

noncomputable def lowMeanSeedTargetExpr0472 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (84077, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (129, 100000)
  let e3 : LowMeanIntegerExpr := .atom (35, 1)
  let e4 : LowMeanIntegerExpr := .atom (57, 2)
  let e5 : LowMeanIntegerExpr := .neg (-57, 2) e4
  let e6 : LowMeanIntegerExpr := .add (13, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (1677, 200000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (46231, 500000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (137, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (169, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (23153, 4000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-23153, 4000000) e11
  let e13 : LowMeanIntegerExpr := .add (69339, 800000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (2773, 500000)
  let e15 : LowMeanIntegerExpr := .atom (8, 13)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (19, 29)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-8, 13) e15
  let e21 : LowMeanIntegerExpr := .add (5, 13) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (40, 169) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-19, 29) e17
  let e24 : LowMeanIntegerExpr := .add (10, 29) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (190, 841) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (40, 169) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (40, 169) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2773, 2112500) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (19411, 422500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (17929811, 135200000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (79, 20)
  let e33 : LowMeanIntegerExpr := .pow (2910383045673370361328125, 972786042517719014174576083150881262357) e21 35
  let e34 : LowMeanIntegerExpr := .mul (45984052121639251708984375, 3891144170070876056698304332603525049428) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-45984052121639251708984375, 3891144170070876056698304332603525049428) e34
  let e36 : LowMeanIntegerExpr := .add (103206330685083501859732300410105454707854583, 778228834014175211339660866520705009885600000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (103214112973423643611845697018770661757953439, 778228834014175211339660866520705009885600000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-103206330685083501859732300410105454707854583, 778228834014175211339660866520705009885600000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0472 : LowMeanDirectSeedInput :=
  { record := 472, positions := [{ j := 20, mode := 0, left := 1005, right := 0 }, { j := 21, mode := 0, left := 1006, right := 0 }, { j := 22, mode := 0, left := 1007, right := 0 }, { j := 24, mode := 0, left := 1008, right := 0 }, { j := 25, mode := 0, left := 1009, right := 0 }, { j := 26, mode := 0, left := 1010, right := 0 }, { j := 27, mode := 0, left := 1011, right := 0 }, { j := 28, mode := 0, left := 1012, right := 0 }], target := { R := 35, expr := lowMeanSeedTargetExpr0472 } }

noncomputable def lowMeanSeedTargetExpr0473 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (84077, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (129, 100000)
  let e3 : LowMeanIntegerExpr := .atom (36, 1)
  let e4 : LowMeanIntegerExpr := .atom (57, 2)
  let e5 : LowMeanIntegerExpr := .neg (-57, 2) e4
  let e6 : LowMeanIntegerExpr := .add (15, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (387, 40000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (11719, 125000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (137, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (225, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1233, 160000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1233, 160000) e11
  let e13 : LowMeanIntegerExpr := .add (344183, 4000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (2773, 500000)
  let e15 : LowMeanIntegerExpr := .atom (8, 13)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (19, 29)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-8, 13) e15
  let e21 : LowMeanIntegerExpr := .add (5, 13) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (40, 169) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-19, 29) e17
  let e24 : LowMeanIntegerExpr := .add (10, 29) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (190, 841) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (40, 169) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (40, 169) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2773, 2112500) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (24957, 528125) e29 e3
  let e31 : LowMeanIntegerExpr := .add (90111887, 676000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (79, 20)
  let e33 : LowMeanIntegerExpr := .pow (14551915228366851806640625, 12646218552730347184269489080961456410641) e21 36
  let e34 : LowMeanIntegerExpr := .mul (229920260608196258544921875, 50584874210921388737077956323845825642564) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-229920260608196258544921875, 50584874210921388737077956323845825642564) e34
  let e36 : LowMeanIntegerExpr := .add (6743045072194684795358683978956440944581256743, 50584874210921388737077956323845825642564000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (6743550920936794009246054758519679402837682383, 50584874210921388737077956323845825642564000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-6743045072194684795358683978956440944581256743, 50584874210921388737077956323845825642564000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0473 : LowMeanDirectSeedInput :=
  { record := 473, positions := [{ j := 20, mode := 0, left := 1013, right := 0 }, { j := 21, mode := 0, left := 1014, right := 0 }, { j := 22, mode := 0, left := 1015, right := 0 }, { j := 25, mode := 0, left := 1016, right := 0 }, { j := 26, mode := 0, left := 1017, right := 0 }, { j := 27, mode := 0, left := 1018, right := 0 }, { j := 28, mode := 0, left := 1019, right := 0 }], target := { R := 36, expr := lowMeanSeedTargetExpr0473 } }

noncomputable def lowMeanSeedTargetExpr0474 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (84077, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (129, 100000)
  let e3 : LowMeanIntegerExpr := .atom (38, 1)
  let e4 : LowMeanIntegerExpr := .atom (57, 2)
  let e5 : LowMeanIntegerExpr := .neg (-57, 2) e4
  let e6 : LowMeanIntegerExpr := .add (19, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (2451, 200000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (24083, 250000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (137, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (361, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (49457, 4000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-49457, 4000000) e11
  let e13 : LowMeanIntegerExpr := .add (335871, 4000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (2773, 500000)
  let e15 : LowMeanIntegerExpr := .atom (8, 13)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (19, 29)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-8, 13) e15
  let e21 : LowMeanIntegerExpr := .add (5, 13) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (40, 169) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-19, 29) e17
  let e24 : LowMeanIntegerExpr := .add (10, 29) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (190, 841) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (40, 169) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (40, 169) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2773, 2112500) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (52687, 1056250) e29 e3
  let e31 : LowMeanIntegerExpr := .add (90481879, 676000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (79, 20)
  let e33 : LowMeanIntegerExpr := .pow (363797880709171295166015625, 2137210935411428674141543654682486133398329) e21 38
  let e34 : LowMeanIntegerExpr := .mul (5748006515204906463623046875, 8548843741645714696566174618729944533593316) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-5748006515204906463623046875, 8548843741645714696566174618729944533593316) e34
  let e36 : LowMeanIntegerExpr := .add (1144253616895696645548547409508912079564518274439, 8548843741645714696566174618729944533593316000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (1144339105333113102695513071255099379009854207599, 8548843741645714696566174618729944533593316000000) e0 e36
  let e38 : LowMeanIntegerExpr := .atom (37, 1)
  let e39 : LowMeanIntegerExpr := .add (17, 2) e38 e5
  let e40 : LowMeanIntegerExpr := .mul (2193, 200000) e2 e39
  let e41 : LowMeanIntegerExpr := .add (47521, 500000) e1 e40
  let e42 : LowMeanIntegerExpr := .pow (289, 4) e39 2
  let e43 : LowMeanIntegerExpr := .mul (39593, 4000000) e9 e42
  let e44 : LowMeanIntegerExpr := .neg (-39593, 4000000) e43
  let e45 : LowMeanIntegerExpr := .add (13623, 160000) e41 e44
  let e46 : LowMeanIntegerExpr := .mul (102601, 2112500) e29 e38
  let e47 : LowMeanIntegerExpr := .add (18077899, 135200000) e45 e46
  let e48 : LowMeanIntegerExpr := .pow (72759576141834259033203125, 164400841185494513395503358052498933338333) e21 37
  let e49 : LowMeanIntegerExpr := .mul (1149601303040981292724609375, 657603364741978053582013432209995733353332) e32 e48
  let e50 : LowMeanIntegerExpr := .neg (-1149601303040981292724609375, 657603364741978053582013432209995733353332) e49
  let e51 : LowMeanIntegerExpr := .add (17585927825244800128366946602758688300007347943, 131520672948395610716402686441999146670666400000) e47 e50
  let e52 : LowMeanIntegerExpr := .neg (-17585927825244800128366946602758688300007347943, 131520672948395610716402686441999146670666400000) e51
  let e53 : LowMeanIntegerExpr := .add (156724586525136793957692759473079938672073913, 1068605467705714337070771827341243066699164500000) e37 e52
  e53

noncomputable def lowMeanSeedRecord0474 : LowMeanDirectSeedInput :=
  { record := 474, positions := [{ j := 21, mode := 0, left := 1020, right := 0 }, { j := 22, mode := 0, left := 1021, right := 0 }, { j := 23, mode := 0, left := 1022, right := 0 }, { j := 25, mode := 0, left := 1023, right := 0 }, { j := 26, mode := 0, left := 1024, right := 0 }, { j := 27, mode := 0, left := 1025, right := 0 }, { j := 28, mode := 0, left := 1026, right := 0 }, { j := 29, mode := 0, left := 1027, right := 0 }], target := { R := 38, expr := lowMeanSeedTargetExpr0474 } }

noncomputable def lowMeanSeedTargetExpr0475 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e2 : LowMeanIntegerExpr := .atom (26, 78125)
  let e3 : LowMeanIntegerExpr := .atom (0, 1)
  let e4 : LowMeanIntegerExpr := .atom (189, 4)
  let e5 : LowMeanIntegerExpr := .neg (-189, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-189, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-2457, 156250) e2 e6
  let e8 : LowMeanIntegerExpr := .add (-58111, 10000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e10 : LowMeanIntegerExpr := .pow (35721, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (46187253, 1600000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-46187253, 1600000000) e11
  let e13 : LowMeanIntegerExpr := .add (-55485013, 1600000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (2063, 10000000)
  let e15 : LowMeanIntegerExpr := .atom (8, 13)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (19, 29)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-8, 13) e15
  let e21 : LowMeanIntegerExpr := .add (5, 13) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (40, 169) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-19, 29) e17
  let e24 : LowMeanIntegerExpr := .add (10, 29) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (190, 841) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (40, 169) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (40, 169) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2063, 42250000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (0, 1) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-55485013, 1600000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (328000, 1)
  let e33 : LowMeanIntegerExpr := .pow (1, 1) e21 0
  let e34 : LowMeanIntegerExpr := .mul (328000, 1) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-328000, 1) e34
  let e36 : LowMeanIntegerExpr := .add (-524800055485013, 1600000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-524800055469013, 1600000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (524800055485013, 1600000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0475 : LowMeanDirectSeedInput :=
  { record := 475, positions := [], target := { R := 0, expr := lowMeanSeedTargetExpr0475 } }

noncomputable def lowMeanSeedTargetExpr0476 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e2 : LowMeanIntegerExpr := .atom (26, 78125)
  let e3 : LowMeanIntegerExpr := .atom (1, 1)
  let e4 : LowMeanIntegerExpr := .atom (189, 4)
  let e5 : LowMeanIntegerExpr := .neg (-189, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-185, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-481, 31250) e2 e6
  let e8 : LowMeanIntegerExpr := .add (-54783, 10000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e10 : LowMeanIntegerExpr := .pow (34225, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1770117, 64000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1770117, 64000000) e11
  let e13 : LowMeanIntegerExpr := .add (-10603641, 320000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (2063, 10000000)
  let e15 : LowMeanIntegerExpr := .atom (8, 13)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (19, 29)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .neg (-8, 13) e15
  let e20 : LowMeanIntegerExpr := .add (5, 13) e3 e19
  let e21 : LowMeanIntegerExpr := .mul (40, 169) e15 e20
  let e22 : LowMeanIntegerExpr := .neg (-19, 29) e17
  let e23 : LowMeanIntegerExpr := .add (10, 29) e3 e22
  let e24 : LowMeanIntegerExpr := .mul (190, 841) e17 e23
  let e25 : LowMeanIntegerExpr := .maximum (40, 169) e21 e24
  let e26 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e25
  let e27 : LowMeanIntegerExpr := .selectLE (40, 169) e15 e16 e26 e25
  let e28 : LowMeanIntegerExpr := .mul (2063, 42250000) e14 e27
  let e29 : LowMeanIntegerExpr := .mul (2063, 42250000) e28 e3
  let e30 : LowMeanIntegerExpr := .add (-1789374689, 54080000000) e13 e29
  let e31 : LowMeanIntegerExpr := .atom (328000, 1)
  let e32 : LowMeanIntegerExpr := .pow (5, 13) e20 1
  let e33 : LowMeanIntegerExpr := .mul (1640000, 13) e31 e32
  let e34 : LowMeanIntegerExpr := .neg (-1640000, 13) e33
  let e35 : LowMeanIntegerExpr := .add (-6822401789374689, 54080000000) e30 e34
  let e36 : LowMeanIntegerExpr := .add (-6822401788833889, 54080000000) e0 e35
  let e37 : LowMeanIntegerExpr := .neg (6822401789374689, 54080000000) e35
  let e38 : LowMeanIntegerExpr := .add (1, 100000) e36 e37
  e38

noncomputable def lowMeanSeedRecord0476 : LowMeanDirectSeedInput :=
  { record := 476, positions := [], target := { R := 1, expr := lowMeanSeedTargetExpr0476 } }

noncomputable def lowMeanSeedTargetExpr0477 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e2 : LowMeanIntegerExpr := .atom (26, 78125)
  let e3 : LowMeanIntegerExpr := .atom (2, 1)
  let e4 : LowMeanIntegerExpr := .atom (189, 4)
  let e5 : LowMeanIntegerExpr := .neg (-189, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-181, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-2353, 156250) e2 e6
  let e8 : LowMeanIntegerExpr := .add (-10291, 2000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e10 : LowMeanIntegerExpr := .pow (32761, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (42359973, 1600000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-42359973, 1600000000) e11
  let e13 : LowMeanIntegerExpr := .add (-50592773, 1600000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (2063, 10000000)
  let e15 : LowMeanIntegerExpr := .atom (8, 13)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (19, 29)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-8, 13) e15
  let e21 : LowMeanIntegerExpr := .add (5, 13) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (40, 169) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-19, 29) e17
  let e24 : LowMeanIntegerExpr := .add (10, 29) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (190, 841) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (40, 169) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (40, 169) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2063, 42250000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (2063, 21125000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-8523772237, 270400000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (328000, 1)
  let e33 : LowMeanIntegerExpr := .pow (25, 169) e21 2
  let e34 : LowMeanIntegerExpr := .mul (8200000, 169) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-8200000, 169) e34
  let e36 : LowMeanIntegerExpr := .add (-13120008523772237, 270400000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-13120008521068237, 270400000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (13120008523772237, 270400000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0477 : LowMeanDirectSeedInput :=
  { record := 477, positions := [], target := { R := 2, expr := lowMeanSeedTargetExpr0477 } }

noncomputable def lowMeanSeedTargetExpr0478 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e2 : LowMeanIntegerExpr := .atom (26, 78125)
  let e3 : LowMeanIntegerExpr := .atom (3, 1)
  let e4 : LowMeanIntegerExpr := .atom (189, 4)
  let e5 : LowMeanIntegerExpr := .neg (-189, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-177, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-2301, 156250) e2 e6
  let e8 : LowMeanIntegerExpr := .add (-48127, 10000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e10 : LowMeanIntegerExpr := .pow (31329, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (40508397, 1600000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-40508397, 1600000000) e11
  let e13 : LowMeanIntegerExpr := .add (-48208717, 1600000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (2063, 10000000)
  let e15 : LowMeanIntegerExpr := .atom (8, 13)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (19, 29)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-8, 13) e15
  let e21 : LowMeanIntegerExpr := .add (5, 13) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (40, 169) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-19, 29) e17
  let e24 : LowMeanIntegerExpr := .add (10, 29) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (190, 841) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (40, 169) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (40, 169) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2063, 42250000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (6189, 42250000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-8107663573, 270400000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (328000, 1)
  let e33 : LowMeanIntegerExpr := .pow (125, 2197) e21 3
  let e34 : LowMeanIntegerExpr := .mul (41000000, 2197) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-41000000, 2197) e34
  let e36 : LowMeanIntegerExpr := .add (-65600105399626449, 3515200000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-65600105364474449, 3515200000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (65600105399626449, 3515200000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0478 : LowMeanDirectSeedInput :=
  { record := 478, positions := [], target := { R := 3, expr := lowMeanSeedTargetExpr0478 } }

noncomputable def lowMeanSeedTargetExpr0479 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e2 : LowMeanIntegerExpr := .atom (26, 78125)
  let e3 : LowMeanIntegerExpr := .atom (4, 1)
  let e4 : LowMeanIntegerExpr := .atom (189, 4)
  let e5 : LowMeanIntegerExpr := .neg (-189, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-173, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-2249, 156250) e2 e6
  let e8 : LowMeanIntegerExpr := .add (-44799, 10000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e10 : LowMeanIntegerExpr := .pow (29929, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (38698197, 1600000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-38698197, 1600000000) e11
  let e13 : LowMeanIntegerExpr := .add (-45866037, 1600000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (2063, 10000000)
  let e15 : LowMeanIntegerExpr := .atom (8, 13)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (19, 29)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-8, 13) e15
  let e21 : LowMeanIntegerExpr := .add (5, 13) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (40, 169) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-19, 29) e17
  let e24 : LowMeanIntegerExpr := .add (10, 29) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (190, 841) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (40, 169) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (40, 169) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2063, 42250000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (2063, 10562500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-7698547453, 270400000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (328000, 1)
  let e33 : LowMeanIntegerExpr := .pow (625, 28561) e21 4
  let e34 : LowMeanIntegerExpr := .mul (205000000, 28561) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-205000000, 28561) e34
  let e36 : LowMeanIntegerExpr := .add (-328001301054519557, 45697600000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-328001300597543557, 45697600000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (328001301054519557, 45697600000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0479 : LowMeanDirectSeedInput :=
  { record := 479, positions := [], target := { R := 4, expr := lowMeanSeedTargetExpr0479 } }

noncomputable def lowMeanSeedGroup0464 : List LowMeanDirectSeedInput := [lowMeanSeedRecord0464, lowMeanSeedRecord0465, lowMeanSeedRecord0466, lowMeanSeedRecord0467, lowMeanSeedRecord0468, lowMeanSeedRecord0469, lowMeanSeedRecord0470, lowMeanSeedRecord0471, lowMeanSeedRecord0472, lowMeanSeedRecord0473, lowMeanSeedRecord0474, lowMeanSeedRecord0475, lowMeanSeedRecord0476, lowMeanSeedRecord0477, lowMeanSeedRecord0478, lowMeanSeedRecord0479]

end Erdos993Lean.Analytic.V213
