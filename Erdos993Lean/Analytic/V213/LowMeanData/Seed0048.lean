module

public import Erdos993Lean.Analytic.V213.LowMeanCoreAll
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0563
public import Erdos993Lean.Analytic.V213.LowMeanFiberSeed
public import Erdos993Lean.Analytic.V213.LowMeanIntegerExpr
public import Erdos993Lean.Analytic.V213.LowMeanSeedGeometry
public import Erdos993Lean.Analytic.V213.LowMeanWidthData
public import Erdos993Lean.Ceiling.Prefix
public import Erdos993Lean.Ceiling.Statement

/-! Exact core/budget keys and equation-51 targets for the direct fibers. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanSeedTargetExpr0048 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (9, 25)
  let e2 : LowMeanIntegerExpr := .atom (1837, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (13, 1)
  let e4 : LowMeanIntegerExpr := .atom (15, 1)
  let e5 : LowMeanIntegerExpr := .neg (-15, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-2, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1837, 500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (178163, 500000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (691, 500000)
  let e10 : LowMeanIntegerExpr := .pow (4, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (691, 125000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-691, 125000) e11
  let e13 : LowMeanIntegerExpr := .add (175399, 500000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (973, 12500)
  let e15 : LowMeanIntegerExpr := .atom (3, 8)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (39, 89)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-3, 8) e15
  let e21 : LowMeanIntegerExpr := .add (5, 8) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (15, 64) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-39, 89) e17
  let e24 : LowMeanIntegerExpr := .add (50, 89) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (1950, 7921) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (1950, 7921) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1950, 7921) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1950, 7921) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (37947, 1980250) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (493311, 1980250) e29 e3
  let e31 : LowMeanIntegerExpr := .add (2375957479, 3960500000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (567, 100)
  let e33 : LowMeanIntegerExpr := .pow (1220703125, 549755813888) e21 13
  let e34 : LowMeanIntegerExpr := .mul (27685546875, 2199023255552) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-27685546875, 2199023255552) e34
  let e36 : LowMeanIntegerExpr := .add (159848035691414536669, 272163487612928000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (159850757326290665949, 272163487612928000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-159848035691414536669, 272163487612928000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0048 : LowMeanDirectSeedInput :=
  { record := 48, positions := [{ j := 2, mode := 0, left := 279, right := 0 }, { j := 3, mode := 0, left := 280, right := 0 }], target := { R := 13, expr := lowMeanSeedTargetExpr0048 } }

noncomputable def lowMeanSeedTargetExpr0049 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (9, 25)
  let e2 : LowMeanIntegerExpr := .atom (1837, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (14, 1)
  let e4 : LowMeanIntegerExpr := .atom (15, 1)
  let e5 : LowMeanIntegerExpr := .neg (-15, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-1, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1837, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (358163, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (691, 500000)
  let e10 : LowMeanIntegerExpr := .pow (1, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (691, 500000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-691, 500000) e11
  let e13 : LowMeanIntegerExpr := .add (356781, 1000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (973, 12500)
  let e15 : LowMeanIntegerExpr := .atom (3, 8)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (39, 89)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-3, 8) e15
  let e21 : LowMeanIntegerExpr := .add (5, 8) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (15, 64) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-39, 89) e17
  let e24 : LowMeanIntegerExpr := .add (50, 89) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (1950, 7921) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (1950, 7921) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1950, 7921) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1950, 7921) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (37947, 1980250) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (265629, 990125) e29 e3
  let e31 : LowMeanIntegerExpr := .add (4951094301, 7921000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (567, 100)
  let e33 : LowMeanIntegerExpr := .pow (6103515625, 4398046511104) e21 14
  let e34 : LowMeanIntegerExpr := .mul (138427734375, 17592186044416) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-138427734375, 17592186044416) e34
  let e36 : LowMeanIntegerExpr := .add (1343813843478990866769, 2177307900903424000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (1343835616557999901009, 2177307900903424000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-1343813843478990866769, 2177307900903424000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0049 : LowMeanDirectSeedInput :=
  { record := 49, positions := [{ j := 2, mode := 0, left := 281, right := 0 }, { j := 3, mode := 0, left := 282, right := 0 }, { j := 4, mode := 0, left := 283, right := 0 }], target := { R := 14, expr := lowMeanSeedTargetExpr0049 } }

noncomputable def lowMeanSeedTargetExpr0050 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (9, 25)
  let e2 : LowMeanIntegerExpr := .atom (1837, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (15, 1)
  let e4 : LowMeanIntegerExpr := .neg (-15, 1) e3
  let e5 : LowMeanIntegerExpr := .add (0, 1) e3 e4
  let e6 : LowMeanIntegerExpr := .mul (0, 1) e2 e5
  let e7 : LowMeanIntegerExpr := .add (9, 25) e1 e6
  let e8 : LowMeanIntegerExpr := .atom (691, 500000)
  let e9 : LowMeanIntegerExpr := .pow (0, 1) e5 2
  let e10 : LowMeanIntegerExpr := .mul (0, 1) e8 e9
  let e11 : LowMeanIntegerExpr := .neg (0, 1) e10
  let e12 : LowMeanIntegerExpr := .add (9, 25) e7 e11
  let e13 : LowMeanIntegerExpr := .atom (973, 12500)
  let e14 : LowMeanIntegerExpr := .atom (3, 8)
  let e15 : LowMeanIntegerExpr := .atom (1, 2)
  let e16 : LowMeanIntegerExpr := .atom (39, 89)
  let e17 : LowMeanIntegerExpr := .atom (1, 4)
  let e18 : LowMeanIntegerExpr := .atom (1, 1)
  let e19 : LowMeanIntegerExpr := .neg (-3, 8) e14
  let e20 : LowMeanIntegerExpr := .add (5, 8) e18 e19
  let e21 : LowMeanIntegerExpr := .mul (15, 64) e14 e20
  let e22 : LowMeanIntegerExpr := .neg (-39, 89) e16
  let e23 : LowMeanIntegerExpr := .add (50, 89) e18 e22
  let e24 : LowMeanIntegerExpr := .mul (1950, 7921) e16 e23
  let e25 : LowMeanIntegerExpr := .maximum (1950, 7921) e21 e24
  let e26 : LowMeanIntegerExpr := .selectLE (1950, 7921) e15 e16 e17 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1950, 7921) e14 e15 e26 e25
  let e28 : LowMeanIntegerExpr := .mul (37947, 1980250) e13 e27
  let e29 : LowMeanIntegerExpr := .mul (113841, 396050) e28 e3
  let e30 : LowMeanIntegerExpr := .add (256419, 396050) e12 e29
  let e31 : LowMeanIntegerExpr := .atom (567, 100)
  let e32 : LowMeanIntegerExpr := .pow (30517578125, 35184372088832) e20 15
  let e33 : LowMeanIntegerExpr := .mul (692138671875, 140737488355328) e31 e32
  let e34 : LowMeanIntegerExpr := .neg (-692138671875, 140737488355328) e33
  let e35 : LowMeanIntegerExpr := .add (17906822252794378341, 27869541131563827200) e30 e34
  let e36 : LowMeanIntegerExpr := .add (2238387618525711747409, 3483692641445478400000) e0 e35
  let e37 : LowMeanIntegerExpr := .neg (-17906822252794378341, 27869541131563827200) e35
  let e38 : LowMeanIntegerExpr := .add (1, 100000) e36 e37
  e38

noncomputable def lowMeanSeedRecord0050 : LowMeanDirectSeedInput :=
  { record := 50, positions := [{ j := 2, mode := 0, left := 284, right := 0 }, { j := 3, mode := 0, left := 285, right := 0 }, { j := 4, mode := 0, left := 286, right := 0 }], target := { R := 15, expr := lowMeanSeedTargetExpr0050 } }

noncomputable def lowMeanSeedTargetExpr0051 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (9, 25)
  let e2 : LowMeanIntegerExpr := .atom (1837, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (16, 1)
  let e4 : LowMeanIntegerExpr := .atom (15, 1)
  let e5 : LowMeanIntegerExpr := .neg (-15, 1) e4
  let e6 : LowMeanIntegerExpr := .add (1, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (1837, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (361837, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (691, 500000)
  let e10 : LowMeanIntegerExpr := .pow (1, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (691, 500000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-691, 500000) e11
  let e13 : LowMeanIntegerExpr := .add (72091, 200000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (973, 12500)
  let e15 : LowMeanIntegerExpr := .atom (3, 8)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (39, 89)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-3, 8) e15
  let e21 : LowMeanIntegerExpr := .add (5, 8) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (15, 64) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-39, 89) e17
  let e24 : LowMeanIntegerExpr := .add (50, 89) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (1950, 7921) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (1950, 7921) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1950, 7921) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1950, 7921) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (37947, 1980250) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (303576, 990125) e29 e3
  let e31 : LowMeanIntegerExpr := .add (1056754411, 1584200000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (567, 100)
  let e33 : LowMeanIntegerExpr := .pow (152587890625, 281474976710656) e21 16
  let e34 : LowMeanIntegerExpr := .mul (3460693359375, 1125899906842624) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-3460693359375, 1125899906842624) e34
  let e36 : LowMeanIntegerExpr := .add (18504957226257970622101, 27869541131563827200000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (18505235921669286260373, 27869541131563827200000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-18504957226257970622101, 27869541131563827200000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0051 : LowMeanDirectSeedInput :=
  { record := 51, positions := [{ j := 3, mode := 0, left := 287, right := 0 }, { j := 4, mode := 0, left := 288, right := 0 }, { j := 5, mode := 0, left := 289, right := 0 }], target := { R := 16, expr := lowMeanSeedTargetExpr0051 } }

noncomputable def lowMeanSeedTargetExpr0052 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (9, 25)
  let e2 : LowMeanIntegerExpr := .atom (1837, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (17, 1)
  let e4 : LowMeanIntegerExpr := .atom (15, 1)
  let e5 : LowMeanIntegerExpr := .neg (-15, 1) e4
  let e6 : LowMeanIntegerExpr := .add (2, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (1837, 500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (181837, 500000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (691, 500000)
  let e10 : LowMeanIntegerExpr := .pow (4, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (691, 125000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-691, 125000) e11
  let e13 : LowMeanIntegerExpr := .add (179073, 500000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (973, 12500)
  let e15 : LowMeanIntegerExpr := .atom (3, 8)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (39, 89)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-3, 8) e15
  let e21 : LowMeanIntegerExpr := .add (5, 8) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (15, 64) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-39, 89) e17
  let e24 : LowMeanIntegerExpr := .add (50, 89) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (1950, 7921) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (1950, 7921) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1950, 7921) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1950, 7921) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (37947, 1980250) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (645099, 1980250) e29 e3
  let e31 : LowMeanIntegerExpr := .add (2708635233, 3960500000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (567, 100)
  let e33 : LowMeanIntegerExpr := .pow (762939453125, 2251799813685248) e21 17
  let e34 : LowMeanIntegerExpr := .mul (17303466796875, 9007199254740992) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-17303466796875, 9007199254740992) e34
  let e36 : LowMeanIntegerExpr := .add (760271464743555305720973, 1114781645262553088000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (760282612560007931251853, 1114781645262553088000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-760271464743555305720973, 1114781645262553088000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0052 : LowMeanDirectSeedInput :=
  { record := 52, positions := [{ j := 3, mode := 0, left := 290, right := 0 }, { j := 4, mode := 0, left := 291, right := 0 }, { j := 5, mode := 0, left := 292, right := 0 }, { j := 8, mode := 0, left := 293, right := 0 }], target := { R := 17, expr := lowMeanSeedTargetExpr0052 } }

noncomputable def lowMeanSeedTargetExpr0053 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (9, 25)
  let e2 : LowMeanIntegerExpr := .atom (1837, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (19, 1)
  let e4 : LowMeanIntegerExpr := .atom (15, 1)
  let e5 : LowMeanIntegerExpr := .neg (-15, 1) e4
  let e6 : LowMeanIntegerExpr := .add (4, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (1837, 250000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (91837, 250000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (691, 500000)
  let e10 : LowMeanIntegerExpr := .pow (16, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (691, 31250) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-691, 31250) e11
  let e13 : LowMeanIntegerExpr := .add (86309, 250000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (973, 12500)
  let e15 : LowMeanIntegerExpr := .atom (3, 8)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (39, 89)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-3, 8) e15
  let e21 : LowMeanIntegerExpr := .add (5, 8) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (15, 64) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-39, 89) e17
  let e24 : LowMeanIntegerExpr := .add (50, 89) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (1950, 7921) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (1950, 7921) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1950, 7921) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1950, 7921) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (37947, 1980250) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (720993, 1980250) e29 e3
  let e31 : LowMeanIntegerExpr := .add (1404646589, 1980250000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (567, 100)
  let e33 : LowMeanIntegerExpr := .pow (19073486328125, 144115188075855872) e21 19
  let e34 : LowMeanIntegerExpr := .mul (432586669921875, 576460752303423488) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-432586669921875, 576460752303423488) e34
  let e36 : LowMeanIntegerExpr := .add (50554187478891556404558277, 71346025296803397632000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (50554900939144524438534597, 71346025296803397632000000) e0 e36
  let e38 : LowMeanIntegerExpr := .atom (18, 1)
  let e39 : LowMeanIntegerExpr := .add (3, 1) e38 e5
  let e40 : LowMeanIntegerExpr := .mul (5511, 1000000) e2 e39
  let e41 : LowMeanIntegerExpr := .add (365511, 1000000) e1 e40
  let e42 : LowMeanIntegerExpr := .pow (9, 1) e39 2
  let e43 : LowMeanIntegerExpr := .mul (6219, 500000) e9 e42
  let e44 : LowMeanIntegerExpr := .neg (-6219, 500000) e43
  let e45 : LowMeanIntegerExpr := .add (353073, 1000000) e41 e44
  let e46 : LowMeanIntegerExpr := .mul (341523, 990125) e29 e38
  let e47 : LowMeanIntegerExpr := .add (5528875233, 7921000000) e45 e46
  let e48 : LowMeanIntegerExpr := .pow (3814697265625, 18014398509481984) e21 18
  let e49 : LowMeanIntegerExpr := .mul (86517333984375, 72057594037927936) e32 e48
  let e50 : LowMeanIntegerExpr := .neg (-86517333984375, 72057594037927936) e49
  let e51 : LowMeanIntegerExpr := .add (6214252237865281150222017, 8918253162100424704000000) e47 e50
  let e52 : LowMeanIntegerExpr := .neg (-6214252237865281150222017, 8918253162100424704000000) e51
  let e53 : LowMeanIntegerExpr := .add (840883036222275236758461, 71346025296803397632000000) e37 e52
  e53

noncomputable def lowMeanSeedRecord0053 : LowMeanDirectSeedInput :=
  { record := 53, positions := [{ j := 4, mode := 0, left := 294, right := 0 }, { j := 5, mode := 0, left := 295, right := 0 }, { j := 6, mode := 0, left := 296, right := 0 }, { j := 8, mode := 0, left := 297, right := 0 }], target := { R := 19, expr := lowMeanSeedTargetExpr0053 } }

noncomputable def lowMeanSeedTargetExpr0054 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (9, 25)
  let e2 : LowMeanIntegerExpr := .atom (1837, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (20, 1)
  let e4 : LowMeanIntegerExpr := .atom (15, 1)
  let e5 : LowMeanIntegerExpr := .neg (-15, 1) e4
  let e6 : LowMeanIntegerExpr := .add (5, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (1837, 200000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (73837, 200000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (691, 500000)
  let e10 : LowMeanIntegerExpr := .pow (25, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (691, 20000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-691, 20000) e11
  let e13 : LowMeanIntegerExpr := .add (66927, 200000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (973, 12500)
  let e15 : LowMeanIntegerExpr := .atom (3, 8)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (39, 89)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-3, 8) e15
  let e21 : LowMeanIntegerExpr := .add (5, 8) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (15, 64) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-39, 89) e17
  let e24 : LowMeanIntegerExpr := .add (50, 89) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (1950, 7921) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (1950, 7921) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1950, 7921) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1950, 7921) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (37947, 1980250) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (75894, 198025) e29 e3
  let e31 : LowMeanIntegerExpr := .add (1137280767, 1584200000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (567, 100)
  let e33 : LowMeanIntegerExpr := .pow (95367431640625, 1152921504606846976) e21 20
  let e34 : LowMeanIntegerExpr := .mul (2162933349609375, 4611686018427387904) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-2162933349609375, 4611686018427387904) e34
  let e36 : LowMeanIntegerExpr := .add (81896176456059760584260037, 114153640474885436211200000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (81897317992464509438622149, 114153640474885436211200000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-81896176456059760584260037, 114153640474885436211200000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0054 : LowMeanDirectSeedInput :=
  { record := 54, positions := [{ j := 5, mode := 0, left := 298, right := 0 }, { j := 6, mode := 0, left := 299, right := 0 }, { j := 7, mode := 0, left := 300, right := 0 }, { j := 9, mode := 0, left := 301, right := 0 }], target := { R := 20, expr := lowMeanSeedTargetExpr0054 } }

noncomputable def lowMeanSeedTargetExpr0055 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (9, 25)
  let e2 : LowMeanIntegerExpr := .atom (1837, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (21, 1)
  let e4 : LowMeanIntegerExpr := .atom (15, 1)
  let e5 : LowMeanIntegerExpr := .neg (-15, 1) e4
  let e6 : LowMeanIntegerExpr := .add (6, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (5511, 500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (185511, 500000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (691, 500000)
  let e10 : LowMeanIntegerExpr := .pow (36, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (6219, 125000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-6219, 125000) e11
  let e13 : LowMeanIntegerExpr := .add (32127, 100000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (973, 12500)
  let e15 : LowMeanIntegerExpr := .atom (3, 8)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (39, 89)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-3, 8) e15
  let e21 : LowMeanIntegerExpr := .add (5, 8) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (15, 64) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-39, 89) e17
  let e24 : LowMeanIntegerExpr := .add (50, 89) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (1950, 7921) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (1950, 7921) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1950, 7921) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1950, 7921) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (37947, 1980250) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (796887, 1980250) e29 e3
  let e31 : LowMeanIntegerExpr := .add (573232767, 792100000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (567, 100)
  let e33 : LowMeanIntegerExpr := .pow (476837158203125, 9223372036854775808) e21 21
  let e34 : LowMeanIntegerExpr := .mul (10814666748046875, 36893488147419103232) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-10814666748046875, 36893488147419103232) e34
  let e36 : LowMeanIntegerExpr := .add (660624687421738391395328217, 913229123799083489689600000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (660633819712976382230225113, 913229123799083489689600000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-660624687421738391395328217, 913229123799083489689600000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0055 : LowMeanDirectSeedInput :=
  { record := 55, positions := [{ j := 5, mode := 0, left := 302, right := 0 }, { j := 6, mode := 0, left := 303, right := 0 }, { j := 7, mode := 0, left := 304, right := 0 }, { j := 9, mode := 0, left := 305, right := 0 }], target := { R := 21, expr := lowMeanSeedTargetExpr0055 } }

noncomputable def lowMeanSeedTargetExpr0056 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (9, 25)
  let e2 : LowMeanIntegerExpr := .atom (1837, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (23, 1)
  let e4 : LowMeanIntegerExpr := .atom (15, 1)
  let e5 : LowMeanIntegerExpr := .neg (-15, 1) e4
  let e6 : LowMeanIntegerExpr := .add (8, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (1837, 125000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (46837, 125000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (691, 500000)
  let e10 : LowMeanIntegerExpr := .pow (64, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1382, 15625) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1382, 15625) e11
  let e13 : LowMeanIntegerExpr := .add (35781, 125000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (973, 12500)
  let e15 : LowMeanIntegerExpr := .atom (3, 8)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (39, 89)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-3, 8) e15
  let e21 : LowMeanIntegerExpr := .add (5, 8) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (15, 64) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-39, 89) e17
  let e24 : LowMeanIntegerExpr := .add (50, 89) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (1950, 7921) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (1950, 7921) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1950, 7921) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1950, 7921) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (37947, 1980250) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (872781, 1980250) e29 e3
  let e31 : LowMeanIntegerExpr := .add (719811801, 990125000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (567, 100)
  let e33 : LowMeanIntegerExpr := .pow (11920928955078125, 590295810358705651712) e21 23
  let e34 : LowMeanIntegerExpr := .mul (270366668701171875, 2361183241434822606848) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-270366668701171875, 2361183241434822606848) e34
  let e36 : LowMeanIntegerExpr := .add (212417483088796217118504929781, 292233319615706716700672000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (212420405421992374185671936501, 292233319615706716700672000000) e0 e36
  let e38 : LowMeanIntegerExpr := .atom (22, 1)
  let e39 : LowMeanIntegerExpr := .add (7, 1) e38 e5
  let e40 : LowMeanIntegerExpr := .mul (12859, 1000000) e2 e39
  let e41 : LowMeanIntegerExpr := .add (372859, 1000000) e1 e40
  let e42 : LowMeanIntegerExpr := .pow (49, 1) e39 2
  let e43 : LowMeanIntegerExpr := .mul (33859, 500000) e9 e42
  let e44 : LowMeanIntegerExpr := .neg (-33859, 500000) e43
  let e45 : LowMeanIntegerExpr := .add (305141, 1000000) e41 e44
  let e46 : LowMeanIntegerExpr := .mul (417417, 990125) e29 e38
  let e47 : LowMeanIntegerExpr := .add (5756357861, 7921000000) e45 e46
  let e48 : LowMeanIntegerExpr := .pow (2384185791015625, 73786976294838206464) e21 22
  let e49 : LowMeanIntegerExpr := .mul (54073333740234375, 295147905179352825856) e32 e48
  let e50 : LowMeanIntegerExpr := .neg (-54073333740234375, 295147905179352825856) e49
  let e51 : LowMeanIntegerExpr := .add (26539822644692091523818353969, 36529164951963339587584000000) e47 e50
  let e52 : LowMeanIntegerExpr := .neg (-26539822644692091523818353969, 36529164951963339587584000000) e51
  let e53 : LowMeanIntegerExpr := .add (101824264455641995125104749, 292233319615706716700672000000) e37 e52
  e53

noncomputable def lowMeanSeedRecord0056 : LowMeanDirectSeedInput :=
  { record := 56, positions := [{ j := 5, mode := 0, left := 306, right := 0 }, { j := 6, mode := 0, left := 307, right := 0 }, { j := 7, mode := 0, left := 308, right := 0 }, { j := 8, mode := 0, left := 309, right := 0 }, { j := 10, mode := 0, left := 310, right := 0 }], target := { R := 23, expr := lowMeanSeedTargetExpr0056 } }

noncomputable def lowMeanSeedTargetExpr0057 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (14303, 100000)
  let e2 : LowMeanIntegerExpr := .atom (149, 20000)
  let e3 : LowMeanIntegerExpr := .atom (0, 1)
  let e4 : LowMeanIntegerExpr := .atom (22, 1)
  let e5 : LowMeanIntegerExpr := .neg (-22, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-22, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1639, 10000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (-2087, 100000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1641, 2000000)
  let e10 : LowMeanIntegerExpr := .pow (484, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (198561, 500000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-198561, 500000) e11
  let e13 : LowMeanIntegerExpr := .add (-52249, 125000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (781, 50000)
  let e15 : LowMeanIntegerExpr := .atom (3, 8)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (39, 89)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-3, 8) e15
  let e21 : LowMeanIntegerExpr := .add (5, 8) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (15, 64) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-39, 89) e17
  let e24 : LowMeanIntegerExpr := .add (50, 89) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (1950, 7921) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (1950, 7921) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1950, 7921) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1950, 7921) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (30459, 7921000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (0, 1) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-52249, 125000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1181, 125)
  let e33 : LowMeanIntegerExpr := .pow (1, 1) e21 0
  let e34 : LowMeanIntegerExpr := .mul (1181, 125) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1181, 125) e34
  let e36 : LowMeanIntegerExpr := .add (-1233249, 125000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-4932991, 500000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (1233249, 125000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0057 : LowMeanDirectSeedInput :=
  { record := 57, positions := [], target := { R := 0, expr := lowMeanSeedTargetExpr0057 } }

noncomputable def lowMeanSeedTargetExpr0058 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (14303, 100000)
  let e2 : LowMeanIntegerExpr := .atom (149, 20000)
  let e3 : LowMeanIntegerExpr := .atom (1, 1)
  let e4 : LowMeanIntegerExpr := .atom (22, 1)
  let e5 : LowMeanIntegerExpr := .neg (-22, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-21, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-3129, 20000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (-671, 50000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1641, 2000000)
  let e10 : LowMeanIntegerExpr := .pow (441, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (723681, 2000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-723681, 2000000) e11
  let e13 : LowMeanIntegerExpr := .add (-750521, 2000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (781, 50000)
  let e15 : LowMeanIntegerExpr := .atom (3, 8)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (39, 89)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .neg (-3, 8) e15
  let e20 : LowMeanIntegerExpr := .add (5, 8) e3 e19
  let e21 : LowMeanIntegerExpr := .mul (15, 64) e15 e20
  let e22 : LowMeanIntegerExpr := .neg (-39, 89) e17
  let e23 : LowMeanIntegerExpr := .add (50, 89) e3 e22
  let e24 : LowMeanIntegerExpr := .mul (1950, 7921) e17 e23
  let e25 : LowMeanIntegerExpr := .maximum (1950, 7921) e21 e24
  let e26 : LowMeanIntegerExpr := .selectLE (1950, 7921) e16 e17 e18 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1950, 7921) e15 e16 e26 e25
  let e28 : LowMeanIntegerExpr := .mul (30459, 7921000) e14 e27
  let e29 : LowMeanIntegerExpr := .mul (30459, 7921000) e28 e3
  let e30 : LowMeanIntegerExpr := .add (-5883958841, 15842000000) e13 e29
  let e31 : LowMeanIntegerExpr := .atom (1181, 125)
  let e32 : LowMeanIntegerExpr := .pow (5, 8) e20 1
  let e33 : LowMeanIntegerExpr := .mul (1181, 200) e31 e32
  let e34 : LowMeanIntegerExpr := .neg (-1181, 200) e33
  let e35 : LowMeanIntegerExpr := .add (-99430968841, 15842000000) e30 e34
  let e36 : LowMeanIntegerExpr := .add (-99430810421, 15842000000) e0 e35
  let e37 : LowMeanIntegerExpr := .neg (99430968841, 15842000000) e35
  let e38 : LowMeanIntegerExpr := .add (1, 100000) e36 e37
  e38

noncomputable def lowMeanSeedRecord0058 : LowMeanDirectSeedInput :=
  { record := 58, positions := [], target := { R := 1, expr := lowMeanSeedTargetExpr0058 } }

noncomputable def lowMeanSeedTargetExpr0059 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (14303, 100000)
  let e2 : LowMeanIntegerExpr := .atom (149, 20000)
  let e3 : LowMeanIntegerExpr := .atom (2, 1)
  let e4 : LowMeanIntegerExpr := .atom (22, 1)
  let e5 : LowMeanIntegerExpr := .neg (-22, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-20, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-149, 1000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (-597, 100000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1641, 2000000)
  let e10 : LowMeanIntegerExpr := .pow (400, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1641, 5000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1641, 5000) e11
  let e13 : LowMeanIntegerExpr := .add (-33417, 100000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (781, 50000)
  let e15 : LowMeanIntegerExpr := .atom (3, 8)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (39, 89)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-3, 8) e15
  let e21 : LowMeanIntegerExpr := .add (5, 8) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (15, 64) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-39, 89) e17
  let e24 : LowMeanIntegerExpr := .add (50, 89) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (1950, 7921) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (1950, 7921) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1950, 7921) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1950, 7921) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (30459, 7921000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (30459, 3960500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-258604257, 792100000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1181, 125)
  let e33 : LowMeanIntegerExpr := .pow (25, 64) e21 2
  let e34 : LowMeanIntegerExpr := .mul (1181, 320) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1181, 320) e34
  let e36 : LowMeanIntegerExpr := .add (-6363896639, 1584200000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-6363880797, 1584200000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (6363896639, 1584200000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0059 : LowMeanDirectSeedInput :=
  { record := 59, positions := [], target := { R := 2, expr := lowMeanSeedTargetExpr0059 } }

noncomputable def lowMeanSeedTargetExpr0060 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (14303, 100000)
  let e2 : LowMeanIntegerExpr := .atom (149, 20000)
  let e3 : LowMeanIntegerExpr := .atom (3, 1)
  let e4 : LowMeanIntegerExpr := .atom (22, 1)
  let e5 : LowMeanIntegerExpr := .neg (-22, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-19, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-2831, 20000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (37, 25000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1641, 2000000)
  let e10 : LowMeanIntegerExpr := .pow (361, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (592401, 2000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-592401, 2000000) e11
  let e13 : LowMeanIntegerExpr := .add (-589441, 2000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (781, 50000)
  let e15 : LowMeanIntegerExpr := .atom (3, 8)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (39, 89)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-3, 8) e15
  let e21 : LowMeanIntegerExpr := .add (5, 8) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (15, 64) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-39, 89) e17
  let e24 : LowMeanIntegerExpr := .add (50, 89) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (1950, 7921) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (1950, 7921) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1950, 7921) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1950, 7921) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (30459, 7921000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (91377, 7921000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-4486208161, 15842000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1181, 125)
  let e33 : LowMeanIntegerExpr := .pow (125, 512) e21 3
  let e34 : LowMeanIntegerExpr := .mul (1181, 512) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1181, 512) e34
  let e36 : LowMeanIntegerExpr := .add (-164112035769, 63368000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-164111402089, 63368000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (164112035769, 63368000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0060 : LowMeanDirectSeedInput :=
  { record := 60, positions := [], target := { R := 3, expr := lowMeanSeedTargetExpr0060 } }

noncomputable def lowMeanSeedTargetExpr0061 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (14303, 100000)
  let e2 : LowMeanIntegerExpr := .atom (149, 20000)
  let e3 : LowMeanIntegerExpr := .atom (4, 1)
  let e4 : LowMeanIntegerExpr := .atom (22, 1)
  let e5 : LowMeanIntegerExpr := .neg (-22, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-18, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1341, 10000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (893, 100000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1641, 2000000)
  let e10 : LowMeanIntegerExpr := .pow (324, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (132921, 500000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-132921, 500000) e11
  let e13 : LowMeanIntegerExpr := .add (-16057, 62500) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (781, 50000)
  let e15 : LowMeanIntegerExpr := .atom (3, 8)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (39, 89)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-3, 8) e15
  let e21 : LowMeanIntegerExpr := .add (5, 8) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (15, 64) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-39, 89) e17
  let e24 : LowMeanIntegerExpr := .add (50, 89) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (1950, 7921) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (1950, 7921) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1950, 7921) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1950, 7921) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (30459, 7921000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (30459, 1980250) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-119572747, 495062500) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1181, 125)
  let e33 : LowMeanIntegerExpr := .pow (625, 4096) e21 4
  let e34 : LowMeanIntegerExpr := .mul (5905, 4096) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-5905, 4096) e34
  let e36 : LowMeanIntegerExpr := .add (-853278508553, 506944000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-853273439113, 506944000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (853278508553, 506944000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0061 : LowMeanDirectSeedInput :=
  { record := 61, positions := [], target := { R := 4, expr := lowMeanSeedTargetExpr0061 } }

noncomputable def lowMeanSeedTargetExpr0062 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (14303, 100000)
  let e2 : LowMeanIntegerExpr := .atom (149, 20000)
  let e3 : LowMeanIntegerExpr := .atom (5, 1)
  let e4 : LowMeanIntegerExpr := .atom (22, 1)
  let e5 : LowMeanIntegerExpr := .neg (-22, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-17, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-2533, 20000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (819, 50000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1641, 2000000)
  let e10 : LowMeanIntegerExpr := .pow (289, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (474249, 2000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-474249, 2000000) e11
  let e13 : LowMeanIntegerExpr := .add (-441489, 2000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (781, 50000)
  let e15 : LowMeanIntegerExpr := .atom (3, 8)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (39, 89)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-3, 8) e15
  let e21 : LowMeanIntegerExpr := .add (5, 8) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (15, 64) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-39, 89) e17
  let e24 : LowMeanIntegerExpr := .add (50, 89) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (1950, 7921) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (1950, 7921) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1950, 7921) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1950, 7921) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (30459, 7921000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (30459, 1584200) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-3192444369, 15842000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1181, 125)
  let e33 : LowMeanIntegerExpr := .pow (3125, 32768) e21 5
  let e34 : LowMeanIntegerExpr := .mul (29525, 32768) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-29525, 32768) e34
  let e36 : LowMeanIntegerExpr := .add (-4471445836589, 4055552000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-4471405281069, 4055552000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (4471445836589, 4055552000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0062 : LowMeanDirectSeedInput :=
  { record := 62, positions := [], target := { R := 5, expr := lowMeanSeedTargetExpr0062 } }

noncomputable def lowMeanSeedTargetExpr0063 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (14303, 100000)
  let e2 : LowMeanIntegerExpr := .atom (149, 20000)
  let e3 : LowMeanIntegerExpr := .atom (6, 1)
  let e4 : LowMeanIntegerExpr := .atom (22, 1)
  let e5 : LowMeanIntegerExpr := .neg (-22, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-16, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-149, 1250) e2 e6
  let e8 : LowMeanIntegerExpr := .add (2383, 100000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1641, 2000000)
  let e10 : LowMeanIntegerExpr := .pow (256, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (3282, 15625) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-3282, 15625) e11
  let e13 : LowMeanIntegerExpr := .add (-93109, 500000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (781, 50000)
  let e15 : LowMeanIntegerExpr := .atom (3, 8)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (39, 89)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-3, 8) e15
  let e21 : LowMeanIntegerExpr := .add (5, 8) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (15, 64) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-39, 89) e17
  let e24 : LowMeanIntegerExpr := .add (50, 89) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (1950, 7921) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (1950, 7921) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1950, 7921) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1950, 7921) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (30459, 7921000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (91377, 3960500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-646139389, 3960500000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1181, 125)
  let e33 : LowMeanIntegerExpr := .pow (15625, 262144) e21 6
  let e34 : LowMeanIntegerExpr := .mul (147625, 262144) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-147625, 262144) e34
  let e36 : LowMeanIntegerExpr := .add (-23564074265313, 32444416000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-23563749821153, 32444416000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (23564074265313, 32444416000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0063 : LowMeanDirectSeedInput :=
  { record := 63, positions := [], target := { R := 6, expr := lowMeanSeedTargetExpr0063 } }

noncomputable def lowMeanSeedGroup0048 : List LowMeanDirectSeedInput := [lowMeanSeedRecord0048, lowMeanSeedRecord0049, lowMeanSeedRecord0050, lowMeanSeedRecord0051, lowMeanSeedRecord0052, lowMeanSeedRecord0053, lowMeanSeedRecord0054, lowMeanSeedRecord0055, lowMeanSeedRecord0056, lowMeanSeedRecord0057, lowMeanSeedRecord0058, lowMeanSeedRecord0059, lowMeanSeedRecord0060, lowMeanSeedRecord0061, lowMeanSeedRecord0062, lowMeanSeedRecord0063]

end Erdos993Lean.Analytic.V213
