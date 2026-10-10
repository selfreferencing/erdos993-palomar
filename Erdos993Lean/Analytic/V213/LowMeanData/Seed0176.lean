module

public import Erdos993Lean.Analytic.V213.LowMeanCoreAll
public import Erdos993Lean.Analytic.V213.LowMeanData.Seed0000
public import Erdos993Lean.Analytic.V213.LowMeanFiberSeed
public import Erdos993Lean.Analytic.V213.LowMeanIntegerExpr
public import Erdos993Lean.Analytic.V213.LowMeanSeedGeometry
public import Erdos993Lean.Analytic.V213.LowMeanWidthData
public import Erdos993Lean.Ceiling.Prefix
public import Erdos993Lean.Ceiling.Statement

/-! Exact core/budget keys and equation-51 targets for the direct fibers. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanSeedTargetExpr0176 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (55569, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (237, 250000)
  let e3 : LowMeanIntegerExpr := .atom (12, 1)
  let e4 : LowMeanIntegerExpr := .atom (23, 2)
  let e5 : LowMeanIntegerExpr := .neg (-23, 2) e4
  let e6 : LowMeanIntegerExpr := .add (1, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (237, 500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (56043, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (9853, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (1, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (9853, 40000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-9853, 40000000) e11
  let e13 : LowMeanIntegerExpr := .add (2231867, 40000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (1743, 100000)
  let e15 : LowMeanIntegerExpr := .atom (23, 48)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (103, 203)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-23, 48) e15
  let e21 : LowMeanIntegerExpr := .add (25, 48) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (575, 2304) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-103, 203) e17
  let e24 : LowMeanIntegerExpr := .add (100, 203) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (10300, 41209) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (10300, 41209) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1, 4) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (1743, 400000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (5229, 100000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (4323467, 40000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (8967, 10000)
  let e33 : LowMeanIntegerExpr := .pow (59604644775390625, 149587343098087735296) e21 12
  let e34 : LowMeanIntegerExpr := .mul (285053253173828125, 797799163189801254912) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-285053253173828125, 797799163189801254912) e34
  let e36 : LowMeanIntegerExpr := .add (6714562938577670580411367, 62328059624203223040000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (6715186219173912612641767, 62328059624203223040000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-6714562938577670580411367, 62328059624203223040000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0176 : LowMeanDirectSeedInput :=
  { record := 176, positions := [{ j := 4, mode := 0, left := 494, right := 0 }, { j := 5, mode := 0, left := 495, right := 0 }, { j := 7, mode := 0, left := 496, right := 0 }, { j := 8, mode := 0, left := 497, right := 0 }], target := { R := 12, expr := lowMeanSeedTargetExpr0176 } }

noncomputable def lowMeanSeedTargetExpr0177 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (55569, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (237, 250000)
  let e3 : LowMeanIntegerExpr := .atom (13, 1)
  let e4 : LowMeanIntegerExpr := .atom (23, 2)
  let e5 : LowMeanIntegerExpr := .neg (-23, 2) e4
  let e6 : LowMeanIntegerExpr := .add (3, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (711, 500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (56991, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (9853, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (9, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (88677, 40000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-88677, 40000000) e11
  let e13 : LowMeanIntegerExpr := .add (2190963, 40000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (1743, 100000)
  let e15 : LowMeanIntegerExpr := .atom (23, 48)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (103, 203)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-23, 48) e15
  let e21 : LowMeanIntegerExpr := .add (25, 48) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (575, 2304) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-103, 203) e17
  let e24 : LowMeanIntegerExpr := .add (100, 203) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (10300, 41209) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (10300, 41209) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1, 4) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (1743, 400000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (22659, 400000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (4456863, 40000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (8967, 10000)
  let e33 : LowMeanIntegerExpr := .pow (1490116119384765625, 7180192468708211294208) e21 13
  let e34 : LowMeanIntegerExpr := .mul (7126331329345703125, 38294359833110460235776) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-7126331329345703125, 38294359833110460235776) e34
  let e36 : LowMeanIntegerExpr := .add (332788402725981166040627599, 2991746861961754705920000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (332818320194600783587686799, 2991746861961754705920000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-332788402725981166040627599, 2991746861961754705920000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0177 : LowMeanDirectSeedInput :=
  { record := 177, positions := [{ j := 5, mode := 0, left := 498, right := 0 }, { j := 6, mode := 0, left := 499, right := 0 }, { j := 7, mode := 0, left := 500, right := 0 }, { j := 8, mode := 0, left := 501, right := 0 }], target := { R := 13, expr := lowMeanSeedTargetExpr0177 } }

noncomputable def lowMeanSeedTargetExpr0178 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (55569, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (237, 250000)
  let e3 : LowMeanIntegerExpr := .atom (14, 1)
  let e4 : LowMeanIntegerExpr := .atom (23, 2)
  let e5 : LowMeanIntegerExpr := .neg (-23, 2) e4
  let e6 : LowMeanIntegerExpr := .add (5, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (237, 100000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (57939, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (9853, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (25, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (9853, 1600000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-9853, 1600000) e11
  let e13 : LowMeanIntegerExpr := .add (414247, 8000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (1743, 100000)
  let e15 : LowMeanIntegerExpr := .atom (23, 48)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (103, 203)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-23, 48) e15
  let e21 : LowMeanIntegerExpr := .add (25, 48) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (575, 2304) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-103, 203) e17
  let e24 : LowMeanIntegerExpr := .add (100, 203) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (10300, 41209) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (10300, 41209) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1, 4) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (1743, 400000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (12201, 200000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (902287, 8000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (8967, 10000)
  let e33 : LowMeanIntegerExpr := .pow (37252902984619140625, 344649238497994142121984) e21 14
  let e34 : LowMeanIntegerExpr := .mul (178158283233642578125, 1838129271989302091317248) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-178158283233642578125, 1838129271989302091317248) e34
  let e36 : LowMeanIntegerExpr := .add (3236513437831137256725323723, 28720769874832845176832000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (3236800645529885585177092043, 28720769874832845176832000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-3236513437831137256725323723, 28720769874832845176832000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0178 : LowMeanDirectSeedInput :=
  { record := 178, positions := [{ j := 5, mode := 0, left := 502, right := 0 }, { j := 6, mode := 0, left := 503, right := 0 }, { j := 7, mode := 0, left := 504, right := 0 }, { j := 8, mode := 0, left := 505, right := 0 }], target := { R := 14, expr := lowMeanSeedTargetExpr0178 } }

noncomputable def lowMeanSeedTargetExpr0179 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (6447, 200000)
  let e2 : LowMeanIntegerExpr := .atom (253, 250000)
  let e3 : LowMeanIntegerExpr := .atom (0, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-16, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-253, 15625) e2 e6
  let e8 : LowMeanIntegerExpr := .add (16043, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1749, 5000000)
  let e10 : LowMeanIntegerExpr := .pow (256, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (6996, 78125) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-6996, 78125) e11
  let e13 : LowMeanIntegerExpr := .add (-367529, 5000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (119, 15625)
  let e15 : LowMeanIntegerExpr := .atom (23, 48)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (103, 203)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-23, 48) e15
  let e21 : LowMeanIntegerExpr := .add (25, 48) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (575, 2304) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-103, 203) e17
  let e24 : LowMeanIntegerExpr := .add (100, 203) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (10300, 41209) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (10300, 41209) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1, 4) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (119, 62500) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (0, 1) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-367529, 5000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (187, 125)
  let e33 : LowMeanIntegerExpr := .pow (1, 1) e21 0
  let e34 : LowMeanIntegerExpr := .mul (187, 125) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-187, 125) e34
  let e36 : LowMeanIntegerExpr := .add (-7847529, 5000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-7847479, 5000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (7847529, 5000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0179 : LowMeanDirectSeedInput :=
  { record := 179, positions := [], target := { R := 0, expr := lowMeanSeedTargetExpr0179 } }

noncomputable def lowMeanSeedTargetExpr0180 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (6447, 200000)
  let e2 : LowMeanIntegerExpr := .atom (253, 250000)
  let e3 : LowMeanIntegerExpr := .atom (1, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-15, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-759, 50000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (3411, 200000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1749, 5000000)
  let e10 : LowMeanIntegerExpr := .pow (225, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (15741, 200000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-15741, 200000) e11
  let e13 : LowMeanIntegerExpr := .add (-1233, 20000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (119, 15625)
  let e15 : LowMeanIntegerExpr := .atom (23, 48)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (103, 203)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .neg (-23, 48) e15
  let e20 : LowMeanIntegerExpr := .add (25, 48) e3 e19
  let e21 : LowMeanIntegerExpr := .mul (575, 2304) e15 e20
  let e22 : LowMeanIntegerExpr := .neg (-103, 203) e17
  let e23 : LowMeanIntegerExpr := .add (100, 203) e3 e22
  let e24 : LowMeanIntegerExpr := .mul (10300, 41209) e17 e23
  let e25 : LowMeanIntegerExpr := .maximum (10300, 41209) e21 e24
  let e26 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e15 e16 e26 e25
  let e28 : LowMeanIntegerExpr := .mul (119, 62500) e14 e27
  let e29 : LowMeanIntegerExpr := .mul (119, 62500) e28 e3
  let e30 : LowMeanIntegerExpr := .add (-29873, 500000) e13 e29
  let e31 : LowMeanIntegerExpr := .atom (187, 125)
  let e32 : LowMeanIntegerExpr := .pow (25, 48) e20 1
  let e33 : LowMeanIntegerExpr := .mul (187, 240) e31 e32
  let e34 : LowMeanIntegerExpr := .neg (-187, 240) e33
  let e35 : LowMeanIntegerExpr := .add (-1258369, 1500000) e30 e34
  let e36 : LowMeanIntegerExpr := .add (-629177, 750000) e0 e35
  let e37 : LowMeanIntegerExpr := .neg (1258369, 1500000) e35
  let e38 : LowMeanIntegerExpr := .add (1, 100000) e36 e37
  e38

noncomputable def lowMeanSeedRecord0180 : LowMeanDirectSeedInput :=
  { record := 180, positions := [], target := { R := 1, expr := lowMeanSeedTargetExpr0180 } }

noncomputable def lowMeanSeedTargetExpr0181 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (6447, 200000)
  let e2 : LowMeanIntegerExpr := .atom (253, 250000)
  let e3 : LowMeanIntegerExpr := .atom (2, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-14, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1771, 125000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (18067, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1749, 5000000)
  let e10 : LowMeanIntegerExpr := .pow (196, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (85701, 1250000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-85701, 1250000) e11
  let e13 : LowMeanIntegerExpr := .add (-252469, 5000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (119, 15625)
  let e15 : LowMeanIntegerExpr := .atom (23, 48)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (103, 203)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-23, 48) e15
  let e21 : LowMeanIntegerExpr := .add (25, 48) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (575, 2304) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-103, 203) e17
  let e24 : LowMeanIntegerExpr := .add (100, 203) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (10300, 41209) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (10300, 41209) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1, 4) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (119, 62500) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (119, 31250) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-233429, 5000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (187, 125)
  let e33 : LowMeanIntegerExpr := .pow (625, 2304) e21 2
  let e34 : LowMeanIntegerExpr := .mul (935, 2304) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-935, 2304) e34
  let e36 : LowMeanIntegerExpr := .add (-81450319, 180000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-81448519, 180000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (81450319, 180000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0181 : LowMeanDirectSeedInput :=
  { record := 181, positions := [], target := { R := 2, expr := lowMeanSeedTargetExpr0181 } }

noncomputable def lowMeanSeedTargetExpr0182 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (6447, 200000)
  let e2 : LowMeanIntegerExpr := .atom (253, 250000)
  let e3 : LowMeanIntegerExpr := .atom (3, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-13, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-3289, 250000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (19079, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1749, 5000000)
  let e10 : LowMeanIntegerExpr := .pow (169, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (295581, 5000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-295581, 5000000) e11
  let e13 : LowMeanIntegerExpr := .add (-100093, 2500000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (119, 15625)
  let e15 : LowMeanIntegerExpr := .atom (23, 48)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (103, 203)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-23, 48) e15
  let e21 : LowMeanIntegerExpr := .add (25, 48) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (575, 2304) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-103, 203) e17
  let e24 : LowMeanIntegerExpr := .add (100, 203) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (10300, 41209) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (10300, 41209) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1, 4) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (119, 62500) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (357, 62500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-85813, 2500000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (187, 125)
  let e33 : LowMeanIntegerExpr := .pow (15625, 110592) e21 3
  let e34 : LowMeanIntegerExpr := .mul (23375, 110592) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-23375, 110592) e34
  let e36 : LowMeanIntegerExpr := .add (-2122741603, 8640000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-2122655203, 8640000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (2122741603, 8640000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0182 : LowMeanDirectSeedInput :=
  { record := 182, positions := [], target := { R := 3, expr := lowMeanSeedTargetExpr0182 } }

noncomputable def lowMeanSeedTargetExpr0183 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (6447, 200000)
  let e2 : LowMeanIntegerExpr := .atom (253, 250000)
  let e3 : LowMeanIntegerExpr := .atom (4, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-12, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-759, 62500) e2 e6
  let e8 : LowMeanIntegerExpr := .add (20091, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1749, 5000000)
  let e10 : LowMeanIntegerExpr := .pow (144, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (15741, 312500) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-15741, 312500) e11
  let e13 : LowMeanIntegerExpr := .add (-151401, 5000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (119, 15625)
  let e15 : LowMeanIntegerExpr := .atom (23, 48)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (103, 203)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-23, 48) e15
  let e21 : LowMeanIntegerExpr := .add (25, 48) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (575, 2304) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-103, 203) e17
  let e24 : LowMeanIntegerExpr := .add (100, 203) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (10300, 41209) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (10300, 41209) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1, 4) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (119, 62500) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (119, 15625) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-113321, 5000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (187, 125)
  let e33 : LowMeanIntegerExpr := .pow (390625, 5308416) e21 4
  let e34 : LowMeanIntegerExpr := .mul (584375, 5308416) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-584375, 5308416) e34
  let e36 : LowMeanIntegerExpr := .add (-55053593899, 414720000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-55049446699, 414720000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (55053593899, 414720000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0183 : LowMeanDirectSeedInput :=
  { record := 183, positions := [{ j := 0, mode := 0, left := 506, right := 0 }, { j := 4, mode := 0, left := 507, right := 0 }], target := { R := 4, expr := lowMeanSeedTargetExpr0183 } }

noncomputable def lowMeanSeedTargetExpr0184 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (6447, 200000)
  let e2 : LowMeanIntegerExpr := .atom (253, 250000)
  let e3 : LowMeanIntegerExpr := .atom (5, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-11, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-2783, 250000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (21103, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1749, 5000000)
  let e10 : LowMeanIntegerExpr := .pow (121, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (211629, 5000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-211629, 5000000) e11
  let e13 : LowMeanIntegerExpr := .add (-53057, 2500000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (119, 15625)
  let e15 : LowMeanIntegerExpr := .atom (23, 48)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (103, 203)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-23, 48) e15
  let e21 : LowMeanIntegerExpr := .add (25, 48) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (575, 2304) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-103, 203) e17
  let e24 : LowMeanIntegerExpr := .add (100, 203) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (10300, 41209) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (10300, 41209) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1, 4) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (119, 62500) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (119, 12500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-29257, 2500000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (187, 125)
  let e33 : LowMeanIntegerExpr := .pow (9765625, 254803968) e21 5
  let e34 : LowMeanIntegerExpr := .mul (14609375, 254803968) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-14609375, 254803968) e34
  let e36 : LowMeanIntegerExpr := .add (-1374319912243, 19906560000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-1374120846643, 19906560000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (1374319912243, 19906560000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0184 : LowMeanDirectSeedInput :=
  { record := 184, positions := [{ j := 0, mode := 0, left := 508, right := 0 }, { j := 5, mode := 0, left := 509, right := 0 }], target := { R := 5, expr := lowMeanSeedTargetExpr0184 } }

noncomputable def lowMeanSeedTargetExpr0185 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (6447, 200000)
  let e2 : LowMeanIntegerExpr := .atom (253, 250000)
  let e3 : LowMeanIntegerExpr := .atom (6, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-10, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-253, 25000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (4423, 200000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1749, 5000000)
  let e10 : LowMeanIntegerExpr := .pow (100, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1749, 50000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1749, 50000) e11
  let e13 : LowMeanIntegerExpr := .add (-2573, 200000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (119, 15625)
  let e15 : LowMeanIntegerExpr := .atom (23, 48)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (103, 203)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-23, 48) e15
  let e21 : LowMeanIntegerExpr := .add (25, 48) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (575, 2304) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-103, 203) e17
  let e24 : LowMeanIntegerExpr := .add (100, 203) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (10300, 41209) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (10300, 41209) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1, 4) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (119, 62500) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (357, 31250) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-1441, 1000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (187, 125)
  let e33 : LowMeanIntegerExpr := .pow (244140625, 12230590464) e21 6
  let e34 : LowMeanIntegerExpr := .mul (365234375, 12230590464) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-365234375, 12230590464) e34
  let e36 : LowMeanIntegerExpr := .add (-5982166497791, 191102976000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-5980255468031, 191102976000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (5982166497791, 191102976000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0185 : LowMeanDirectSeedInput :=
  { record := 185, positions := [{ j := 1, mode := 0, left := 510, right := 0 }, { j := 5, mode := 0, left := 511, right := 0 }], target := { R := 6, expr := lowMeanSeedTargetExpr0185 } }

noncomputable def lowMeanSeedTargetExpr0186 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (6447, 200000)
  let e2 : LowMeanIntegerExpr := .atom (253, 250000)
  let e3 : LowMeanIntegerExpr := .atom (7, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-9, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-2277, 250000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (23127, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1749, 5000000)
  let e10 : LowMeanIntegerExpr := .pow (81, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (141669, 5000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-141669, 5000000) e11
  let e13 : LowMeanIntegerExpr := .add (-13017, 2500000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (119, 15625)
  let e15 : LowMeanIntegerExpr := .atom (23, 48)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (103, 203)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-23, 48) e15
  let e21 : LowMeanIntegerExpr := .add (25, 48) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (575, 2304) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-103, 203) e17
  let e24 : LowMeanIntegerExpr := .add (100, 203) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (10300, 41209) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (10300, 41209) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1, 4) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (119, 62500) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (833, 62500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (20303, 2500000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (187, 125)
  let e33 : LowMeanIntegerExpr := .pow (6103515625, 587068342272) e21 7
  let e34 : LowMeanIntegerExpr := .mul (9130859375, 587068342272) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-9130859375, 587068342272) e34
  let e36 : LowMeanIntegerExpr := .add (-340871871385987, 45864714240000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-340413224243587, 45864714240000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (340871871385987, 45864714240000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0186 : LowMeanDirectSeedInput :=
  { record := 186, positions := [{ j := 1, mode := 0, left := 512, right := 0 }, { j := 6, mode := 0, left := 513, right := 0 }], target := { R := 7, expr := lowMeanSeedTargetExpr0186 } }

noncomputable def lowMeanSeedTargetExpr0187 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (6447, 200000)
  let e2 : LowMeanIntegerExpr := .atom (253, 250000)
  let e3 : LowMeanIntegerExpr := .atom (8, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-8, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-253, 31250) e2 e6
  let e8 : LowMeanIntegerExpr := .add (24139, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1749, 5000000)
  let e10 : LowMeanIntegerExpr := .pow (64, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1749, 78125) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1749, 78125) e11
  let e13 : LowMeanIntegerExpr := .add (8759, 5000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (119, 15625)
  let e15 : LowMeanIntegerExpr := .atom (23, 48)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (103, 203)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-23, 48) e15
  let e21 : LowMeanIntegerExpr := .add (25, 48) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (575, 2304) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-103, 203) e17
  let e24 : LowMeanIntegerExpr := .add (100, 203) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (10300, 41209) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (10300, 41209) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1, 4) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (119, 62500) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (238, 15625) e29 e3
  let e31 : LowMeanIntegerExpr := .add (84919, 5000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (187, 125)
  let e33 : LowMeanIntegerExpr := .pow (152587890625, 28179280429056) e21 8
  let e34 : LowMeanIntegerExpr := .mul (228271484375, 28179280429056) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-228271484375, 28179280429056) e34
  let e36 : LowMeanIntegerExpr := .add (19556232701250101, 2201506283520000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (19578247764085301, 2201506283520000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-19556232701250101, 2201506283520000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0187 : LowMeanDirectSeedInput :=
  { record := 187, positions := [{ j := 1, mode := 0, left := 514, right := 0 }, { j := 2, mode := 0, left := 515, right := 0 }, { j := 6, mode := 0, left := 516, right := 0 }], target := { R := 8, expr := lowMeanSeedTargetExpr0187 } }

noncomputable def lowMeanSeedTargetExpr0188 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (6447, 200000)
  let e2 : LowMeanIntegerExpr := .atom (253, 250000)
  let e3 : LowMeanIntegerExpr := .atom (9, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-7, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1771, 250000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (25151, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1749, 5000000)
  let e10 : LowMeanIntegerExpr := .pow (49, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (85701, 5000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-85701, 5000000) e11
  let e13 : LowMeanIntegerExpr := .add (20027, 2500000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (119, 15625)
  let e15 : LowMeanIntegerExpr := .atom (23, 48)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (103, 203)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-23, 48) e15
  let e21 : LowMeanIntegerExpr := .add (25, 48) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (575, 2304) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-103, 203) e17
  let e24 : LowMeanIntegerExpr := .add (100, 203) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (10300, 41209) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (10300, 41209) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1, 4) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (119, 62500) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (1071, 62500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (62867, 2500000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (187, 125)
  let e33 : LowMeanIntegerExpr := .pow (3814697265625, 1352605460594688) e21 9
  let e34 : LowMeanIntegerExpr := .mul (5706787109375, 1352605460594688) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-5706787109375, 1352605460594688) e34
  let e36 : LowMeanIntegerExpr := .add (2211477491180273453, 105672301608960000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (2212534214196363053, 105672301608960000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-2211477491180273453, 105672301608960000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0188 : LowMeanDirectSeedInput :=
  { record := 188, positions := [{ j := 2, mode := 0, left := 517, right := 0 }, { j := 7, mode := 0, left := 518, right := 0 }], target := { R := 9, expr := lowMeanSeedTargetExpr0188 } }

noncomputable def lowMeanSeedTargetExpr0189 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (6447, 200000)
  let e2 : LowMeanIntegerExpr := .atom (253, 250000)
  let e3 : LowMeanIntegerExpr := .atom (10, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-6, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-759, 125000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (26163, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1749, 5000000)
  let e10 : LowMeanIntegerExpr := .pow (36, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (15741, 1250000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-15741, 1250000) e11
  let e13 : LowMeanIntegerExpr := .add (67851, 5000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (119, 15625)
  let e15 : LowMeanIntegerExpr := .atom (23, 48)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (103, 203)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-23, 48) e15
  let e21 : LowMeanIntegerExpr := .add (25, 48) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (575, 2304) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-103, 203) e17
  let e24 : LowMeanIntegerExpr := .add (100, 203) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (10300, 41209) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (10300, 41209) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1, 4) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (119, 62500) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (119, 6250) e29 e3
  let e31 : LowMeanIntegerExpr := .add (163051, 5000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (187, 125)
  let e33 : LowMeanIntegerExpr := .pow (95367431640625, 64925062108545024) e21 10
  let e34 : LowMeanIntegerExpr := .mul (142669677734375, 64925062108545024) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-142669677734375, 64925062108545024) e34
  let e36 : LowMeanIntegerExpr := .add (154261686143570307941, 5072270477230080000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (154312408848342608741, 5072270477230080000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-154261686143570307941, 5072270477230080000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0189 : LowMeanDirectSeedInput :=
  { record := 189, positions := [{ j := 2, mode := 0, left := 519, right := 0 }, { j := 3, mode := 0, left := 520, right := 0 }, { j := 7, mode := 0, left := 521, right := 0 }], target := { R := 10, expr := lowMeanSeedTargetExpr0189 } }

noncomputable def lowMeanSeedTargetExpr0190 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (6447, 200000)
  let e2 : LowMeanIntegerExpr := .atom (253, 250000)
  let e3 : LowMeanIntegerExpr := .atom (11, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-5, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-253, 50000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (1087, 40000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1749, 5000000)
  let e10 : LowMeanIntegerExpr := .pow (25, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1749, 200000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1749, 200000) e11
  let e13 : LowMeanIntegerExpr := .add (1843, 100000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (119, 15625)
  let e15 : LowMeanIntegerExpr := .atom (23, 48)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (103, 203)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-23, 48) e15
  let e21 : LowMeanIntegerExpr := .add (25, 48) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (575, 2304) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-103, 203) e17
  let e24 : LowMeanIntegerExpr := .add (100, 203) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (10300, 41209) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (10300, 41209) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1, 4) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (119, 62500) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (1309, 62500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (19687, 500000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (187, 125)
  let e33 : LowMeanIntegerExpr := .pow (2384185791015625, 3116402981210161152) e21 11
  let e34 : LowMeanIntegerExpr := .mul (3566741943359375, 3116402981210161152) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-3566741943359375, 3116402981210161152) e34
  let e36 : LowMeanIntegerExpr := .add (1861539203731398596857, 48693796581408768000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (1862026141697212684537, 48693796581408768000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-1861539203731398596857, 48693796581408768000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0190 : LowMeanDirectSeedInput :=
  { record := 190, positions := [{ j := 3, mode := 0, left := 522, right := 0 }, { j := 8, mode := 0, left := 523, right := 0 }], target := { R := 11, expr := lowMeanSeedTargetExpr0190 } }

noncomputable def lowMeanSeedTargetExpr0191 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (6447, 200000)
  let e2 : LowMeanIntegerExpr := .atom (253, 250000)
  let e3 : LowMeanIntegerExpr := .atom (12, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-4, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-253, 62500) e2 e6
  let e8 : LowMeanIntegerExpr := .add (28187, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1749, 5000000)
  let e10 : LowMeanIntegerExpr := .pow (16, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1749, 312500) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1749, 312500) e11
  let e13 : LowMeanIntegerExpr := .add (112951, 5000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (119, 15625)
  let e15 : LowMeanIntegerExpr := .atom (23, 48)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (103, 203)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-23, 48) e15
  let e21 : LowMeanIntegerExpr := .add (25, 48) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (575, 2304) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-103, 203) e17
  let e24 : LowMeanIntegerExpr := .add (100, 203) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (10300, 41209) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (10300, 41209) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1, 4) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (119, 62500) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (357, 15625) e29 e3
  let e31 : LowMeanIntegerExpr := .add (227191, 5000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (187, 125)
  let e33 : LowMeanIntegerExpr := .pow (59604644775390625, 149587343098087735296) e21 12
  let e34 : LowMeanIntegerExpr := .mul (89168548583984375, 149587343098087735296) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-89168548583984375, 149587343098087735296) e34
  let e36 : LowMeanIntegerExpr := .add (524047739419964512416149, 11686511179538104320000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (524164604531759893459349, 11686511179538104320000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-524047739419964512416149, 11686511179538104320000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0191 : LowMeanDirectSeedInput :=
  { record := 191, positions := [{ j := 3, mode := 0, left := 524, right := 0 }, { j := 4, mode := 0, left := 525, right := 0 }, { j := 8, mode := 0, left := 526, right := 0 }], target := { R := 12, expr := lowMeanSeedTargetExpr0191 } }

noncomputable def lowMeanSeedGroup0176 : List LowMeanDirectSeedInput := [lowMeanSeedRecord0176, lowMeanSeedRecord0177, lowMeanSeedRecord0178, lowMeanSeedRecord0179, lowMeanSeedRecord0180, lowMeanSeedRecord0181, lowMeanSeedRecord0182, lowMeanSeedRecord0183, lowMeanSeedRecord0184, lowMeanSeedRecord0185, lowMeanSeedRecord0186, lowMeanSeedRecord0187, lowMeanSeedRecord0188, lowMeanSeedRecord0189, lowMeanSeedRecord0190, lowMeanSeedRecord0191]

end Erdos993Lean.Analytic.V213
