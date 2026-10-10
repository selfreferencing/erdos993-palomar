module

public import Erdos993Lean.Analytic.V213.LowMeanCoreAll
public import Erdos993Lean.Analytic.V213.LowMeanData.Seed0208
public import Erdos993Lean.Analytic.V213.LowMeanFiberSeed
public import Erdos993Lean.Analytic.V213.LowMeanIntegerExpr
public import Erdos993Lean.Analytic.V213.LowMeanSeedGeometry
public import Erdos993Lean.Analytic.V213.LowMeanWidthData
public import Erdos993Lean.Ceiling.Prefix
public import Erdos993Lean.Ceiling.Statement

/-! Exact core/budget keys and equation-51 targets for the direct fibers. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanSeedTargetExpr0320 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (61769, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (2919, 5000000)
  let e3 : LowMeanIntegerExpr := .atom (12, 1)
  let e4 : LowMeanIntegerExpr := .atom (21, 2)
  let e5 : LowMeanIntegerExpr := .neg (-21, 2) e4
  let e6 : LowMeanIntegerExpr := .add (3, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (8757, 10000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (626447, 10000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (143, 125000)
  let e10 : LowMeanIntegerExpr := .pow (9, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1287, 500000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1287, 500000) e11
  let e13 : LowMeanIntegerExpr := .add (600707, 10000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (2047, 100000)
  let e15 : LowMeanIntegerExpr := .atom (11, 21)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (13, 23)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-11, 21) e15
  let e21 : LowMeanIntegerExpr := .add (10, 21) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (110, 441) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-13, 23) e17
  let e24 : LowMeanIntegerExpr := .add (10, 23) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (130, 529) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (110, 441) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (110, 441) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (22517, 4410000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (22517, 367500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (178371929, 1470000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (889, 1000)
  let e33 : LowMeanIntegerExpr := .pow (1000000000000, 7355827511386641) e21 12
  let e34 : LowMeanIntegerExpr := .mul (127000000000, 1050832501626663) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-127000000000, 1050832501626663) e34
  let e36 : LowMeanIntegerExpr := .add (1273825376673765422741, 10508325016266630000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (1273930459923928089041, 10508325016266630000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-1273825376673765422741, 10508325016266630000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0320 : LowMeanDirectSeedInput :=
  { record := 320, positions := [{ j := 5, mode := 0, left := 692, right := 0 }, { j := 6, mode := 0, left := 693, right := 0 }, { j := 8, mode := 0, left := 694, right := 0 }, { j := 9, mode := 0, left := 695, right := 0 }], target := { R := 12, expr := lowMeanSeedTargetExpr0320 } }

noncomputable def lowMeanSeedTargetExpr0321 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (61769, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (2919, 5000000)
  let e3 : LowMeanIntegerExpr := .atom (13, 1)
  let e4 : LowMeanIntegerExpr := .atom (21, 2)
  let e5 : LowMeanIntegerExpr := .neg (-21, 2) e4
  let e6 : LowMeanIntegerExpr := .add (5, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (2919, 2000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (126457, 2000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (143, 125000)
  let e10 : LowMeanIntegerExpr := .pow (25, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (143, 20000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-143, 20000) e11
  let e13 : LowMeanIntegerExpr := .add (112157, 2000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (2047, 100000)
  let e15 : LowMeanIntegerExpr := .atom (11, 21)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (13, 23)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-11, 21) e15
  let e21 : LowMeanIntegerExpr := .add (10, 21) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (110, 441) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-13, 23) e17
  let e24 : LowMeanIntegerExpr := .add (10, 23) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (130, 529) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (110, 441) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (110, 441) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (22517, 4410000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (292721, 4410000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (108005437, 882000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (889, 1000)
  let e33 : LowMeanIntegerExpr := .pow (10000000000000, 154472377739119461) e21 13
  let e34 : LowMeanIntegerExpr := .mul (1270000000000, 22067482534159923) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1270000000000, 22067482534159923) e34
  let e36 : LowMeanIntegerExpr := .add (5402013502475759436511, 44134965068319846000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (5402454852126442634971, 44134965068319846000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-5402013502475759436511, 44134965068319846000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0321 : LowMeanDirectSeedInput :=
  { record := 321, positions := [{ j := 6, mode := 0, left := 696, right := 0 }, { j := 7, mode := 0, left := 697, right := 0 }, { j := 8, mode := 0, left := 698, right := 0 }, { j := 9, mode := 0, left := 699, right := 0 }], target := { R := 13, expr := lowMeanSeedTargetExpr0321 } }

noncomputable def lowMeanSeedTargetExpr0322 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (8933, 250000)
  let e2 : LowMeanIntegerExpr := .atom (8401, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (0, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-16, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-8401, 625000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (27863, 1250000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (3593, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (256, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (7186, 78125) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-7186, 78125) e11
  let e13 : LowMeanIntegerExpr := .add (-87113, 1250000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (247, 31250)
  let e15 : LowMeanIntegerExpr := .atom (11, 21)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (13, 23)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-11, 21) e15
  let e21 : LowMeanIntegerExpr := .add (10, 21) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (110, 441) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-13, 23) e17
  let e24 : LowMeanIntegerExpr := .add (10, 23) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (130, 529) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (110, 441) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (110, 441) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2717, 1378125) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (0, 1) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-87113, 1250000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1773, 1000)
  let e33 : LowMeanIntegerExpr := .pow (1, 1) e21 0
  let e34 : LowMeanIntegerExpr := .mul (1773, 1000) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1773, 1000) e34
  let e36 : LowMeanIntegerExpr := .add (-2303363, 1250000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-4606701, 2500000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (2303363, 1250000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0322 : LowMeanDirectSeedInput :=
  { record := 322, positions := [], target := { R := 0, expr := lowMeanSeedTargetExpr0322 } }

noncomputable def lowMeanSeedTargetExpr0323 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (8933, 250000)
  let e2 : LowMeanIntegerExpr := .atom (8401, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (1, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-15, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-25203, 2000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (46261, 2000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (3593, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (225, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (32337, 400000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-32337, 400000) e11
  let e13 : LowMeanIntegerExpr := .add (-3607, 62500) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (247, 31250)
  let e15 : LowMeanIntegerExpr := .atom (11, 21)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (13, 23)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .neg (-11, 21) e15
  let e20 : LowMeanIntegerExpr := .add (10, 21) e3 e19
  let e21 : LowMeanIntegerExpr := .mul (110, 441) e15 e20
  let e22 : LowMeanIntegerExpr := .neg (-13, 23) e17
  let e23 : LowMeanIntegerExpr := .add (10, 23) e3 e22
  let e24 : LowMeanIntegerExpr := .mul (130, 529) e17 e23
  let e25 : LowMeanIntegerExpr := .maximum (110, 441) e21 e24
  let e26 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e25
  let e27 : LowMeanIntegerExpr := .selectLE (110, 441) e15 e16 e26 e25
  let e28 : LowMeanIntegerExpr := .mul (2717, 1378125) e14 e27
  let e29 : LowMeanIntegerExpr := .mul (2717, 1378125) e28 e3
  let e30 : LowMeanIntegerExpr := .add (-1536347, 27562500) e13 e29
  let e31 : LowMeanIntegerExpr := .atom (1773, 1000)
  let e32 : LowMeanIntegerExpr := .pow (10, 21) e20 1
  let e33 : LowMeanIntegerExpr := .mul (591, 700) e31 e32
  let e34 : LowMeanIntegerExpr := .neg (-591, 700) e33
  let e35 : LowMeanIntegerExpr := .add (-6201743, 6890625) e30 e34
  let e36 : LowMeanIntegerExpr := .add (-198453571, 220500000) e0 e35
  let e37 : LowMeanIntegerExpr := .neg (6201743, 6890625) e35
  let e38 : LowMeanIntegerExpr := .add (1, 100000) e36 e37
  e38

noncomputable def lowMeanSeedRecord0323 : LowMeanDirectSeedInput :=
  { record := 323, positions := [], target := { R := 1, expr := lowMeanSeedTargetExpr0323 } }

noncomputable def lowMeanSeedTargetExpr0324 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (8933, 250000)
  let e2 : LowMeanIntegerExpr := .atom (8401, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (2, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-14, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-58807, 5000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (119853, 5000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (3593, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (196, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (176057, 2500000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-176057, 2500000) e11
  let e13 : LowMeanIntegerExpr := .add (-232261, 5000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (247, 31250)
  let e15 : LowMeanIntegerExpr := .atom (11, 21)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (13, 23)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-11, 21) e15
  let e21 : LowMeanIntegerExpr := .add (10, 21) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (110, 441) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-13, 23) e17
  let e24 : LowMeanIntegerExpr := .add (10, 23) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (130, 529) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (110, 441) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (110, 441) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2717, 1378125) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (5434, 1378125) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-93732701, 2205000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1773, 1000)
  let e33 : LowMeanIntegerExpr := .pow (100, 441) e21 2
  let e34 : LowMeanIntegerExpr := .mul (197, 490) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-197, 490) e34
  let e36 : LowMeanIntegerExpr := .add (-20004749, 45000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-20004299, 45000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (20004749, 45000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0324 : LowMeanDirectSeedInput :=
  { record := 324, positions := [], target := { R := 2, expr := lowMeanSeedTargetExpr0324 } }

noncomputable def lowMeanSeedTargetExpr0325 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (8933, 250000)
  let e2 : LowMeanIntegerExpr := .atom (8401, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (3, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-13, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-109213, 10000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (248107, 10000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (3593, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (169, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (607217, 10000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-607217, 10000000) e11
  let e13 : LowMeanIntegerExpr := .add (-35911, 1000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (247, 31250)
  let e15 : LowMeanIntegerExpr := .atom (11, 21)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (13, 23)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-11, 21) e15
  let e21 : LowMeanIntegerExpr := .add (10, 21) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (110, 441) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-13, 23) e17
  let e24 : LowMeanIntegerExpr := .add (10, 23) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (130, 529) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (110, 441) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (110, 441) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2717, 1378125) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (2717, 459375) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-4409477, 147000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1773, 1000)
  let e33 : LowMeanIntegerExpr := .pow (1000, 9261) e21 3
  let e34 : LowMeanIntegerExpr := .mul (197, 1029) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-197, 1029) e34
  let e36 : LowMeanIntegerExpr := .add (-227866339, 1029000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-227856049, 1029000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (227866339, 1029000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0325 : LowMeanDirectSeedInput :=
  { record := 325, positions := [{ j := 0, mode := 0, left := 700, right := 0 }], target := { R := 3, expr := lowMeanSeedTargetExpr0325 } }

noncomputable def lowMeanSeedTargetExpr0326 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (8933, 250000)
  let e2 : LowMeanIntegerExpr := .atom (8401, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (4, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-12, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-25203, 2500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (64127, 2500000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (3593, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (144, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (32337, 625000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-32337, 625000) e11
  let e13 : LowMeanIntegerExpr := .add (-65221, 2500000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (247, 31250)
  let e15 : LowMeanIntegerExpr := .atom (11, 21)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (13, 23)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-11, 21) e15
  let e21 : LowMeanIntegerExpr := .add (10, 21) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (110, 441) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-13, 23) e17
  let e24 : LowMeanIntegerExpr := .add (10, 23) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (130, 529) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (110, 441) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (110, 441) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2717, 1378125) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (10868, 1378125) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-20068061, 1102500000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1773, 1000)
  let e33 : LowMeanIntegerExpr := .pow (10000, 194481) e21 4
  let e34 : LowMeanIntegerExpr := .mul (1970, 21609) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1970, 21609) e34
  let e36 : LowMeanIntegerExpr := .add (-5908334989, 54022500000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-1476948691, 13505625000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (5908334989, 54022500000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0326 : LowMeanDirectSeedInput :=
  { record := 326, positions := [{ j := 0, mode := 0, left := 701, right := 0 }], target := { R := 4, expr := lowMeanSeedTargetExpr0326 } }

noncomputable def lowMeanSeedTargetExpr0327 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (8933, 250000)
  let e2 : LowMeanIntegerExpr := .atom (8401, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (5, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-11, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-92411, 10000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (264909, 10000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (3593, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (121, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (434753, 10000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-434753, 10000000) e11
  let e13 : LowMeanIntegerExpr := .add (-42461, 2500000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (247, 31250)
  let e15 : LowMeanIntegerExpr := .atom (11, 21)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (13, 23)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-11, 21) e15
  let e21 : LowMeanIntegerExpr := .add (10, 21) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (110, 441) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-13, 23) e17
  let e24 : LowMeanIntegerExpr := .add (10, 23) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (130, 529) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (110, 441) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (110, 441) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2717, 1378125) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (2717, 275625) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-7857301, 1102500000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1773, 1000)
  let e33 : LowMeanIntegerExpr := .pow (100000, 4084101) e21 5
  let e34 : LowMeanIntegerExpr := .mul (19700, 453789) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-19700, 453789) e34
  let e36 : LowMeanIntegerExpr := .add (-57335162729, 1134472500000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-14330954501, 283618125000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (57335162729, 1134472500000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0327 : LowMeanDirectSeedInput :=
  { record := 327, positions := [{ j := 1, mode := 0, left := 702, right := 0 }, { j := 5, mode := 0, left := 703, right := 0 }], target := { R := 5, expr := lowMeanSeedTargetExpr0327 } }

noncomputable def lowMeanSeedTargetExpr0328 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (8933, 250000)
  let e2 : LowMeanIntegerExpr := .atom (8401, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (6, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-10, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-8401, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (27331, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (3593, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (100, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (3593, 100000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-3593, 100000) e11
  let e13 : LowMeanIntegerExpr := .add (-8599, 1000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (247, 31250)
  let e15 : LowMeanIntegerExpr := .atom (11, 21)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (13, 23)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-11, 21) e15
  let e21 : LowMeanIntegerExpr := .add (10, 21) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (110, 441) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-13, 23) e17
  let e24 : LowMeanIntegerExpr := .add (10, 23) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (130, 529) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (110, 441) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (110, 441) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2717, 1378125) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (5434, 459375) e29 e3
  let e31 : LowMeanIntegerExpr := .add (474827, 147000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1773, 1000)
  let e33 : LowMeanIntegerExpr := .pow (1000000, 85766121) e21 6
  let e34 : LowMeanIntegerExpr := .mul (197000, 9529569) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-197000, 9529569) e34
  let e36 : LowMeanIntegerExpr := .add (-166218390071, 9529569000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-166123094381, 9529569000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (166218390071, 9529569000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0328 : LowMeanDirectSeedInput :=
  { record := 328, positions := [{ j := 1, mode := 0, left := 704, right := 0 }, { j := 6, mode := 0, left := 705, right := 0 }], target := { R := 6, expr := lowMeanSeedTargetExpr0328 } }

noncomputable def lowMeanSeedTargetExpr0329 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (8933, 250000)
  let e2 : LowMeanIntegerExpr := .atom (8401, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (7, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-9, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-75609, 10000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (281711, 10000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (3593, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (81, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (291033, 10000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-291033, 10000000) e11
  let e13 : LowMeanIntegerExpr := .add (-4661, 5000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (247, 31250)
  let e15 : LowMeanIntegerExpr := .atom (11, 21)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (13, 23)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-11, 21) e15
  let e21 : LowMeanIntegerExpr := .add (10, 21) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (110, 441) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-13, 23) e17
  let e24 : LowMeanIntegerExpr := .add (10, 23) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (130, 529) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (110, 441) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (110, 441) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2717, 1378125) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (2717, 196875) e29 e3
  let e31 : LowMeanIntegerExpr := .add (4053557, 315000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1773, 1000)
  let e33 : LowMeanIntegerExpr := .pow (10000000, 1801088541) e21 7
  let e34 : LowMeanIntegerExpr := .mul (1970000, 200120949) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1970000, 200120949) e34
  let e36 : LowMeanIntegerExpr := .add (3026217042311, 1000604745000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (3036223089761, 1000604745000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-3026217042311, 1000604745000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0329 : LowMeanDirectSeedInput :=
  { record := 329, positions := [{ j := 1, mode := 0, left := 706, right := 0 }, { j := 2, mode := 0, left := 707, right := 0 }, { j := 6, mode := 0, left := 708, right := 0 }], target := { R := 7, expr := lowMeanSeedTargetExpr0329 } }

noncomputable def lowMeanSeedTargetExpr0330 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (8933, 250000)
  let e2 : LowMeanIntegerExpr := .atom (8401, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (8, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-8, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-8401, 1250000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (4533, 156250) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (3593, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (64, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (3593, 156250) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-3593, 156250) e11
  let e13 : LowMeanIntegerExpr := .add (94, 15625) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (247, 31250)
  let e15 : LowMeanIntegerExpr := .atom (11, 21)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (13, 23)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-11, 21) e15
  let e21 : LowMeanIntegerExpr := .add (10, 21) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (110, 441) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-13, 23) e17
  let e24 : LowMeanIntegerExpr := .add (10, 23) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (130, 529) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (110, 441) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (110, 441) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2717, 1378125) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (21736, 1378125) e29 e3
  let e31 : LowMeanIntegerExpr := .add (150134, 6890625) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1773, 1000)
  let e33 : LowMeanIntegerExpr := .pow (100000000, 37822859361) e21 8
  let e34 : LowMeanIntegerExpr := .mul (19700000, 4202539929) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-19700000, 4202539929) e34
  let e36 : LowMeanIntegerExpr := .add (1122899812246, 65664686390625) e31 e35
  let e37 : LowMeanIntegerExpr := .add (35953806691517, 2101269964500000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-1122899812246, 65664686390625) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0330 : LowMeanDirectSeedInput :=
  { record := 330, positions := [{ j := 2, mode := 0, left := 709, right := 0 }, { j := 7, mode := 0, left := 710, right := 0 }], target := { R := 8, expr := lowMeanSeedTargetExpr0330 } }

noncomputable def lowMeanSeedTargetExpr0331 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (8933, 250000)
  let e2 : LowMeanIntegerExpr := .atom (8401, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (9, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-7, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-58807, 10000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (298513, 10000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (3593, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (49, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (176057, 10000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-176057, 10000000) e11
  let e13 : LowMeanIntegerExpr := .add (15307, 1250000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (247, 31250)
  let e15 : LowMeanIntegerExpr := .atom (11, 21)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (13, 23)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-11, 21) e15
  let e21 : LowMeanIntegerExpr := .add (10, 21) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (110, 441) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-13, 23) e17
  let e24 : LowMeanIntegerExpr := .add (10, 23) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (130, 529) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (110, 441) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (110, 441) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2717, 1378125) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (2717, 153125) e29 e3
  let e31 : LowMeanIntegerExpr := .add (1836843, 61250000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1773, 1000)
  let e33 : LowMeanIntegerExpr := .pow (1000000000, 794280046581) e21 9
  let e34 : LowMeanIntegerExpr := .mul (197000000, 88253338509) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-197000000, 88253338509) e34
  let e36 : LowMeanIntegerExpr := .add (3062066878916063, 110316673136250000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (6126340091294851, 220633346272500000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-3062066878916063, 110316673136250000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0331 : LowMeanDirectSeedInput :=
  { record := 331, positions := [{ j := 3, mode := 0, left := 711, right := 0 }, { j := 8, mode := 0, left := 712, right := 0 }], target := { R := 9, expr := lowMeanSeedTargetExpr0331 } }

noncomputable def lowMeanSeedTargetExpr0332 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (8933, 250000)
  let e2 : LowMeanIntegerExpr := .atom (8401, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (10, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-6, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-25203, 5000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (153457, 5000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (3593, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (36, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (32337, 2500000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-32337, 2500000) e11
  let e13 : LowMeanIntegerExpr := .add (88783, 5000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (247, 31250)
  let e15 : LowMeanIntegerExpr := .atom (11, 21)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (13, 23)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-11, 21) e15
  let e21 : LowMeanIntegerExpr := .add (10, 21) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (110, 441) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-13, 23) e17
  let e24 : LowMeanIntegerExpr := .add (10, 23) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (130, 529) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (110, 441) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (110, 441) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2717, 1378125) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (5434, 275625) e29 e3
  let e31 : LowMeanIntegerExpr := .add (82625303, 2205000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1773, 1000)
  let e33 : LowMeanIntegerExpr := .pow (10000000000, 16679880978201) e21 10
  let e34 : LowMeanIntegerExpr := .mul (1970000000, 1853320108689) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1970000000, 1853320108689) e34
  let e36 : LowMeanIntegerExpr := .add (337386135003223487, 9266600543445000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (337478801008657937, 9266600543445000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-337386135003223487, 9266600543445000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0332 : LowMeanDirectSeedInput :=
  { record := 332, positions := [{ j := 3, mode := 0, left := 713, right := 0 }, { j := 4, mode := 0, left := 714, right := 0 }, { j := 8, mode := 0, left := 715, right := 0 }], target := { R := 10, expr := lowMeanSeedTargetExpr0332 } }

noncomputable def lowMeanSeedTargetExpr0333 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (8933, 250000)
  let e2 : LowMeanIntegerExpr := .atom (8401, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (11, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-5, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-8401, 2000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (63063, 2000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (3593, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (25, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (3593, 400000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-3593, 400000) e11
  let e13 : LowMeanIntegerExpr := .add (22549, 1000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (247, 31250)
  let e15 : LowMeanIntegerExpr := .atom (11, 21)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (13, 23)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-11, 21) e15
  let e21 : LowMeanIntegerExpr := .add (10, 21) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (110, 441) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-13, 23) e17
  let e24 : LowMeanIntegerExpr := .add (10, 23) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (130, 529) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (110, 441) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (110, 441) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2717, 1378125) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (29887, 1378125) e29 e3
  let e31 : LowMeanIntegerExpr := .add (19507949, 441000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1773, 1000)
  let e33 : LowMeanIntegerExpr := .pow (100000000000, 350277500542221) e21 11
  let e34 : LowMeanIntegerExpr := .mul (19700000000, 38919722282469) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-19700000000, 38919722282469) e34
  let e36 : LowMeanIntegerExpr := .add (1701941626713308041, 38919722282469000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (1702330823936132731, 38919722282469000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-1701941626713308041, 38919722282469000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0333 : LowMeanDirectSeedInput :=
  { record := 333, positions := [{ j := 4, mode := 0, left := 716, right := 0 }, { j := 8, mode := 0, left := 717, right := 0 }, { j := 9, mode := 0, left := 718, right := 0 }], target := { R := 11, expr := lowMeanSeedTargetExpr0333 } }

noncomputable def lowMeanSeedTargetExpr0334 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (8933, 250000)
  let e2 : LowMeanIntegerExpr := .atom (8401, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (12, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-4, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-8401, 2500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (80929, 2500000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (3593, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (16, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (3593, 625000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-3593, 625000) e11
  let e13 : LowMeanIntegerExpr := .add (66557, 2500000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (247, 31250)
  let e15 : LowMeanIntegerExpr := .atom (11, 21)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (13, 23)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-11, 21) e15
  let e21 : LowMeanIntegerExpr := .add (10, 21) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (110, 441) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-13, 23) e17
  let e24 : LowMeanIntegerExpr := .add (10, 23) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (130, 529) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (110, 441) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (110, 441) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2717, 1378125) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (10868, 459375) e29 e3
  let e31 : LowMeanIntegerExpr := .add (18478279, 367500000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1773, 1000)
  let e33 : LowMeanIntegerExpr := .pow (1000000000000, 7355827511386641) e21 12
  let e34 : LowMeanIntegerExpr := .mul (197000000000, 817314167931849) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-197000000000, 817314167931849) e34
  let e36 : LowMeanIntegerExpr := .add (102245998133996998693, 2043285419829622500000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (51133215494097647459, 1021642709914811250000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-102245998133996998693, 2043285419829622500000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0334 : LowMeanDirectSeedInput :=
  { record := 334, positions := [{ j := 4, mode := 0, left := 719, right := 0 }, { j := 5, mode := 0, left := 720, right := 0 }, { j := 9, mode := 0, left := 721, right := 0 }, { j := 10, mode := 0, left := 722, right := 0 }], target := { R := 12, expr := lowMeanSeedTargetExpr0334 } }

noncomputable def lowMeanSeedTargetExpr0335 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (8933, 250000)
  let e2 : LowMeanIntegerExpr := .atom (8401, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (13, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-3, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-25203, 10000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (332117, 10000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (3593, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (9, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (32337, 10000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-32337, 10000000) e11
  let e13 : LowMeanIntegerExpr := .add (14989, 500000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (247, 31250)
  let e15 : LowMeanIntegerExpr := .atom (11, 21)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (13, 23)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-11, 21) e15
  let e21 : LowMeanIntegerExpr := .add (10, 21) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (110, 441) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-13, 23) e17
  let e24 : LowMeanIntegerExpr := .add (10, 23) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (130, 529) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (110, 441) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (110, 441) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2717, 1378125) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (35321, 1378125) e29 e3
  let e31 : LowMeanIntegerExpr := .add (12261509, 220500000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1773, 1000)
  let e33 : LowMeanIntegerExpr := .pow (10000000000000, 154472377739119461) e21 13
  let e34 : LowMeanIntegerExpr := .mul (1970000000000, 17163597526568829) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1970000000000, 17163597526568829) e34
  let e36 : LowMeanIntegerExpr := .add (476229525043994185721, 8581798763284414500000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (238157671515813514933, 4290899381642207250000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-476229525043994185721, 8581798763284414500000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0335 : LowMeanDirectSeedInput :=
  { record := 335, positions := [{ j := 5, mode := 0, left := 723, right := 0 }, { j := 9, mode := 0, left := 724, right := 0 }, { j := 10, mode := 0, left := 725, right := 0 }], target := { R := 13, expr := lowMeanSeedTargetExpr0335 } }

noncomputable def lowMeanSeedGroup0320 : List LowMeanDirectSeedInput := [lowMeanSeedRecord0320, lowMeanSeedRecord0321, lowMeanSeedRecord0322, lowMeanSeedRecord0323, lowMeanSeedRecord0324, lowMeanSeedRecord0325, lowMeanSeedRecord0326, lowMeanSeedRecord0327, lowMeanSeedRecord0328, lowMeanSeedRecord0329, lowMeanSeedRecord0330, lowMeanSeedRecord0331, lowMeanSeedRecord0332, lowMeanSeedRecord0333, lowMeanSeedRecord0334, lowMeanSeedRecord0335]

end Erdos993Lean.Analytic.V213
