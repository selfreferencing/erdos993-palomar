module

public import Erdos993Lean.Analytic.V213.LowMeanCoreAll
public import Erdos993Lean.Analytic.V213.LowMeanData.Seed0224
public import Erdos993Lean.Analytic.V213.LowMeanFiberSeed
public import Erdos993Lean.Analytic.V213.LowMeanIntegerExpr
public import Erdos993Lean.Analytic.V213.LowMeanSeedGeometry
public import Erdos993Lean.Analytic.V213.LowMeanWidthData
public import Erdos993Lean.Ceiling.Prefix
public import Erdos993Lean.Ceiling.Statement

/-! Exact core/budget keys and equation-51 targets for the direct fibers. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanSeedTargetExpr0304 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (89731, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (-467, 125000)
  let e3 : LowMeanIntegerExpr := .atom (7, 1)
  let e4 : LowMeanIntegerExpr := .atom (8, 1)
  let e5 : LowMeanIntegerExpr := .neg (-8, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-1, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (467, 125000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (93467, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (289, 200000)
  let e10 : LowMeanIntegerExpr := .pow (1, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (289, 200000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-289, 200000) e11
  let e13 : LowMeanIntegerExpr := .add (46011, 500000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (3873, 100000)
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
  let e29 : LowMeanIntegerExpr := .mul (14201, 1470000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (14201, 210000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (1676281, 10500000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (4759, 5000)
  let e33 : LowMeanIntegerExpr := .pow (10000000, 1801088541) e21 7
  let e34 : LowMeanIntegerExpr := .mul (9518000, 1801088541) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-9518000, 1801088541) e34
  let e36 : LowMeanIntegerExpr := .add (139009119076001, 900544270500000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (69509062259353, 450272135250000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-139009119076001, 900544270500000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0304 : LowMeanDirectSeedInput :=
  { record := 304, positions := [{ j := 2, mode := 0, left := 656, right := 0 }, { j := 3, mode := 0, left := 657, right := 0 }, { j := 5, mode := 0, left := 658, right := 0 }, { j := 6, mode := 0, left := 659, right := 0 }], target := { R := 7, expr := lowMeanSeedTargetExpr0304 } }

noncomputable def lowMeanSeedTargetExpr0305 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (89731, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (-467, 125000)
  let e3 : LowMeanIntegerExpr := .atom (8, 1)
  let e4 : LowMeanIntegerExpr := .neg (-8, 1) e3
  let e5 : LowMeanIntegerExpr := .add (0, 1) e3 e4
  let e6 : LowMeanIntegerExpr := .mul (0, 1) e2 e5
  let e7 : LowMeanIntegerExpr := .add (89731, 1000000) e1 e6
  let e8 : LowMeanIntegerExpr := .atom (289, 200000)
  let e9 : LowMeanIntegerExpr := .pow (0, 1) e5 2
  let e10 : LowMeanIntegerExpr := .mul (0, 1) e8 e9
  let e11 : LowMeanIntegerExpr := .neg (0, 1) e10
  let e12 : LowMeanIntegerExpr := .add (89731, 1000000) e7 e11
  let e13 : LowMeanIntegerExpr := .atom (3873, 100000)
  let e14 : LowMeanIntegerExpr := .atom (11, 21)
  let e15 : LowMeanIntegerExpr := .atom (1, 2)
  let e16 : LowMeanIntegerExpr := .atom (13, 23)
  let e17 : LowMeanIntegerExpr := .atom (1, 4)
  let e18 : LowMeanIntegerExpr := .atom (1, 1)
  let e19 : LowMeanIntegerExpr := .neg (-11, 21) e14
  let e20 : LowMeanIntegerExpr := .add (10, 21) e18 e19
  let e21 : LowMeanIntegerExpr := .mul (110, 441) e14 e20
  let e22 : LowMeanIntegerExpr := .neg (-13, 23) e16
  let e23 : LowMeanIntegerExpr := .add (10, 23) e18 e22
  let e24 : LowMeanIntegerExpr := .mul (130, 529) e16 e23
  let e25 : LowMeanIntegerExpr := .maximum (110, 441) e21 e24
  let e26 : LowMeanIntegerExpr := .selectLE (1, 4) e15 e16 e17 e25
  let e27 : LowMeanIntegerExpr := .selectLE (110, 441) e14 e15 e26 e25
  let e28 : LowMeanIntegerExpr := .mul (14201, 1470000) e13 e27
  let e29 : LowMeanIntegerExpr := .mul (14201, 183750) e28 e3
  let e30 : LowMeanIntegerExpr := .add (24551257, 147000000) e12 e29
  let e31 : LowMeanIntegerExpr := .atom (4759, 5000)
  let e32 : LowMeanIntegerExpr := .pow (100000000, 37822859361) e20 8
  let e33 : LowMeanIntegerExpr := .mul (95180000, 37822859361) e31 e32
  let e34 : LowMeanIntegerExpr := .neg (-95180000, 37822859361) e33
  let e35 : LowMeanIntegerExpr := .add (6221818235692291, 37822859361000000) e30 e34
  let e36 : LowMeanIntegerExpr := .add (6222196464285901, 37822859361000000) e0 e35
  let e37 : LowMeanIntegerExpr := .neg (-6221818235692291, 37822859361000000) e35
  let e38 : LowMeanIntegerExpr := .add (1, 100000) e36 e37
  e38

noncomputable def lowMeanSeedRecord0305 : LowMeanDirectSeedInput :=
  { record := 305, positions := [{ j := 3, mode := 0, left := 660, right := 0 }, { j := 4, mode := 0, left := 661, right := 0 }, { j := 6, mode := 0, left := 662, right := 0 }], target := { R := 8, expr := lowMeanSeedTargetExpr0305 } }

noncomputable def lowMeanSeedTargetExpr0306 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (89731, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (-467, 125000)
  let e3 : LowMeanIntegerExpr := .atom (9, 1)
  let e4 : LowMeanIntegerExpr := .atom (8, 1)
  let e5 : LowMeanIntegerExpr := .neg (-8, 1) e4
  let e6 : LowMeanIntegerExpr := .add (1, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-467, 125000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (17199, 200000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (289, 200000)
  let e10 : LowMeanIntegerExpr := .pow (1, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (289, 200000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-289, 200000) e11
  let e13 : LowMeanIntegerExpr := .add (1691, 20000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (3873, 100000)
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
  let e29 : LowMeanIntegerExpr := .mul (14201, 1470000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (42603, 490000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (33613, 196000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (4759, 5000)
  let e33 : LowMeanIntegerExpr := .pow (1000000000, 794280046581) e21 9
  let e34 : LowMeanIntegerExpr := .mul (951800000, 794280046581) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-951800000, 794280046581) e34
  let e36 : LowMeanIntegerExpr := .add (541052702157697, 3177120186324000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (6763555916994503, 39714002329050000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-541052702157697, 3177120186324000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0306 : LowMeanDirectSeedInput :=
  { record := 306, positions := [{ j := 4, mode := 0, left := 663, right := 0 }, { j := 6, mode := 0, left := 664, right := 0 }, { j := 7, mode := 0, left := 665, right := 0 }], target := { R := 9, expr := lowMeanSeedTargetExpr0306 } }

noncomputable def lowMeanSeedTargetExpr0307 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (89731, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (-467, 125000)
  let e3 : LowMeanIntegerExpr := .atom (10, 1)
  let e4 : LowMeanIntegerExpr := .atom (8, 1)
  let e5 : LowMeanIntegerExpr := .neg (-8, 1) e4
  let e6 : LowMeanIntegerExpr := .add (2, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-467, 62500) e2 e6
  let e8 : LowMeanIntegerExpr := .add (82259, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (289, 200000)
  let e10 : LowMeanIntegerExpr := .pow (4, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (289, 50000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-289, 50000) e11
  let e13 : LowMeanIntegerExpr := .add (76479, 1000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (3873, 100000)
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
  let e29 : LowMeanIntegerExpr := .mul (14201, 1470000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (14201, 147000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (25443413, 147000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (4759, 5000)
  let e33 : LowMeanIntegerExpr := .pow (10000000000, 16679880978201) e21 10
  let e34 : LowMeanIntegerExpr := .mul (9518000000, 16679880978201) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-9518000000, 16679880978201) e34
  let e36 : LowMeanIntegerExpr := .add (2877509894688517279, 16679880978201000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (2877676693498299289, 16679880978201000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-2877509894688517279, 16679880978201000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0307 : LowMeanDirectSeedInput :=
  { record := 307, positions := [{ j := 5, mode := 0, left := 666, right := 0 }, { j := 6, mode := 0, left := 667, right := 0 }, { j := 7, mode := 0, left := 668, right := 0 }], target := { R := 10, expr := lowMeanSeedTargetExpr0307 } }

noncomputable def lowMeanSeedTargetExpr0308 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (61769, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (2919, 5000000)
  let e3 : LowMeanIntegerExpr := .atom (0, 1)
  let e4 : LowMeanIntegerExpr := .atom (21, 2)
  let e5 : LowMeanIntegerExpr := .neg (-21, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-21, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-61299, 10000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (556391, 10000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (143, 125000)
  let e10 : LowMeanIntegerExpr := .pow (441, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (63063, 500000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-63063, 500000) e11
  let e13 : LowMeanIntegerExpr := .add (-704869, 10000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (0, 1) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-704869, 10000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (889, 1000)
  let e33 : LowMeanIntegerExpr := .pow (1, 1) e21 0
  let e34 : LowMeanIntegerExpr := .mul (889, 1000) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-889, 1000) e34
  let e36 : LowMeanIntegerExpr := .add (-9594869, 10000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-9594769, 10000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (9594869, 10000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0308 : LowMeanDirectSeedInput :=
  { record := 308, positions := [], target := { R := 0, expr := lowMeanSeedTargetExpr0308 } }

noncomputable def lowMeanSeedTargetExpr0309 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (61769, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (2919, 5000000)
  let e3 : LowMeanIntegerExpr := .atom (1, 1)
  let e4 : LowMeanIntegerExpr := .atom (21, 2)
  let e5 : LowMeanIntegerExpr := .neg (-21, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-19, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-55461, 10000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (562229, 10000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (143, 125000)
  let e10 : LowMeanIntegerExpr := .pow (361, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (51623, 500000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-51623, 500000) e11
  let e13 : LowMeanIntegerExpr := .add (-470231, 10000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (2047, 100000)
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
  let e28 : LowMeanIntegerExpr := .mul (22517, 4410000) e14 e27
  let e29 : LowMeanIntegerExpr := .mul (22517, 4410000) e28 e3
  let e30 : LowMeanIntegerExpr := .add (-184854871, 4410000000) e13 e29
  let e31 : LowMeanIntegerExpr := .atom (889, 1000)
  let e32 : LowMeanIntegerExpr := .pow (10, 21) e20 1
  let e33 : LowMeanIntegerExpr := .mul (127, 300) e31 e32
  let e34 : LowMeanIntegerExpr := .neg (-127, 300) e33
  let e35 : LowMeanIntegerExpr := .add (-2051754871, 4410000000) e30 e34
  let e36 : LowMeanIntegerExpr := .add (-2051710771, 4410000000) e0 e35
  let e37 : LowMeanIntegerExpr := .neg (2051754871, 4410000000) e35
  let e38 : LowMeanIntegerExpr := .add (1, 100000) e36 e37
  e38

noncomputable def lowMeanSeedRecord0309 : LowMeanDirectSeedInput :=
  { record := 309, positions := [], target := { R := 1, expr := lowMeanSeedTargetExpr0309 } }

noncomputable def lowMeanSeedTargetExpr0310 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (61769, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (2919, 5000000)
  let e3 : LowMeanIntegerExpr := .atom (2, 1)
  let e4 : LowMeanIntegerExpr := .atom (21, 2)
  let e5 : LowMeanIntegerExpr := .neg (-21, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-17, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-49623, 10000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (568067, 10000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (143, 125000)
  let e10 : LowMeanIntegerExpr := .pow (289, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (41327, 500000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-41327, 500000) e11
  let e13 : LowMeanIntegerExpr := .add (-258473, 10000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (22517, 2205000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-68952593, 4410000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (889, 1000)
  let e33 : LowMeanIntegerExpr := .pow (100, 441) e21 2
  let e34 : LowMeanIntegerExpr := .mul (127, 630) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-127, 630) e34
  let e36 : LowMeanIntegerExpr := .add (-106439177, 490000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-106434277, 490000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (106439177, 490000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0310 : LowMeanDirectSeedInput :=
  { record := 310, positions := [], target := { R := 2, expr := lowMeanSeedTargetExpr0310 } }

noncomputable def lowMeanSeedTargetExpr0311 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (61769, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (2919, 5000000)
  let e3 : LowMeanIntegerExpr := .atom (3, 1)
  let e4 : LowMeanIntegerExpr := .atom (21, 2)
  let e5 : LowMeanIntegerExpr := .neg (-21, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-15, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-8757, 2000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (114781, 2000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (143, 125000)
  let e10 : LowMeanIntegerExpr := .pow (225, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1287, 20000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1287, 20000) e11
  let e13 : LowMeanIntegerExpr := .add (-13919, 2000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (22517, 1470000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (2457307, 294000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (889, 1000)
  let e33 : LowMeanIntegerExpr := .pow (1000, 9261) e21 3
  let e34 : LowMeanIntegerExpr := .mul (127, 1323) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-127, 1323) e34
  let e36 : LowMeanIntegerExpr := .add (-231884237, 2646000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-231857777, 2646000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (231884237, 2646000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0311 : LowMeanDirectSeedInput :=
  { record := 311, positions := [{ j := 0, mode := 0, left := 669, right := 0 }], target := { R := 3, expr := lowMeanSeedTargetExpr0311 } }

noncomputable def lowMeanSeedTargetExpr0312 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (61769, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (2919, 5000000)
  let e3 : LowMeanIntegerExpr := .atom (4, 1)
  let e4 : LowMeanIntegerExpr := .atom (21, 2)
  let e5 : LowMeanIntegerExpr := .neg (-21, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-13, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-37947, 10000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (579743, 10000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (143, 125000)
  let e10 : LowMeanIntegerExpr := .pow (169, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (24167, 500000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-24167, 500000) e11
  let e13 : LowMeanIntegerExpr := .add (96403, 10000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (22517, 1102500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (132581723, 4410000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (889, 1000)
  let e33 : LowMeanIntegerExpr := .pow (10000, 194481) e21 4
  let e34 : LowMeanIntegerExpr := .mul (1270, 27783) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1270, 27783) e34
  let e36 : LowMeanIntegerExpr := .add (-4347351451, 277830000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-4344573151, 277830000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (4347351451, 277830000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0312 : LowMeanDirectSeedInput :=
  { record := 312, positions := [{ j := 0, mode := 0, left := 670, right := 0 }, { j := 4, mode := 0, left := 671, right := 0 }], target := { R := 4, expr := lowMeanSeedTargetExpr0312 } }

noncomputable def lowMeanSeedTargetExpr0313 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (61769, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (2919, 5000000)
  let e3 : LowMeanIntegerExpr := .atom (5, 1)
  let e4 : LowMeanIntegerExpr := .atom (21, 2)
  let e5 : LowMeanIntegerExpr := .neg (-21, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-11, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-32109, 10000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (585581, 10000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (143, 125000)
  let e10 : LowMeanIntegerExpr := .pow (121, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (17303, 500000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-17303, 500000) e11
  let e13 : LowMeanIntegerExpr := .add (239521, 10000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (22517, 882000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (218213761, 4410000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (889, 1000)
  let e33 : LowMeanIntegerExpr := .pow (100000, 4084101) e21 5
  let e34 : LowMeanIntegerExpr := .mul (12700, 583443) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-12700, 583443) e34
  let e36 : LowMeanIntegerExpr := .add (161696805803, 5834430000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (161755150103, 5834430000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-161696805803, 5834430000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0313 : LowMeanDirectSeedInput :=
  { record := 313, positions := [{ j := 1, mode := 1, left := 672, right := 673 }, { j := 5, mode := 0, left := 674, right := 0 }], target := { R := 5, expr := lowMeanSeedTargetExpr0313 } }

noncomputable def lowMeanSeedTargetExpr0314 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (61769, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (2919, 5000000)
  let e3 : LowMeanIntegerExpr := .atom (6, 1)
  let e4 : LowMeanIntegerExpr := .atom (21, 2)
  let e5 : LowMeanIntegerExpr := .neg (-21, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-9, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-26271, 10000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (591419, 10000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (143, 125000)
  let e10 : LowMeanIntegerExpr := .pow (81, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (11583, 500000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-11583, 500000) e11
  let e13 : LowMeanIntegerExpr := .add (359759, 10000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (22517, 735000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (97918573, 1470000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (889, 1000)
  let e33 : LowMeanIntegerExpr := .pow (1000000, 85766121) e21 6
  let e34 : LowMeanIntegerExpr := .mul (127000, 12252303) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-127000, 12252303) e34
  let e36 : LowMeanIntegerExpr := .add (6891415140977, 122523030000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (6892640371277, 122523030000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-6891415140977, 122523030000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0314 : LowMeanDirectSeedInput :=
  { record := 314, positions := [{ j := 1, mode := 0, left := 675, right := 0 }, { j := 2, mode := 0, left := 676, right := 0 }, { j := 5, mode := 0, left := 677, right := 0 }, { j := 6, mode := 0, left := 678, right := 0 }], target := { R := 6, expr := lowMeanSeedTargetExpr0314 } }

noncomputable def lowMeanSeedTargetExpr0315 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (61769, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (2919, 5000000)
  let e3 : LowMeanIntegerExpr := .atom (7, 1)
  let e4 : LowMeanIntegerExpr := .atom (21, 2)
  let e5 : LowMeanIntegerExpr := .neg (-21, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-7, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-20433, 10000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (597257, 10000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (143, 125000)
  let e10 : LowMeanIntegerExpr := .pow (49, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (7007, 500000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-7007, 500000) e11
  let e13 : LowMeanIntegerExpr := .add (457117, 10000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (22517, 630000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (51315371, 630000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (889, 1000)
  let e33 : LowMeanIntegerExpr := .pow (10000000, 1801088541) e21 7
  let e34 : LowMeanIntegerExpr := .mul (1270000, 257298363) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1270000, 257298363) e34
  let e36 : LowMeanIntegerExpr := .add (196877158016471, 2572983630000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (196902887852771, 2572983630000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-196877158016471, 2572983630000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0315 : LowMeanDirectSeedInput :=
  { record := 315, positions := [{ j := 2, mode := 0, left := 679, right := 0 }, { j := 6, mode := 0, left := 680, right := 0 }], target := { R := 7, expr := lowMeanSeedTargetExpr0315 } }

noncomputable def lowMeanSeedTargetExpr0316 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (61769, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (2919, 5000000)
  let e3 : LowMeanIntegerExpr := .atom (8, 1)
  let e4 : LowMeanIntegerExpr := .atom (21, 2)
  let e5 : LowMeanIntegerExpr := .neg (-21, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-5, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-2919, 2000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (120619, 2000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (143, 125000)
  let e10 : LowMeanIntegerExpr := .pow (25, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (143, 20000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-143, 20000) e11
  let e13 : LowMeanIntegerExpr := .add (106319, 2000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (22517, 551250) e29 e3
  let e31 : LowMeanIntegerExpr := .add (82913879, 882000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (889, 1000)
  let e33 : LowMeanIntegerExpr := .pow (100000000, 37822859361) e21 8
  let e34 : LowMeanIntegerExpr := .mul (12700000, 5403265623) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-12700000, 5403265623) e34
  let e36 : LowMeanIntegerExpr := .add (990485968413337, 10806531246000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (990594033725797, 10806531246000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-990485968413337, 10806531246000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0316 : LowMeanDirectSeedInput :=
  { record := 316, positions := [{ j := 3, mode := 0, left := 681, right := 0 }, { j := 6, mode := 0, left := 682, right := 0 }, { j := 7, mode := 0, left := 683, right := 0 }], target := { R := 8, expr := lowMeanSeedTargetExpr0316 } }

noncomputable def lowMeanSeedTargetExpr0317 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (61769, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (2919, 5000000)
  let e3 : LowMeanIntegerExpr := .atom (9, 1)
  let e4 : LowMeanIntegerExpr := .atom (21, 2)
  let e5 : LowMeanIntegerExpr := .neg (-21, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-3, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-8757, 10000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (608933, 10000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (143, 125000)
  let e10 : LowMeanIntegerExpr := .pow (9, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1287, 500000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1287, 500000) e11
  let e13 : LowMeanIntegerExpr := .add (583193, 10000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (22517, 490000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (51093457, 490000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (889, 1000)
  let e33 : LowMeanIntegerExpr := .pow (1000000000, 794280046581) e21 9
  let e34 : LowMeanIntegerExpr := .mul (127000000, 113468578083) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-127000000, 113468578083) e34
  let e36 : LowMeanIntegerExpr := .add (117046365614998019, 1134685780830000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (117057712472806319, 1134685780830000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-117046365614998019, 1134685780830000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0317 : LowMeanDirectSeedInput :=
  { record := 317, positions := [{ j := 3, mode := 0, left := 684, right := 0 }, { j := 7, mode := 0, left := 685, right := 0 }], target := { R := 9, expr := lowMeanSeedTargetExpr0317 } }

noncomputable def lowMeanSeedTargetExpr0318 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (61769, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (2919, 5000000)
  let e3 : LowMeanIntegerExpr := .atom (10, 1)
  let e4 : LowMeanIntegerExpr := .atom (21, 2)
  let e5 : LowMeanIntegerExpr := .neg (-21, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-1, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-2919, 10000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (614771, 10000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (143, 125000)
  let e10 : LowMeanIntegerExpr := .pow (1, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (143, 500000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-143, 500000) e11
  let e13 : LowMeanIntegerExpr := .add (611911, 10000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (22517, 441000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (495022751, 4410000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (889, 1000)
  let e33 : LowMeanIntegerExpr := .pow (10000000000, 16679880978201) e21 10
  let e34 : LowMeanIntegerExpr := .mul (1270000000, 2382840139743) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1270000000, 2382840139743) e34
  let e36 : LowMeanIntegerExpr := .add (2662039413081188873, 23828401397430000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (2662277697095163173, 23828401397430000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-2662039413081188873, 23828401397430000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0318 : LowMeanDirectSeedInput :=
  { record := 318, positions := [{ j := 4, mode := 0, left := 686, right := 0 }, { j := 7, mode := 0, left := 687, right := 0 }, { j := 8, mode := 0, left := 688, right := 0 }], target := { R := 10, expr := lowMeanSeedTargetExpr0318 } }

noncomputable def lowMeanSeedTargetExpr0319 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (61769, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (2919, 5000000)
  let e3 : LowMeanIntegerExpr := .atom (11, 1)
  let e4 : LowMeanIntegerExpr := .atom (21, 2)
  let e5 : LowMeanIntegerExpr := .neg (-21, 2) e4
  let e6 : LowMeanIntegerExpr := .add (1, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (2919, 10000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (620609, 10000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (143, 125000)
  let e10 : LowMeanIntegerExpr := .pow (1, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (143, 500000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-143, 500000) e11
  let e13 : LowMeanIntegerExpr := .add (617749, 10000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (247687, 4410000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (520114309, 4410000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (889, 1000)
  let e33 : LowMeanIntegerExpr := .pow (100000000000, 350277500542221) e21 11
  let e34 : LowMeanIntegerExpr := .mul (12700000000, 50039642934603) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-12700000000, 50039642934603) e34
  let e36 : LowMeanIntegerExpr := .add (58889631082852089647, 500396429346030000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (58894635047145549947, 500396429346030000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-58889631082852089647, 500396429346030000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0319 : LowMeanDirectSeedInput :=
  { record := 319, positions := [{ j := 5, mode := 0, left := 689, right := 0 }, { j := 7, mode := 0, left := 690, right := 0 }, { j := 8, mode := 0, left := 691, right := 0 }], target := { R := 11, expr := lowMeanSeedTargetExpr0319 } }

noncomputable def lowMeanSeedGroup0304 : List LowMeanDirectSeedInput := [lowMeanSeedRecord0304, lowMeanSeedRecord0305, lowMeanSeedRecord0306, lowMeanSeedRecord0307, lowMeanSeedRecord0308, lowMeanSeedRecord0309, lowMeanSeedRecord0310, lowMeanSeedRecord0311, lowMeanSeedRecord0312, lowMeanSeedRecord0313, lowMeanSeedRecord0314, lowMeanSeedRecord0315, lowMeanSeedRecord0316, lowMeanSeedRecord0317, lowMeanSeedRecord0318, lowMeanSeedRecord0319]

end Erdos993Lean.Analytic.V213
