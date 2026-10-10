module

public import Erdos993Lean.Analytic.V213.LowMeanCoreAll
public import Erdos993Lean.Analytic.V213.LowMeanData.Seed0368
public import Erdos993Lean.Analytic.V213.LowMeanIntegerExpr
public import Erdos993Lean.Analytic.V213.LowMeanSeedGeometry
public import Erdos993Lean.Analytic.V213.LowMeanWidthData
public import Erdos993Lean.Ceiling.Prefix
public import Erdos993Lean.Ceiling.Statement

/-! Exact core/budget keys and equation-51 targets for the direct fibers. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanSeedTargetExpr0480 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e2 : LowMeanIntegerExpr := .atom (26, 78125)
  let e3 : LowMeanIntegerExpr := .atom (5, 1)
  let e4 : LowMeanIntegerExpr := .atom (189, 4)
  let e5 : LowMeanIntegerExpr := .neg (-189, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-169, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-2197, 156250) e2 e6
  let e8 : LowMeanIntegerExpr := .add (-41471, 10000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e10 : LowMeanIntegerExpr := .pow (28561, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (36929373, 1600000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-36929373, 1600000000) e11
  let e13 : LowMeanIntegerExpr := .add (-43564733, 1600000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (2063, 8450000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-7296423877, 270400000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (328000, 1)
  let e33 : LowMeanIntegerExpr := .pow (3125, 371293) e21 5
  let e34 : LowMeanIntegerExpr := .mul (1025000000, 371293) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1025000000, 371293) e34
  let e36 : LowMeanIntegerExpr := .add (-1640016030243257769, 594068800000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-1640016024302569769, 594068800000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (1640016030243257769, 594068800000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0480 : LowMeanDirectSeedInput :=
  { record := 480, positions := [], target := { R := 5, expr := lowMeanSeedTargetExpr0480 } }

noncomputable def lowMeanSeedTargetExpr0481 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e2 : LowMeanIntegerExpr := .atom (26, 78125)
  let e3 : LowMeanIntegerExpr := .atom (6, 1)
  let e4 : LowMeanIntegerExpr := .atom (189, 4)
  let e5 : LowMeanIntegerExpr := .neg (-189, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-165, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-429, 31250) e2 e6
  let e8 : LowMeanIntegerExpr := .add (-38143, 10000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e10 : LowMeanIntegerExpr := .pow (27225, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1408077, 64000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1408077, 64000000) e11
  let e13 : LowMeanIntegerExpr := .add (-8260961, 320000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (6189, 21125000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-1380258569, 54080000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (328000, 1)
  let e33 : LowMeanIntegerExpr := .pow (15625, 4826809) e21 6
  let e34 : LowMeanIntegerExpr := .mul (5125000000, 4826809) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-5125000000, 4826809) e34
  let e36 : LowMeanIntegerExpr := .add (-1640039421564989209, 1544578880000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-1640039406119200409, 1544578880000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (1640039421564989209, 1544578880000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0481 : LowMeanDirectSeedInput :=
  { record := 481, positions := [], target := { R := 6, expr := lowMeanSeedTargetExpr0481 } }

noncomputable def lowMeanSeedTargetExpr0482 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e2 : LowMeanIntegerExpr := .atom (26, 78125)
  let e3 : LowMeanIntegerExpr := .atom (7, 1)
  let e4 : LowMeanIntegerExpr := .atom (189, 4)
  let e5 : LowMeanIntegerExpr := .neg (-189, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-161, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-2093, 156250) e2 e6
  let e8 : LowMeanIntegerExpr := .add (-6963, 2000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e10 : LowMeanIntegerExpr := .pow (25921, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (33515853, 1600000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-33515853, 1600000000) e11
  let e13 : LowMeanIntegerExpr := .add (-39086253, 1600000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (14441, 42250000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-6513154357, 270400000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (328000, 1)
  let e33 : LowMeanIntegerExpr := .pow (78125, 62748517) e21 7
  let e34 : LowMeanIntegerExpr := .mul (25625000000, 62748517) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-25625000000, 62748517) e34
  let e36 : LowMeanIntegerExpr := .add (-41002418288620673601, 100397627200000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-41002417284644401601, 100397627200000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (41002418288620673601, 100397627200000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0482 : LowMeanDirectSeedInput :=
  { record := 482, positions := [], target := { R := 7, expr := lowMeanSeedTargetExpr0482 } }

noncomputable def lowMeanSeedTargetExpr0483 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e2 : LowMeanIntegerExpr := .atom (26, 78125)
  let e3 : LowMeanIntegerExpr := .atom (8, 1)
  let e4 : LowMeanIntegerExpr := .atom (189, 4)
  let e5 : LowMeanIntegerExpr := .neg (-189, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-157, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-2041, 156250) e2 e6
  let e8 : LowMeanIntegerExpr := .add (-31487, 10000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e10 : LowMeanIntegerExpr := .pow (24649, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (31871157, 1600000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-31871157, 1600000000) e11
  let e13 : LowMeanIntegerExpr := .add (-36909077, 1600000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (2063, 5281250) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-6132008413, 270400000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (328000, 1)
  let e33 : LowMeanIntegerExpr := .pow (390625, 815730721) e21 8
  let e34 : LowMeanIntegerExpr := .mul (128125000000, 815730721) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-128125000000, 815730721) e34
  let e36 : LowMeanIntegerExpr := .add (-205029598033395944117, 1305169153600000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-205029584981704408117, 1305169153600000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (205029598033395944117, 1305169153600000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0483 : LowMeanDirectSeedInput :=
  { record := 483, positions := [], target := { R := 8, expr := lowMeanSeedTargetExpr0483 } }

noncomputable def lowMeanSeedTargetExpr0484 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e2 : LowMeanIntegerExpr := .atom (26, 78125)
  let e3 : LowMeanIntegerExpr := .atom (9, 1)
  let e4 : LowMeanIntegerExpr := .atom (189, 4)
  let e5 : LowMeanIntegerExpr := .neg (-189, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-153, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1989, 156250) e2 e6
  let e8 : LowMeanIntegerExpr := .add (-28159, 10000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e10 : LowMeanIntegerExpr := .pow (23409, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (30267837, 1600000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-30267837, 1600000000) e11
  let e13 : LowMeanIntegerExpr := .add (-34773277, 1600000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (18567, 42250000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-5757855013, 270400000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (328000, 1)
  let e33 : LowMeanIntegerExpr := .pow (1953125, 10604499373) e21 9
  let e34 : LowMeanIntegerExpr := .mul (640625000000, 10604499373) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-640625000000, 10604499373) e34
  let e36 : LowMeanIntegerExpr := .add (-1025361296863166765721, 16967198996800000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-1025361127191176797721, 16967198996800000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (1025361296863166765721, 16967198996800000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0484 : LowMeanDirectSeedInput :=
  { record := 484, positions := [], target := { R := 9, expr := lowMeanSeedTargetExpr0484 } }

noncomputable def lowMeanSeedTargetExpr0485 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e2 : LowMeanIntegerExpr := .atom (26, 78125)
  let e3 : LowMeanIntegerExpr := .atom (10, 1)
  let e4 : LowMeanIntegerExpr := .atom (189, 4)
  let e5 : LowMeanIntegerExpr := .neg (-189, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-149, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1937, 156250) e2 e6
  let e8 : LowMeanIntegerExpr := .add (-24831, 10000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e10 : LowMeanIntegerExpr := .pow (22201, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (28705893, 1600000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-28705893, 1600000000) e11
  let e13 : LowMeanIntegerExpr := .add (-32678853, 1600000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (2063, 4225000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-5390694157, 270400000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (328000, 1)
  let e33 : LowMeanIntegerExpr := .pow (9765625, 137858491849) e21 10
  let e34 : LowMeanIntegerExpr := .mul (3203125000000, 137858491849) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-3203125000000, 137858491849) e34
  let e36 : LowMeanIntegerExpr := .add (-5129397354831380097197, 220573586958400000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-5129395149095510513197, 220573586958400000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (5129397354831380097197, 220573586958400000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0485 : LowMeanDirectSeedInput :=
  { record := 485, positions := [], target := { R := 10, expr := lowMeanSeedTargetExpr0485 } }

noncomputable def lowMeanSeedTargetExpr0486 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e2 : LowMeanIntegerExpr := .atom (26, 78125)
  let e3 : LowMeanIntegerExpr := .atom (11, 1)
  let e4 : LowMeanIntegerExpr := .atom (189, 4)
  let e5 : LowMeanIntegerExpr := .neg (-189, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-145, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-377, 31250) e2 e6
  let e8 : LowMeanIntegerExpr := .add (-21503, 10000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e10 : LowMeanIntegerExpr := .pow (21025, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1087413, 64000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1087413, 64000000) e11
  let e13 : LowMeanIntegerExpr := .add (-6125161, 320000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (22693, 42250000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-1006105169, 54080000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (328000, 1)
  let e33 : LowMeanIntegerExpr := .pow (48828125, 1792160394037) e21 11
  let e34 : LowMeanIntegerExpr := .mul (16015625000000, 1792160394037) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-16015625000000, 1792160394037) e34
  let e36 : LowMeanIntegerExpr := .add (-5135669241633832559037, 573491326091840000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-5135663506720571640637, 573491326091840000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (5135669241633832559037, 573491326091840000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0486 : LowMeanDirectSeedInput :=
  { record := 486, positions := [], target := { R := 11, expr := lowMeanSeedTargetExpr0486 } }

noncomputable def lowMeanSeedTargetExpr0487 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e2 : LowMeanIntegerExpr := .atom (26, 78125)
  let e3 : LowMeanIntegerExpr := .atom (12, 1)
  let e4 : LowMeanIntegerExpr := .atom (189, 4)
  let e5 : LowMeanIntegerExpr := .neg (-189, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-141, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1833, 156250) e2 e6
  let e8 : LowMeanIntegerExpr := .add (-727, 400000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e10 : LowMeanIntegerExpr := .pow (19881, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (25706133, 1600000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-25706133, 1600000000) e11
  let e13 : LowMeanIntegerExpr := .add (-28614133, 1600000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (6189, 10562500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-4677350077, 270400000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (328000, 1)
  let e33 : LowMeanIntegerExpr := .pow (244140625, 23298085122481) e21 12
  let e34 : LowMeanIntegerExpr := .mul (80078125000000, 23298085122481) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-80078125000000, 23298085122481) e34
  let e36 : LowMeanIntegerExpr := .add (-128769812427465024022373, 37276936195969600000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-128769439658103064326373, 37276936195969600000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (128769812427465024022373, 37276936195969600000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0487 : LowMeanDirectSeedInput :=
  { record := 487, positions := [], target := { R := 12, expr := lowMeanSeedTargetExpr0487 } }

noncomputable def lowMeanSeedTargetExpr0488 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e2 : LowMeanIntegerExpr := .atom (26, 78125)
  let e3 : LowMeanIntegerExpr := .atom (13, 1)
  let e4 : LowMeanIntegerExpr := .atom (189, 4)
  let e5 : LowMeanIntegerExpr := .neg (-189, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-137, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1781, 156250) e2 e6
  let e8 : LowMeanIntegerExpr := .add (-14847, 10000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e10 : LowMeanIntegerExpr := .pow (18769, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (24268317, 1600000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-24268317, 1600000000) e11
  let e13 : LowMeanIntegerExpr := .add (-26643837, 1600000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (2063, 3250000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-333166681, 20800000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (328000, 1)
  let e33 : LowMeanIntegerExpr := .pow (1220703125, 302875106592253) e21 13
  let e34 : LowMeanIntegerExpr := .mul (400390625000000, 302875106592253) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-400390625000000, 302875106592253) e34
  let e36 : LowMeanIntegerExpr := .add (-648387145693912473255561, 484600170547604800000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-648382299692206997207561, 484600170547604800000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (648387145693912473255561, 484600170547604800000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0488 : LowMeanDirectSeedInput :=
  { record := 488, positions := [], target := { R := 13, expr := lowMeanSeedTargetExpr0488 } }

noncomputable def lowMeanSeedTargetExpr0489 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e2 : LowMeanIntegerExpr := .atom (26, 78125)
  let e3 : LowMeanIntegerExpr := .atom (14, 1)
  let e4 : LowMeanIntegerExpr := .atom (189, 4)
  let e5 : LowMeanIntegerExpr := .neg (-189, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-133, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1729, 156250) e2 e6
  let e8 : LowMeanIntegerExpr := .add (-11519, 10000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e10 : LowMeanIntegerExpr := .pow (17689, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (22871877, 1600000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-22871877, 1600000000) e11
  let e13 : LowMeanIntegerExpr := .add (-24714917, 1600000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (14441, 21125000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-3991976173, 270400000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (328000, 1)
  let e33 : LowMeanIntegerExpr := .pow (6103515625, 3937376385699289) e21 14
  let e34 : LowMeanIntegerExpr := .mul (2001953125000000, 3937376385699289) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-2001953125000000, 3937376385699289) e34
  let e36 : LowMeanIntegerExpr := .add (-3296130400685469938645213, 6299802217118862400000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-3296067402663298750021213, 6299802217118862400000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (3296130400685469938645213, 6299802217118862400000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0489 : LowMeanDirectSeedInput :=
  { record := 489, positions := [], target := { R := 14, expr := lowMeanSeedTargetExpr0489 } }

noncomputable def lowMeanSeedTargetExpr0490 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e2 : LowMeanIntegerExpr := .atom (26, 78125)
  let e3 : LowMeanIntegerExpr := .atom (15, 1)
  let e4 : LowMeanIntegerExpr := .atom (189, 4)
  let e5 : LowMeanIntegerExpr := .neg (-189, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-129, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1677, 156250) e2 e6
  let e8 : LowMeanIntegerExpr := .add (-8191, 10000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e10 : LowMeanIntegerExpr := .pow (16641, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (21516813, 1600000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-21516813, 1600000000) e11
  let e13 : LowMeanIntegerExpr := .add (-22827373, 1600000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (6189, 8450000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-3659778037, 270400000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (328000, 1)
  let e33 : LowMeanIntegerExpr := .pow (30517578125, 51185893014090757) e21 15
  let e34 : LowMeanIntegerExpr := .mul (10009765625000000, 51185893014090757) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-10009765625000000, 51185893014090757) e34
  let e36 : LowMeanIntegerExpr := .add (-17124080663060361443747361, 81897428822545211200000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-17123261688772135991635361, 81897428822545211200000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (17124080663060361443747361, 81897428822545211200000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0490 : LowMeanDirectSeedInput :=
  { record := 490, positions := [], target := { R := 15, expr := lowMeanSeedTargetExpr0490 } }

noncomputable def lowMeanSeedTargetExpr0491 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e2 : LowMeanIntegerExpr := .atom (26, 78125)
  let e3 : LowMeanIntegerExpr := .atom (16, 1)
  let e4 : LowMeanIntegerExpr := .atom (189, 4)
  let e5 : LowMeanIntegerExpr := .neg (-189, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-125, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-13, 1250) e2 e6
  let e8 : LowMeanIntegerExpr := .add (-4863, 10000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e10 : LowMeanIntegerExpr := .pow (15625, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1293, 102400) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1293, 102400) e11
  let e13 : LowMeanIntegerExpr := .add (-4196241, 320000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (2063, 2640625) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-666914489, 54080000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (328000, 1)
  let e33 : LowMeanIntegerExpr := .pow (152587890625, 665416609183179841) e21 16
  let e34 : LowMeanIntegerExpr := .mul (50048828125000000, 665416609183179841) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-50048828125000000, 665416609183179841) e34
  let e36 : LowMeanIntegerExpr := .add (-18641518360269308231098321, 212933314938617549120000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-18639389027119922055607121, 212933314938617549120000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (18641518360269308231098321, 212933314938617549120000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0491 : LowMeanDirectSeedInput :=
  { record := 491, positions := [], target := { R := 16, expr := lowMeanSeedTargetExpr0491 } }

noncomputable def lowMeanSeedTargetExpr0492 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e2 : LowMeanIntegerExpr := .atom (26, 78125)
  let e3 : LowMeanIntegerExpr := .atom (17, 1)
  let e4 : LowMeanIntegerExpr := .atom (189, 4)
  let e5 : LowMeanIntegerExpr := .neg (-189, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-121, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1573, 156250) e2 e6
  let e8 : LowMeanIntegerExpr := .add (-307, 2000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e10 : LowMeanIntegerExpr := .pow (14641, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (18930813, 1600000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-18930813, 1600000000) e11
  let e13 : LowMeanIntegerExpr := .add (-19176413, 1600000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (35071, 42250000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-3016359397, 270400000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (328000, 1)
  let e33 : LowMeanIntegerExpr := .pow (762939453125, 8650415919381337933) e21 17
  let e34 : LowMeanIntegerExpr := .mul (250244140625000000, 8650415919381337933) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-250244140625000000, 8650415919381337933) e34
  let e36 : LowMeanIntegerExpr := .add (-554785674386889308287793529, 13840665471010140692800000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-554647267732179206880865529, 13840665471010140692800000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (554785674386889308287793529, 13840665471010140692800000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0492 : LowMeanDirectSeedInput :=
  { record := 492, positions := [], target := { R := 17, expr := lowMeanSeedTargetExpr0492 } }

noncomputable def lowMeanSeedTargetExpr0493 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e2 : LowMeanIntegerExpr := .atom (26, 78125)
  let e3 : LowMeanIntegerExpr := .atom (18, 1)
  let e4 : LowMeanIntegerExpr := .atom (189, 4)
  let e5 : LowMeanIntegerExpr := .neg (-189, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-117, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1521, 156250) e2 e6
  let e8 : LowMeanIntegerExpr := .add (1793, 10000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e10 : LowMeanIntegerExpr := .pow (13689, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (17699877, 1600000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-17699877, 1600000000) e11
  let e13 : LowMeanIntegerExpr := .add (-17412997, 1600000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (18567, 21125000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-2705138893, 270400000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (328000, 1)
  let e33 : LowMeanIntegerExpr := .pow (3814697265625, 112455406951957393129) e21 18
  let e34 : LowMeanIntegerExpr := .mul (1251220703125000000, 112455406951957393129) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1251220703125000000, 112455406951957393129) e34
  let e36 : LowMeanIntegerExpr := .add (-3801997474549600749302656013, 179928651123131829006400000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-3800198188038369431012592013, 179928651123131829006400000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (3801997474549600749302656013, 179928651123131829006400000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0493 : LowMeanDirectSeedInput :=
  { record := 493, positions := [], target := { R := 18, expr := lowMeanSeedTargetExpr0493 } }

noncomputable def lowMeanSeedTargetExpr0494 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e2 : LowMeanIntegerExpr := .atom (26, 78125)
  let e3 : LowMeanIntegerExpr := .atom (19, 1)
  let e4 : LowMeanIntegerExpr := .atom (189, 4)
  let e5 : LowMeanIntegerExpr := .neg (-189, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-113, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1469, 156250) e2 e6
  let e8 : LowMeanIntegerExpr := .add (5121, 10000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e10 : LowMeanIntegerExpr := .pow (12769, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (16510317, 1600000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-16510317, 1600000000) e11
  let e13 : LowMeanIntegerExpr := .add (-15690957, 1600000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (39197, 42250000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-2400910933, 270400000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (328000, 1)
  let e33 : LowMeanIntegerExpr := .pow (19073486328125, 1461920290375446110677) e21 19
  let e34 : LowMeanIntegerExpr := .mul (6256103515625000000, 1461920290375446110677) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-6256103515625000000, 1461920290375446110677) e34
  let e36 : LowMeanIntegerExpr := .add (-30778643780839900839507321489, 2339072464600713777083200000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-30755253056193893701736489489, 2339072464600713777083200000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (30778643780839900839507321489, 2339072464600713777083200000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0494 : LowMeanDirectSeedInput :=
  { record := 494, positions := [], target := { R := 19, expr := lowMeanSeedTargetExpr0494 } }

noncomputable def lowMeanSeedTargetExpr0495 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e2 : LowMeanIntegerExpr := .atom (26, 78125)
  let e3 : LowMeanIntegerExpr := .atom (20, 1)
  let e4 : LowMeanIntegerExpr := .atom (189, 4)
  let e5 : LowMeanIntegerExpr := .neg (-189, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-109, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1417, 156250) e2 e6
  let e8 : LowMeanIntegerExpr := .add (8449, 10000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e10 : LowMeanIntegerExpr := .pow (11881, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (15362133, 1600000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-15362133, 1600000000) e11
  let e13 : LowMeanIntegerExpr := .add (-14010293, 1600000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (2063, 2112500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-2103675517, 270400000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (328000, 1)
  let e33 : LowMeanIntegerExpr := .pow (95367431640625, 19004963774880799438801) e21 20
  let e34 : LowMeanIntegerExpr := .mul (31280517578125000000, 19004963774880799438801) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-31280517578125000000, 19004963774880799438801) e34
  let e36 : LowMeanIntegerExpr := .add (-286618514484104363152621322693, 30407942039809279102081600000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-286314435063706270361600506693, 30407942039809279102081600000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (286618514484104363152621322693, 30407942039809279102081600000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0495 : LowMeanDirectSeedInput :=
  { record := 495, positions := [], target := { R := 20, expr := lowMeanSeedTargetExpr0495 } }

noncomputable def lowMeanSeedGroup0480 : List LowMeanDirectSeedInput := [lowMeanSeedRecord0480, lowMeanSeedRecord0481, lowMeanSeedRecord0482, lowMeanSeedRecord0483, lowMeanSeedRecord0484, lowMeanSeedRecord0485, lowMeanSeedRecord0486, lowMeanSeedRecord0487, lowMeanSeedRecord0488, lowMeanSeedRecord0489, lowMeanSeedRecord0490, lowMeanSeedRecord0491, lowMeanSeedRecord0492, lowMeanSeedRecord0493, lowMeanSeedRecord0494, lowMeanSeedRecord0495]

end Erdos993Lean.Analytic.V213
