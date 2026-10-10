module

public import Erdos993Lean.Analytic.V213.LowMeanCoreAll
public import Erdos993Lean.Analytic.V213.LowMeanData.Seed0416
public import Erdos993Lean.Analytic.V213.LowMeanIntegerExpr
public import Erdos993Lean.Analytic.V213.LowMeanSeedGeometry
public import Erdos993Lean.Analytic.V213.LowMeanWidthData
public import Erdos993Lean.Ceiling.Prefix
public import Erdos993Lean.Ceiling.Statement

/-! Exact core/budget keys and equation-51 targets for the direct fibers. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanSeedTargetExpr0496 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e2 : LowMeanIntegerExpr := .atom (26, 78125)
  let e3 : LowMeanIntegerExpr := .atom (21, 1)
  let e4 : LowMeanIntegerExpr := .atom (189, 4)
  let e5 : LowMeanIntegerExpr := .neg (-189, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-105, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-273, 31250) e2 e6
  let e8 : LowMeanIntegerExpr := .add (11777, 10000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e10 : LowMeanIntegerExpr := .pow (11025, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (570213, 64000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-570213, 64000000) e11
  let e13 : LowMeanIntegerExpr := .add (-2474201, 320000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (43323, 42250000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-362686529, 54080000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (328000, 1)
  let e33 : LowMeanIntegerExpr := .pow (476837158203125, 247064529073450392704413) e21 21
  let e34 : LowMeanIntegerExpr := .mul (156402587890625000000, 247064529073450392704413) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-156402587890625000000, 247064529073450392704413) e34
  let e36 : LowMeanIntegerExpr := .add (-580267623915942656707990970133, 79060649303504125665412160000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-579477017422907615451336848533, 79060649303504125665412160000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (580267623915942656707990970133, 79060649303504125665412160000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0496 : LowMeanDirectSeedInput :=
  { record := 496, positions := [], target := { R := 21, expr := lowMeanSeedTargetExpr0496 } }

noncomputable def lowMeanSeedTargetExpr0497 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e2 : LowMeanIntegerExpr := .atom (26, 78125)
  let e3 : LowMeanIntegerExpr := .atom (22, 1)
  let e4 : LowMeanIntegerExpr := .atom (189, 4)
  let e5 : LowMeanIntegerExpr := .neg (-189, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-101, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1313, 156250) e2 e6
  let e8 : LowMeanIntegerExpr := .add (3021, 2000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e10 : LowMeanIntegerExpr := .pow (10201, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (13189893, 1600000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-13189893, 1600000000) e11
  let e13 : LowMeanIntegerExpr := .add (-10773093, 1600000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (22693, 21125000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-1530182317, 270400000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (328000, 1)
  let e33 : LowMeanIntegerExpr := .pow (2384185791015625, 3211838877954855105157369) e21 22
  let e34 : LowMeanIntegerExpr := .mul (782012939453125000000, 3211838877954855105157369) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-782012939453125000000, 3211838877954855105157369) e34
  let e36 : LowMeanIntegerExpr := .add (-30332280206673168084076813881917, 5138942204727768168251790400000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-30280890784625890402394295977917, 5138942204727768168251790400000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (30332280206673168084076813881917, 5138942204727768168251790400000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0497 : LowMeanDirectSeedInput :=
  { record := 497, positions := [], target := { R := 22, expr := lowMeanSeedTargetExpr0497 } }

noncomputable def lowMeanSeedTargetExpr0498 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e2 : LowMeanIntegerExpr := .atom (26, 78125)
  let e3 : LowMeanIntegerExpr := .atom (23, 1)
  let e4 : LowMeanIntegerExpr := .atom (189, 4)
  let e5 : LowMeanIntegerExpr := .neg (-189, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-97, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1261, 156250) e2 e6
  let e8 : LowMeanIntegerExpr := .add (18433, 10000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e10 : LowMeanIntegerExpr := .pow (9409, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (12165837, 1600000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-12165837, 1600000000) e11
  let e13 : LowMeanIntegerExpr := .add (-9216557, 1600000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (47449, 42250000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-1253924533, 270400000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (328000, 1)
  let e33 : LowMeanIntegerExpr := .pow (11920928955078125, 41753905413413116367045797) e21 23
  let e34 : LowMeanIntegerExpr := .mul (3910064697265625000000, 41753905413413116367045797) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-3910064697265625000000, 41753905413413116367045797) e34
  let e36 : LowMeanIntegerExpr := .add (-316056377754916206370547678064129, 66806248661460986187273275200000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-315388315268301596508674945312129, 66806248661460986187273275200000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (316056377754916206370547678064129, 66806248661460986187273275200000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0498 : LowMeanDirectSeedInput :=
  { record := 498, positions := [], target := { R := 23, expr := lowMeanSeedTargetExpr0498 } }

noncomputable def lowMeanSeedTargetExpr0499 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e2 : LowMeanIntegerExpr := .atom (26, 78125)
  let e3 : LowMeanIntegerExpr := .atom (24, 1)
  let e4 : LowMeanIntegerExpr := .atom (189, 4)
  let e5 : LowMeanIntegerExpr := .neg (-189, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-93, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1209, 156250) e2 e6
  let e8 : LowMeanIntegerExpr := .add (21761, 10000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e10 : LowMeanIntegerExpr := .pow (8649, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (11183157, 1600000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-11183157, 1600000000) e11
  let e13 : LowMeanIntegerExpr := .add (-7701397, 1600000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (6189, 5281250) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-984659293, 270400000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (328000, 1)
  let e33 : LowMeanIntegerExpr := .pow (59604644775390625, 542800770374370512771595361) e21 24
  let e34 : LowMeanIntegerExpr := .mul (19550323486328125000000, 542800770374370512771595361) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-19550323486328125000000, 542800770374370512771595361) e34
  let e36 : LowMeanIntegerExpr := .add (-3193847516375065913761695613280117, 868481232598992820434552577600000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-3185162704049075985557350087504117, 868481232598992820434552577600000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (3193847516375065913761695613280117, 868481232598992820434552577600000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0499 : LowMeanDirectSeedInput :=
  { record := 499, positions := [], target := { R := 24, expr := lowMeanSeedTargetExpr0499 } }

noncomputable def lowMeanSeedTargetExpr0500 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e2 : LowMeanIntegerExpr := .atom (26, 78125)
  let e3 : LowMeanIntegerExpr := .atom (25, 1)
  let e4 : LowMeanIntegerExpr := .atom (189, 4)
  let e5 : LowMeanIntegerExpr := .neg (-189, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-89, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1157, 156250) e2 e6
  let e8 : LowMeanIntegerExpr := .add (25089, 10000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e10 : LowMeanIntegerExpr := .pow (7921, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (10241853, 1600000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-10241853, 1600000000) e11
  let e13 : LowMeanIntegerExpr := .add (-6227613, 1600000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (2063, 1690000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-722386597, 270400000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (328000, 1)
  let e33 : LowMeanIntegerExpr := .pow (298023223876953125, 7056410014866816666030739693) e21 25
  let e34 : LowMeanIntegerExpr := .mul (97751617431640625000000, 7056410014866816666030739693) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-97751617431640625000000, 7056410014866816666030739693) e34
  let e36 : LowMeanIntegerExpr := .add (-30318864230946004287555216237982809, 11290256023786906665649183508800000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-30205961670708135220898724402894809, 11290256023786906665649183508800000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (30318864230946004287555216237982809, 11290256023786906665649183508800000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0500 : LowMeanDirectSeedInput :=
  { record := 500, positions := [], target := { R := 25, expr := lowMeanSeedTargetExpr0500 } }

noncomputable def lowMeanSeedTargetExpr0501 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e2 : LowMeanIntegerExpr := .atom (26, 78125)
  let e3 : LowMeanIntegerExpr := .atom (26, 1)
  let e4 : LowMeanIntegerExpr := .atom (189, 4)
  let e5 : LowMeanIntegerExpr := .neg (-189, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-85, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-221, 31250) e2 e6
  let e8 : LowMeanIntegerExpr := .add (28417, 10000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e10 : LowMeanIntegerExpr := .pow (7225, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (373677, 64000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-373677, 64000000) e11
  let e13 : LowMeanIntegerExpr := .add (-959041, 320000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (2063, 1625000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-7186253, 4160000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (328000, 1)
  let e33 : LowMeanIntegerExpr := .pow (1490116119384765625, 91733330193268616658399616009) e21 26
  let e34 : LowMeanIntegerExpr := .mul (488758087158203125000000, 91733330193268616658399616009) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-488758087158203125000000, 91733330193268616658399616009) e34
  let e36 : LowMeanIntegerExpr := .add (-50865550226457330866713401211040329, 29354665661845957330687877122880000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-50572003569838871293406522439811529, 29354665661845957330687877122880000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (50865550226457330866713401211040329, 29354665661845957330687877122880000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0501 : LowMeanDirectSeedInput :=
  { record := 501, positions := [], target := { R := 26, expr := lowMeanSeedTargetExpr0501 } }

noncomputable def lowMeanSeedTargetExpr0502 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e2 : LowMeanIntegerExpr := .atom (26, 78125)
  let e3 : LowMeanIntegerExpr := .atom (27, 1)
  let e4 : LowMeanIntegerExpr := .atom (189, 4)
  let e5 : LowMeanIntegerExpr := .neg (-189, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-81, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1053, 156250) e2 e6
  let e8 : LowMeanIntegerExpr := .add (6349, 2000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e10 : LowMeanIntegerExpr := .pow (6561, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (8483373, 1600000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-8483373, 1600000000) e11
  let e13 : LowMeanIntegerExpr := .add (-3404173, 1600000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (55701, 42250000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-218818837, 270400000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (328000, 1)
  let e33 : LowMeanIntegerExpr := .pow (7450580596923828125, 1192533292512492016559195008117) e21 27
  let e34 : LowMeanIntegerExpr := .mul (2443790435791015625000000, 1192533292512492016559195008117) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-2443790435791015625000000, 1192533292512492016559195008117) e34
  let e36 : LowMeanIntegerExpr := .add (-1547985497545575157753063865871997041, 1908053268019987226494712012987200000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-1528904964865375285488116745742125041, 1908053268019987226494712012987200000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (1547985497545575157753063865871997041, 1908053268019987226494712012987200000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0502 : LowMeanDirectSeedInput :=
  { record := 502, positions := [], target := { R := 27, expr := lowMeanSeedTargetExpr0502 } }

noncomputable def lowMeanSeedTargetExpr0503 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e2 : LowMeanIntegerExpr := .atom (26, 78125)
  let e3 : LowMeanIntegerExpr := .atom (28, 1)
  let e4 : LowMeanIntegerExpr := .atom (189, 4)
  let e5 : LowMeanIntegerExpr := .neg (-189, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-77, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1001, 156250) e2 e6
  let e8 : LowMeanIntegerExpr := .add (35073, 10000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e10 : LowMeanIntegerExpr := .pow (5929, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (7666197, 1600000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-7666197, 1600000000) e11
  let e13 : LowMeanIntegerExpr := .add (-2054517, 1600000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (14441, 10562500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (22476227, 270400000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (328000, 1)
  let e33 : LowMeanIntegerExpr := .pow (37252902984619140625, 15502932802662396215269535105521) e21 28
  let e34 : LowMeanIntegerExpr := .mul (12218952178955078125000000, 15502932802662396215269535105521) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-12218952178955078125000000, 15502932802662396215269535105521) e34
  let e36 : LowMeanIntegerExpr := .add (2042268829403531174990171226131118043, 24804692484259833944431256168833600000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (2290315754246129514434483787819454043, 24804692484259833944431256168833600000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-2042268829403531174990171226131118043, 24804692484259833944431256168833600000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0503 : LowMeanDirectSeedInput :=
  { record := 503, positions := [], target := { R := 28, expr := lowMeanSeedTargetExpr0503 } }

noncomputable def lowMeanSeedTargetExpr0504 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e2 : LowMeanIntegerExpr := .atom (26, 78125)
  let e3 : LowMeanIntegerExpr := .atom (29, 1)
  let e4 : LowMeanIntegerExpr := .atom (189, 4)
  let e5 : LowMeanIntegerExpr := .neg (-189, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-73, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-949, 156250) e2 e6
  let e8 : LowMeanIntegerExpr := .add (38401, 10000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e10 : LowMeanIntegerExpr := .pow (5329, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (6890397, 1600000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-6890397, 1600000000) e11
  let e13 : LowMeanIntegerExpr := .add (-746237, 1600000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (59827, 42250000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (256778747, 270400000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (328000, 1)
  let e33 : LowMeanIntegerExpr := .pow (186264514923095703125, 201538126434611150798503956371773) e21 29
  let e34 : LowMeanIntegerExpr := .mul (61094760894775390625000000, 201538126434611150798503956371773) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-61094760894775390625000000, 201538126434611150798503956371773) e34
  let e36 : LowMeanIntegerExpr := .add (306119452989710541234573345512938089399, 322461002295377841277606330194836800000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (309344063012664319647349408814886457399, 322461002295377841277606330194836800000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-306119452989710541234573345512938089399, 322461002295377841277606330194836800000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0504 : LowMeanDirectSeedInput :=
  { record := 504, positions := [], target := { R := 29, expr := lowMeanSeedTargetExpr0504 } }

noncomputable def lowMeanSeedTargetExpr0505 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e2 : LowMeanIntegerExpr := .atom (26, 78125)
  let e3 : LowMeanIntegerExpr := .atom (30, 1)
  let e4 : LowMeanIntegerExpr := .atom (189, 4)
  let e5 : LowMeanIntegerExpr := .neg (-189, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-69, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-897, 156250) e2 e6
  let e8 : LowMeanIntegerExpr := .add (41729, 10000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e10 : LowMeanIntegerExpr := .pow (4761, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (6155973, 1600000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-6155973, 1600000000) e11
  let e13 : LowMeanIntegerExpr := .add (520667, 1600000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (6189, 4225000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (484088723, 270400000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (328000, 1)
  let e33 : LowMeanIntegerExpr := .pow (931322574615478515625, 2619995643649944960380551432833049) e21 30
  let e34 : LowMeanIntegerExpr := .mul (305473804473876953125000000, 2619995643649944960380551432833049) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-305473804473876953125000000, 2619995643649944960380551432833049) e34
  let e36 : LowMeanIntegerExpr := .add (7504306185108492180844862350035331139683, 4191993029839911936608882292532878400000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (7546226115406891300210951172960659923683, 4191993029839911936608882292532878400000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-7504306185108492180844862350035331139683, 4191993029839911936608882292532878400000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0505 : LowMeanDirectSeedInput :=
  { record := 505, positions := [], target := { R := 30, expr := lowMeanSeedTargetExpr0505 } }

noncomputable def lowMeanSeedTargetExpr0506 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e2 : LowMeanIntegerExpr := .atom (26, 78125)
  let e3 : LowMeanIntegerExpr := .atom (31, 1)
  let e4 : LowMeanIntegerExpr := .atom (189, 4)
  let e5 : LowMeanIntegerExpr := .neg (-189, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-65, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-169, 31250) e2 e6
  let e8 : LowMeanIntegerExpr := .add (45057, 10000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e10 : LowMeanIntegerExpr := .pow (4225, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (218517, 64000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-218517, 64000000) e11
  let e13 : LowMeanIntegerExpr := .add (349239, 320000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (63953, 42250000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (140881231, 54080000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (328000, 1)
  let e33 : LowMeanIntegerExpr := .pow (4656612873077392578125, 34059943367449284484947168626829637) e21 31
  let e34 : LowMeanIntegerExpr := .mul (1527369022369384765625000000, 34059943367449284484947168626829637) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1527369022369384765625000000, 34059943367449284484947168626829637) e34
  let e36 : LowMeanIntegerExpr := .add (28392450587454501727694870332025673892563, 10899181877583771035183093960585483840000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (28501442406230339438046701271631528730963, 10899181877583771035183093960585483840000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-28392450587454501727694870332025673892563, 10899181877583771035183093960585483840000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0506 : LowMeanDirectSeedInput :=
  { record := 506, positions := [], target := { R := 31, expr := lowMeanSeedTargetExpr0506 } }

noncomputable def lowMeanSeedTargetExpr0507 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e2 : LowMeanIntegerExpr := .atom (26, 78125)
  let e3 : LowMeanIntegerExpr := .atom (32, 1)
  let e4 : LowMeanIntegerExpr := .atom (189, 4)
  let e5 : LowMeanIntegerExpr := .neg (-189, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-61, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-793, 156250) e2 e6
  let e8 : LowMeanIntegerExpr := .add (9677, 2000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e10 : LowMeanIntegerExpr := .pow (3721, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (4811253, 1600000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-4811253, 1600000000) e11
  let e13 : LowMeanIntegerExpr := .add (2930347, 1600000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (4126, 2640625) e29 e3
  let e31 : LowMeanIntegerExpr := .add (917731043, 270400000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (328000, 1)
  let e33 : LowMeanIntegerExpr := .pow (23283064365386962890625, 442779263776840698304313192148785281) e21 32
  let e34 : LowMeanIntegerExpr := .mul (7636845111846923828125000000, 442779263776840698304313192148785281) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-7636845111846923828125000000, 442779263776840698304313192148785281) e34
  let e36 : LowMeanIntegerExpr := .add (2404439115750141360304512143369018503640107, 708446822042945117286901107438056449600000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (2411523583970570811477381154443399068136107, 708446822042945117286901107438056449600000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-2404439115750141360304512143369018503640107, 708446822042945117286901107438056449600000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0507 : LowMeanDirectSeedInput :=
  { record := 507, positions := [], target := { R := 32, expr := lowMeanSeedTargetExpr0507 } }

noncomputable def lowMeanSeedTargetExpr0508 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e2 : LowMeanIntegerExpr := .atom (26, 78125)
  let e3 : LowMeanIntegerExpr := .atom (33, 1)
  let e4 : LowMeanIntegerExpr := .atom (189, 4)
  let e5 : LowMeanIntegerExpr := .neg (-189, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-57, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-741, 156250) e2 e6
  let e8 : LowMeanIntegerExpr := .add (51713, 10000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e10 : LowMeanIntegerExpr := .pow (3249, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (4200957, 1600000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-4200957, 1600000000) e11
  let e13 : LowMeanIntegerExpr := .add (4073123, 1600000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (68079, 42250000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (1124063387, 270400000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (328000, 1)
  let e33 : LowMeanIntegerExpr := .pow (116415321826934814453125, 5756130429098929077956071497934208653) e21 33
  let e34 : LowMeanIntegerExpr := .mul (38184225559234619140625000000, 5756130429098929077956071497934208653) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-38184225559234619140625000000, 5756130429098929077956071497934208653) e34
  let e36 : LowMeanIntegerExpr := .add (38285474207882333493485639882734260838200519, 9209808686558286524729714396694733844800000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (38377572294747916358732937026701208176648519, 9209808686558286524729714396694733844800000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-38285474207882333493485639882734260838200519, 9209808686558286524729714396694733844800000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0508 : LowMeanDirectSeedInput :=
  { record := 508, positions := [], target := { R := 33, expr := lowMeanSeedTargetExpr0508 } }

noncomputable def lowMeanSeedTargetExpr0509 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e2 : LowMeanIntegerExpr := .atom (26, 78125)
  let e3 : LowMeanIntegerExpr := .atom (34, 1)
  let e4 : LowMeanIntegerExpr := .atom (189, 4)
  let e5 : LowMeanIntegerExpr := .neg (-189, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-53, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-689, 156250) e2 e6
  let e8 : LowMeanIntegerExpr := .add (55041, 10000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e10 : LowMeanIntegerExpr := .pow (2809, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (3632037, 1600000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-3632037, 1600000000) e11
  let e13 : LowMeanIntegerExpr := .add (5174523, 1600000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (35071, 21125000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (1323403187, 270400000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (328000, 1)
  let e33 : LowMeanIntegerExpr := .pow (582076609134674072265625, 74829695578286078013428929473144712489) e21 34
  let e34 : LowMeanIntegerExpr := .mul (190921127796173095703125000000, 74829695578286078013428929473144712489) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-190921127796173095703125000000, 74829695578286078013428929473144712489) e34
  let e36 : LowMeanIntegerExpr := .add (585975183345980163050280449335845819054090547, 119727512925257724821486287157031539982400000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (587172458475232740298495312207416134453914547, 119727512925257724821486287157031539982400000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-585975183345980163050280449335845819054090547, 119727512925257724821486287157031539982400000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0509 : LowMeanDirectSeedInput :=
  { record := 509, positions := [], target := { R := 34, expr := lowMeanSeedTargetExpr0509 } }

noncomputable def lowMeanSeedTargetExpr0510 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e2 : LowMeanIntegerExpr := .atom (26, 78125)
  let e3 : LowMeanIntegerExpr := .atom (35, 1)
  let e4 : LowMeanIntegerExpr := .atom (189, 4)
  let e5 : LowMeanIntegerExpr := .neg (-189, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-49, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-637, 156250) e2 e6
  let e8 : LowMeanIntegerExpr := .add (58369, 10000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e10 : LowMeanIntegerExpr := .pow (2401, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (3104493, 1600000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-3104493, 1600000000) e11
  let e13 : LowMeanIntegerExpr := .add (6234547, 1600000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (14441, 8450000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (1515750443, 270400000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (328000, 1)
  let e33 : LowMeanIntegerExpr := .pow (2910383045673370361328125, 972786042517719014174576083150881262357) e21 35
  let e34 : LowMeanIntegerExpr := .mul (954605638980865478515625000000, 972786042517719014174576083150881262357) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-954605638980865478515625000000, 972786042517719014174576083150881262357) e34
  let e36 : LowMeanIntegerExpr := .add (8724855720503459471352731282533450350639183279, 1556457668028350422679321733041410019771200000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (8740420297183742975579524499863864450836895279, 1556457668028350422679321733041410019771200000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-8724855720503459471352731282533450350639183279, 1556457668028350422679321733041410019771200000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0510 : LowMeanDirectSeedInput :=
  { record := 510, positions := [], target := { R := 35, expr := lowMeanSeedTargetExpr0510 } }

noncomputable def lowMeanSeedTargetExpr0511 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e2 : LowMeanIntegerExpr := .atom (26, 78125)
  let e3 : LowMeanIntegerExpr := .atom (36, 1)
  let e4 : LowMeanIntegerExpr := .atom (189, 4)
  let e5 : LowMeanIntegerExpr := .neg (-189, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-45, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-117, 31250) e2 e6
  let e8 : LowMeanIntegerExpr := .add (61697, 10000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e10 : LowMeanIntegerExpr := .pow (2025, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (104733, 64000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-104733, 64000000) e11
  let e13 : LowMeanIntegerExpr := .add (1450639, 320000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (18567, 10562500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (340221031, 54080000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (328000, 1)
  let e33 : LowMeanIntegerExpr := .pow (14551915228366851806640625, 12646218552730347184269489080961456410641) e21 36
  let e34 : LowMeanIntegerExpr := .mul (4773028194904327392578125000000, 12646218552730347184269489080961456410641) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-4773028194904327392578125000000, 12646218552730347184269489080961456410641) e34
  let e36 : LowMeanIntegerExpr := .add (25458634651691608305290456605579580895206156159, 4046789936873711098966236505907666051405120000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (25499102551060345416280118970638657555720207359, 4046789936873711098966236505907666051405120000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-25458634651691608305290456605579580895206156159, 4046789936873711098966236505907666051405120000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0511 : LowMeanDirectSeedInput :=
  { record := 511, positions := [], target := { R := 36, expr := lowMeanSeedTargetExpr0511 } }

noncomputable def lowMeanSeedGroup0496 : List LowMeanDirectSeedInput := [lowMeanSeedRecord0496, lowMeanSeedRecord0497, lowMeanSeedRecord0498, lowMeanSeedRecord0499, lowMeanSeedRecord0500, lowMeanSeedRecord0501, lowMeanSeedRecord0502, lowMeanSeedRecord0503, lowMeanSeedRecord0504, lowMeanSeedRecord0505, lowMeanSeedRecord0506, lowMeanSeedRecord0507, lowMeanSeedRecord0508, lowMeanSeedRecord0509, lowMeanSeedRecord0510, lowMeanSeedRecord0511]

end Erdos993Lean.Analytic.V213
