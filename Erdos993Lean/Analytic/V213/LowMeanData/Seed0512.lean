module

public import Erdos993Lean.Analytic.V213.LowMeanCoreAll
public import Erdos993Lean.Analytic.V213.LowMeanData.Seed0448
public import Erdos993Lean.Analytic.V213.LowMeanFiberSeed
public import Erdos993Lean.Analytic.V213.LowMeanIntegerExpr
public import Erdos993Lean.Analytic.V213.LowMeanSeedGeometry
public import Erdos993Lean.Analytic.V213.LowMeanWidthData
public import Erdos993Lean.Ceiling.Prefix
public import Erdos993Lean.Ceiling.Statement

/-! Exact core/budget keys and equation-51 targets for the direct fibers. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanSeedTargetExpr0512 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e2 : LowMeanIntegerExpr := .atom (26, 78125)
  let e3 : LowMeanIntegerExpr := .atom (37, 1)
  let e4 : LowMeanIntegerExpr := .atom (189, 4)
  let e5 : LowMeanIntegerExpr := .neg (-189, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-41, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-533, 156250) e2 e6
  let e8 : LowMeanIntegerExpr := .add (2601, 400000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e10 : LowMeanIntegerExpr := .pow (1681, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (2173533, 1600000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-2173533, 1600000000) e11
  let e13 : LowMeanIntegerExpr := .add (8230467, 1600000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (76331, 42250000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (1879467323, 270400000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (328000, 1)
  let e33 : LowMeanIntegerExpr := .pow (72759576141834259033203125, 164400841185494513395503358052498933338333) e21 37
  let e34 : LowMeanIntegerExpr := .mul (23865140974521636962890625000000, 164400841185494513395503358052498933338333) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-23865140974521636962890625000000, 164400841185494513395503358052498933338333) e34
  let e36 : LowMeanIntegerExpr := .add (1828319540998315976402270425034412211252971460311, 263041345896791221432805372883998293341332800000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (1830949954457283888616598478763252194186384788311, 263041345896791221432805372883998293341332800000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-1828319540998315976402270425034412211252971460311, 263041345896791221432805372883998293341332800000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0512 : LowMeanDirectSeedInput :=
  { record := 512, positions := [], target := { R := 37, expr := lowMeanSeedTargetExpr0512 } }

noncomputable def lowMeanSeedTargetExpr0513 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e2 : LowMeanIntegerExpr := .atom (26, 78125)
  let e3 : LowMeanIntegerExpr := .atom (38, 1)
  let e4 : LowMeanIntegerExpr := .atom (189, 4)
  let e5 : LowMeanIntegerExpr := .neg (-189, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-37, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-481, 156250) e2 e6
  let e8 : LowMeanIntegerExpr := .add (68353, 10000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e10 : LowMeanIntegerExpr := .pow (1369, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1770117, 1600000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1770117, 1600000000) e11
  let e13 : LowMeanIntegerExpr := .add (9166363, 1600000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (39197, 21125000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (2050836947, 270400000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (328000, 1)
  let e33 : LowMeanIntegerExpr := .pow (363797880709171295166015625, 2137210935411428674141543654682486133398329) e21 38
  let e34 : LowMeanIntegerExpr := .mul (119325704872608184814453125000000, 2137210935411428674141543654682486133398329) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-119325704872608184814453125000000, 2137210935411428674141543654682486133398329) e34
  let e36 : LowMeanIntegerExpr := .add (25935332056855135937464189708923829089872566753027, 3419537496658285878626469847491977813437326400000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (25969527431821718796250454407398748868006940017027, 3419537496658285878626469847491977813437326400000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-25935332056855135937464189708923829089872566753027, 3419537496658285878626469847491977813437326400000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0513 : LowMeanDirectSeedInput :=
  { record := 513, positions := [], target := { R := 38, expr := lowMeanSeedTargetExpr0513 } }

noncomputable def lowMeanSeedTargetExpr0514 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e2 : LowMeanIntegerExpr := .atom (26, 78125)
  let e3 : LowMeanIntegerExpr := .atom (39, 1)
  let e4 : LowMeanIntegerExpr := .atom (189, 4)
  let e5 : LowMeanIntegerExpr := .neg (-189, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-33, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-429, 156250) e2 e6
  let e8 : LowMeanIntegerExpr := .add (71681, 10000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e10 : LowMeanIntegerExpr := .pow (1089, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1408077, 1600000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1408077, 1600000000) e11
  let e13 : LowMeanIntegerExpr := .add (10060883, 1600000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (6189, 3250000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (170401079, 20800000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (328000, 1)
  let e33 : LowMeanIntegerExpr := .pow (1818989403545856475830078125, 27783742160348572763840067510872319734178277) e21 39
  let e34 : LowMeanIntegerExpr := .mul (596628524363040924072265625000000, 27783742160348572763840067510872319734178277) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-596628524363040924072265625000000, 27783742160348572763840067510872319734178277) e34
  let e36 : LowMeanIntegerExpr := .add (364183048490101116024392958967874039533613198396991, 44453987456557716422144108017395711574685243200000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (364627588364666693188614400048047996649360050828991, 44453987456557716422144108017395711574685243200000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-364183048490101116024392958967874039533613198396991, 44453987456557716422144108017395711574685243200000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0514 : LowMeanDirectSeedInput :=
  { record := 514, positions := [], target := { R := 39, expr := lowMeanSeedTargetExpr0514 } }

noncomputable def lowMeanSeedTargetExpr0515 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e2 : LowMeanIntegerExpr := .atom (26, 78125)
  let e3 : LowMeanIntegerExpr := .atom (40, 1)
  let e4 : LowMeanIntegerExpr := .atom (189, 4)
  let e5 : LowMeanIntegerExpr := .neg (-189, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-29, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-377, 156250) e2 e6
  let e8 : LowMeanIntegerExpr := .add (75009, 10000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e10 : LowMeanIntegerExpr := .pow (841, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1087413, 1600000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1087413, 1600000000) e11
  let e13 : LowMeanIntegerExpr := .add (10914027, 1600000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (2063, 1056250) e29 e3
  let e31 : LowMeanIntegerExpr := .add (2372598563, 270400000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (328000, 1)
  let e33 : LowMeanIntegerExpr := .pow (9094947017729282379150390625, 361188648084531445929920877641340156544317601) e21 40
  let e34 : LowMeanIntegerExpr := .mul (2983142621815204620361328125000000, 361188648084531445929920877641340156544317601) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-2983142621815204620361328125000000, 361188648084531445929920877641340156544317601) e34
  let e36 : LowMeanIntegerExpr := .add (5070743589412013291140894341123309821368301692001227, 577901836935250313487873404226144250470908161600000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (5076522607781365794275773075165571263873010773617227, 577901836935250313487873404226144250470908161600000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-5070743589412013291140894341123309821368301692001227, 577901836935250313487873404226144250470908161600000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0515 : LowMeanDirectSeedInput :=
  { record := 515, positions := [], target := { R := 40, expr := lowMeanSeedTargetExpr0515 } }

noncomputable def lowMeanSeedTargetExpr0516 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e2 : LowMeanIntegerExpr := .atom (26, 78125)
  let e3 : LowMeanIntegerExpr := .atom (41, 1)
  let e4 : LowMeanIntegerExpr := .atom (189, 4)
  let e5 : LowMeanIntegerExpr := .neg (-189, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-25, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-13, 6250) e2 e6
  let e8 : LowMeanIntegerExpr := .add (78337, 10000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e10 : LowMeanIntegerExpr := .pow (625, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1293, 2560000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1293, 2560000) e11
  let e13 : LowMeanIntegerExpr := .add (2345159, 320000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (84583, 42250000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (504598111, 54080000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (328000, 1)
  let e33 : LowMeanIntegerExpr := .pow (45474735088646411895751953125, 4695452425098908797088971409337422035076128813) e21 41
  let e34 : LowMeanIntegerExpr := .mul (14915713109076023101806640625000000, 4695452425098908797088971409337422035076128813) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-14915713109076023101806640625000000, 4695452425098908797088971409337422035076128813) e34
  let e36 : LowMeanIntegerExpr := .add (14019623805849920723275419779520519500054380711434747, 1502544776031650815068470850987975051224361220160000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (14034649253610237231426104488030399250566624323636347, 1502544776031650815068470850987975051224361220160000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-14019623805849920723275419779520519500054380711434747, 1502544776031650815068470850987975051224361220160000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0516 : LowMeanDirectSeedInput :=
  { record := 516, positions := [{ j := 34, mode := 0, left := 1028, right := 0 }], target := { R := 41, expr := lowMeanSeedTargetExpr0516 } }

noncomputable def lowMeanSeedTargetExpr0517 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e2 : LowMeanIntegerExpr := .atom (26, 78125)
  let e3 : LowMeanIntegerExpr := .atom (42, 1)
  let e4 : LowMeanIntegerExpr := .atom (189, 4)
  let e5 : LowMeanIntegerExpr := .neg (-189, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-21, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-273, 156250) e2 e6
  let e8 : LowMeanIntegerExpr := .add (16333, 2000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e10 : LowMeanIntegerExpr := .pow (441, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (570213, 1600000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-570213, 1600000000) e11
  let e13 : LowMeanIntegerExpr := .add (12496187, 1600000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (43323, 21125000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (2666390003, 270400000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (328000, 1)
  let e33 : LowMeanIntegerExpr := .pow (227373675443232059478759765625, 61040881526285814362156628321386486455989674569) e21 42
  let e34 : LowMeanIntegerExpr := .mul (74578565545380115509033203125000000, 61040881526285814362156628321386486455989674569) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-74578565545380115509033203125000000, 61040881526285814362156628321386486455989674569) e34
  let e36 : LowMeanIntegerExpr := .add (963069800330354041494067881909402487932223477763342803, 97665410442057302979450605314218378329583479310400000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (964046454434774614523862387962544671715519312556446803, 97665410442057302979450605314218378329583479310400000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-963069800330354041494067881909402487932223477763342803, 97665410442057302979450605314218378329583479310400000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0517 : LowMeanDirectSeedInput :=
  { record := 517, positions := [{ j := 35, mode := 0, left := 1029, right := 0 }], target := { R := 42, expr := lowMeanSeedTargetExpr0517 } }

noncomputable def lowMeanSeedTargetExpr0518 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e2 : LowMeanIntegerExpr := .atom (26, 78125)
  let e3 : LowMeanIntegerExpr := .atom (48, 1)
  let e4 : LowMeanIntegerExpr := .atom (189, 4)
  let e5 : LowMeanIntegerExpr := .neg (-189, 4) e4
  let e6 : LowMeanIntegerExpr := .add (3, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (39, 156250) e2 e6
  let e8 : LowMeanIntegerExpr := .add (101633, 10000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e10 : LowMeanIntegerExpr := .pow (9, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (11637, 1600000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-11637, 1600000000) e11
  let e13 : LowMeanIntegerExpr := .add (16249643, 1600000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (6189, 2640625) e29 e3
  let e31 : LowMeanIntegerExpr := .add (3379943267, 270400000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (328000, 1)
  let e33 : LowMeanIntegerExpr := .pow (3552713678800500929355621337890625, 294632676319010105335586872991323185304149065116720321) e21 48
  let e34 : LowMeanIntegerExpr := .mul (1165290086646564304828643798828125000000, 294632676319010105335586872991323185304149065116720321) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1165290086646564304828643798828125000000, 294632676319010105335586872991323185304149065116720321) e34
  let e36 : LowMeanIntegerExpr := .add (5892554618711913936062416543624741327257685531394103065597803, 471412282110416168536938996786117096486638504186752513600000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (5897268741533018097747785933592602498222551916435970590733803, 471412282110416168536938996786117096486638504186752513600000000) e0 e36
  let e38 : LowMeanIntegerExpr := .atom (43, 1)
  let e39 : LowMeanIntegerExpr := .add (-17, 4) e38 e5
  let e40 : LowMeanIntegerExpr := .mul (-221, 156250) e2 e39
  let e41 : LowMeanIntegerExpr := .add (84993, 10000000) e1 e40
  let e42 : LowMeanIntegerExpr := .pow (289, 16) e39 2
  let e43 : LowMeanIntegerExpr := .mul (373677, 1600000000) e9 e42
  let e44 : LowMeanIntegerExpr := .neg (-373677, 1600000000) e43
  let e45 : LowMeanIntegerExpr := .add (13225203, 1600000000) e41 e44
  let e46 : LowMeanIntegerExpr := .mul (88709, 42250000) e29 e38
  let e47 : LowMeanIntegerExpr := .add (2802796907, 270400000000) e45 e46
  let e48 : LowMeanIntegerExpr := .pow (1136868377216160297393798828125, 793531459841715586708036168178024323927865769397) e21 43
  let e49 : LowMeanIntegerExpr := .mul (372892827726900577545166015625000000, 793531459841715586708036168178024323927865769397) e32 e48
  let e50 : LowMeanIntegerExpr := .neg (-372892827726900577545166015625000000, 793531459841715586708036168178024323927865769397) e49
  let e51 : LowMeanIntegerExpr := .add (13160399533436242221193018745830091774265019346609981391, 1269650335746744938732857869084838918284585231035200000000) e47 e50
  let e52 : LowMeanIntegerExpr := .neg (-13160399533436242221193018745830091774265019346609981391, 1269650335746744938732857869084838918284585231035200000000) e51
  let e53 : LowMeanIntegerExpr := .add (25272612939121885367859160609927755827009252204377769253131, 11785307052760404213423474919652927412165962604668812840000000) e37 e52
  e53

noncomputable def lowMeanSeedRecord0518 : LowMeanDirectSeedInput :=
  { record := 518, positions := [{ j := 35, mode := 0, left := 1030, right := 0 }, { j := 36, mode := 0, left := 1031, right := 0 }, { j := 37, mode := 0, left := 1032, right := 0 }], target := { R := 48, expr := lowMeanSeedTargetExpr0518 } }

noncomputable def lowMeanSeedTargetExpr0519 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e2 : LowMeanIntegerExpr := .atom (26, 78125)
  let e3 : LowMeanIntegerExpr := .atom (49, 1)
  let e4 : LowMeanIntegerExpr := .atom (189, 4)
  let e5 : LowMeanIntegerExpr := .neg (-189, 4) e4
  let e6 : LowMeanIntegerExpr := .add (7, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (91, 156250) e2 e6
  let e8 : LowMeanIntegerExpr := .add (104961, 10000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e10 : LowMeanIntegerExpr := .pow (49, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (63357, 1600000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-63357, 1600000000) e11
  let e13 : LowMeanIntegerExpr := .add (16730403, 1600000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (101087, 42250000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (3474394907, 270400000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (328000, 1)
  let e33 : LowMeanIntegerExpr := .pow (17763568394002504646778106689453125, 3830224792147131369362629348887201408953937846517364173) e21 49
  let e34 : LowMeanIntegerExpr := .mul (5826450433232821524143218994140625000000, 3830224792147131369362629348887201408953937846517364173) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-5826450433232821524143218994140625000000, 3830224792147131369362629348887201408953937846517364173) e34
  let e36 : LowMeanIntegerExpr := .add (78743866926032848237729639591492842404359587139257264909677319, 6128359667435410190980206958219522254326300554427782676800000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (78805150522707202339639441661075037626902850144801542736445319, 6128359667435410190980206958219522254326300554427782676800000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-78743866926032848237729639591492842404359587139257264909677319, 6128359667435410190980206958219522254326300554427782676800000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0519 : LowMeanDirectSeedInput :=
  { record := 519, positions := [{ j := 39, mode := 0, left := 1033, right := 0 }, { j := 40, mode := 0, left := 1034, right := 0 }, { j := 41, mode := 0, left := 1035, right := 0 }], target := { R := 49, expr := lowMeanSeedTargetExpr0519 } }

noncomputable def lowMeanSeedTargetExpr0520 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e2 : LowMeanIntegerExpr := .atom (26, 78125)
  let e3 : LowMeanIntegerExpr := .atom (62, 1)
  let e4 : LowMeanIntegerExpr := .atom (189, 4)
  let e5 : LowMeanIntegerExpr := .neg (-189, 4) e4
  let e6 : LowMeanIntegerExpr := .add (59, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (767, 156250) e2 e6
  let e8 : LowMeanIntegerExpr := .add (5929, 400000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e10 : LowMeanIntegerExpr := .pow (3481, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (4500933, 1600000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-4500933, 1600000000) e11
  let e13 : LowMeanIntegerExpr := .add (19215067, 1600000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (63953, 21125000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (4065944723, 270400000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (328000, 1)
  let e33 : LowMeanIntegerExpr := .pow (21684043449710088680149056017398834228515625, 1160079742193852504915146511382047428546764970438554956151425821551769) e21 62
  let e34 : LowMeanIntegerExpr := .mul (7112366251504909087088890373706817626953125000000, 1160079742193852504915146511382047428546764970438554956151425821551769) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-7112366251504909087088890373706817626953125000000, 1160079742193852504915146511382047428546764970438554956151425821551769) e34
  let e36 : LowMeanIntegerExpr := .add (27910178142202929192170933055140637644299423865240059369119888805114525661923, 1856127587510164007864234418211275885674823952701687929842281314482830400000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (27928739418078030832249575399322750403156172104767076248418311618259353965923, 1856127587510164007864234418211275885674823952701687929842281314482830400000000) e0 e36
  let e38 : LowMeanIntegerExpr := .atom (50, 1)
  let e39 : LowMeanIntegerExpr := .add (11, 4) e38 e5
  let e40 : LowMeanIntegerExpr := .mul (143, 156250) e2 e39
  let e41 : LowMeanIntegerExpr := .add (108289, 10000000) e1 e40
  let e42 : LowMeanIntegerExpr := .pow (121, 16) e39 2
  let e43 : LowMeanIntegerExpr := .mul (156453, 1600000000) e9 e42
  let e44 : LowMeanIntegerExpr := .neg (-156453, 1600000000) e43
  let e45 : LowMeanIntegerExpr := .add (17169787, 1600000000) e41 e44
  let e46 : LowMeanIntegerExpr := .mul (2063, 845000) e29 e38
  let e47 : LowMeanIntegerExpr := .add (3561854003, 270400000000) e45 e46
  let e48 : LowMeanIntegerExpr := .pow (88817841970012523233890533447265625, 49792922297912707801714181535533618316401192004725734249) e21 50
  let e49 : LowMeanIntegerExpr := .mul (29132252166164107620716094970703125000000, 49792922297912707801714181535533618316401192004725734249) e32 e48
  let e50 : LowMeanIntegerExpr := .neg (-29132252166164107620716094970703125000000, 49792922297912707801714181535533618316401192004725734249) e49
  let e51 : LowMeanIntegerExpr := .add (1049438577561422837083545899346203926090340995094697937585294963, 79668675676660332482742690456853789306241907207561174798400000000) e47 e50
  let e52 : LowMeanIntegerExpr := .neg (-1049438577561422837083545899346203926090340995094697937585294963, 79668675676660332482742690456853789306241907207561174798400000000) e51
  let e53 : LowMeanIntegerExpr := .add (21742688170228890216470877663272885049670542816219782681485729542681166267, 11600797421938525049151465113820474285467649704385549561514258215517690000000) e37 e52
  e53

noncomputable def lowMeanSeedRecord0520 : LowMeanDirectSeedInput :=
  { record := 520, positions := [{ j := 25, mode := 0, left := 1036, right := 0 }, { j := 26, mode := 0, left := 1037, right := 0 }, { j := 39, mode := 0, left := 1038, right := 0 }, { j := 40, mode := 0, left := 1039, right := 0 }, { j := 41, mode := 0, left := 1040, right := 0 }, { j := 42, mode := 0, left := 1041, right := 0 }], target := { R := 62, expr := lowMeanSeedTargetExpr0520 } }

noncomputable def lowMeanSeedTargetExpr0521 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (5559, 25000)
  let e2 : LowMeanIntegerExpr := .atom (7469, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (0, 1)
  let e4 : LowMeanIntegerExpr := .atom (39, 4)
  let e5 : LowMeanIntegerExpr := .neg (-39, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-39, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-291291, 4000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (598149, 4000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (2003, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (1521, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (3046563, 16000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-3046563, 16000000) e11
  let e13 : LowMeanIntegerExpr := .add (-653967, 16000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (159, 3125)
  let e15 : LowMeanIntegerExpr := .atom (19, 29)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (7, 10)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-19, 29) e15
  let e21 : LowMeanIntegerExpr := .add (10, 29) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (190, 841) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-7, 10) e17
  let e24 : LowMeanIntegerExpr := .add (3, 10) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (21, 100) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (190, 841) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (190, 841) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (6042, 525625) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (0, 1) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-653967, 16000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (8457, 10000)
  let e33 : LowMeanIntegerExpr := .pow (1, 1) e21 0
  let e34 : LowMeanIntegerExpr := .mul (8457, 10000) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-8457, 10000) e34
  let e36 : LowMeanIntegerExpr := .add (-14185167, 16000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-14185007, 16000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (14185167, 16000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0521 : LowMeanDirectSeedInput :=
  { record := 521, positions := [], target := { R := 0, expr := lowMeanSeedTargetExpr0521 } }

noncomputable def lowMeanSeedTargetExpr0522 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (5559, 25000)
  let e2 : LowMeanIntegerExpr := .atom (7469, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (1, 1)
  let e4 : LowMeanIntegerExpr := .atom (39, 4)
  let e5 : LowMeanIntegerExpr := .neg (-39, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-35, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-52283, 800000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (25121, 160000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (2003, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (1225, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (98147, 640000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-98147, 640000) e11
  let e13 : LowMeanIntegerExpr := .add (2337, 640000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (159, 3125)
  let e15 : LowMeanIntegerExpr := .atom (19, 29)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (7, 10)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .neg (-19, 29) e15
  let e20 : LowMeanIntegerExpr := .add (10, 29) e3 e19
  let e21 : LowMeanIntegerExpr := .mul (190, 841) e15 e20
  let e22 : LowMeanIntegerExpr := .neg (-7, 10) e17
  let e23 : LowMeanIntegerExpr := .add (3, 10) e3 e22
  let e24 : LowMeanIntegerExpr := .mul (21, 100) e17 e23
  let e25 : LowMeanIntegerExpr := .maximum (190, 841) e21 e24
  let e26 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e25
  let e27 : LowMeanIntegerExpr := .selectLE (190, 841) e15 e16 e26 e25
  let e28 : LowMeanIntegerExpr := .mul (6042, 525625) e14 e27
  let e29 : LowMeanIntegerExpr := .mul (6042, 525625) e28 e3
  let e30 : LowMeanIntegerExpr := .add (326097, 21529600) e13 e29
  let e31 : LowMeanIntegerExpr := .atom (8457, 10000)
  let e32 : LowMeanIntegerExpr := .pow (10, 29) e20 1
  let e33 : LowMeanIntegerExpr := .mul (8457, 29000) e31 e32
  let e34 : LowMeanIntegerExpr := .neg (-8457, 29000) e33
  let e35 : LowMeanIntegerExpr := .add (-29761899, 107648000) e30 e34
  let e36 : LowMeanIntegerExpr := .add (-744020563, 2691200000) e0 e35
  let e37 : LowMeanIntegerExpr := .neg (29761899, 107648000) e35
  let e38 : LowMeanIntegerExpr := .add (1, 100000) e36 e37
  e38

noncomputable def lowMeanSeedRecord0522 : LowMeanDirectSeedInput :=
  { record := 522, positions := [], target := { R := 1, expr := lowMeanSeedTargetExpr0522 } }

noncomputable def lowMeanSeedTargetExpr0523 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (5559, 25000)
  let e2 : LowMeanIntegerExpr := .atom (7469, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (2, 1)
  let e4 : LowMeanIntegerExpr := .atom (39, 4)
  let e5 : LowMeanIntegerExpr := .neg (-39, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-31, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-231539, 4000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (657901, 4000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (2003, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (961, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1924883, 16000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1924883, 16000000) e11
  let e13 : LowMeanIntegerExpr := .add (706721, 16000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (159, 3125)
  let e15 : LowMeanIntegerExpr := .atom (19, 29)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (7, 10)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-19, 29) e15
  let e21 : LowMeanIntegerExpr := .add (10, 29) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (190, 841) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-7, 10) e17
  let e24 : LowMeanIntegerExpr := .add (3, 10) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (21, 100) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (190, 841) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (190, 841) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (6042, 525625) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (12084, 525625) e29 e3
  let e31 : LowMeanIntegerExpr := .add (903702761, 13456000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (8457, 10000)
  let e33 : LowMeanIntegerExpr := .pow (100, 841) e21 2
  let e34 : LowMeanIntegerExpr := .mul (8457, 84100) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-8457, 84100) e34
  let e36 : LowMeanIntegerExpr := .add (-449417239, 13456000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-449282679, 13456000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (449417239, 13456000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0523 : LowMeanDirectSeedInput :=
  { record := 523, positions := [{ j := 0, mode := 0, left := 1042, right := 0 }], target := { R := 2, expr := lowMeanSeedTargetExpr0523 } }

noncomputable def lowMeanSeedTargetExpr0524 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (5559, 25000)
  let e2 : LowMeanIntegerExpr := .atom (7469, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (3, 1)
  let e4 : LowMeanIntegerExpr := .atom (39, 4)
  let e5 : LowMeanIntegerExpr := .neg (-39, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-27, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-201663, 4000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (687777, 4000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (2003, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (729, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1460187, 16000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1460187, 16000000) e11
  let e13 : LowMeanIntegerExpr := .add (1290921, 16000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (159, 3125)
  let e15 : LowMeanIntegerExpr := .atom (19, 29)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (7, 10)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-19, 29) e15
  let e21 : LowMeanIntegerExpr := .add (10, 29) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (190, 841) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-7, 10) e17
  let e24 : LowMeanIntegerExpr := .add (3, 10) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (21, 100) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (190, 841) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (190, 841) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (6042, 525625) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (18126, 525625) e29 e3
  let e31 : LowMeanIntegerExpr := .add (1549690161, 13456000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (8457, 10000)
  let e33 : LowMeanIntegerExpr := .pow (1000, 24389) e21 3
  let e34 : LowMeanIntegerExpr := .mul (8457, 243890) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-8457, 243890) e34
  let e36 : LowMeanIntegerExpr := .add (31409814669, 390224000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (31413716909, 390224000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-31409814669, 390224000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0524 : LowMeanDirectSeedInput :=
  { record := 524, positions := [], target := { R := 3, expr := lowMeanSeedTargetExpr0524 } }

noncomputable def lowMeanSeedTargetExpr0525 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (5559, 25000)
  let e2 : LowMeanIntegerExpr := .atom (7469, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (4, 1)
  let e4 : LowMeanIntegerExpr := .atom (39, 4)
  let e5 : LowMeanIntegerExpr := .neg (-39, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-23, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-171787, 4000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (717653, 4000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (2003, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (529, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1059587, 16000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1059587, 16000000) e11
  let e13 : LowMeanIntegerExpr := .add (72441, 640000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (159, 3125)
  let e15 : LowMeanIntegerExpr := .atom (19, 29)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (7, 10)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-19, 29) e15
  let e21 : LowMeanIntegerExpr := .add (10, 29) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (190, 841) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-7, 10) e17
  let e24 : LowMeanIntegerExpr := .add (3, 10) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (21, 100) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (190, 841) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (190, 841) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (6042, 525625) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (24168, 525625) e29 e3
  let e31 : LowMeanIntegerExpr := .add (85670913, 538240000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (8457, 10000)
  let e33 : LowMeanIntegerExpr := .pow (10000, 707281) e21 4
  let e34 : LowMeanIntegerExpr := .mul (8457, 707281) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-8457, 707281) e34
  let e36 : LowMeanIntegerExpr := .add (66636757833, 452659840000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (333206422157, 2263299200000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-66636757833, 452659840000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0525 : LowMeanDirectSeedInput :=
  { record := 525, positions := [], target := { R := 4, expr := lowMeanSeedTargetExpr0525 } }

noncomputable def lowMeanSeedTargetExpr0526 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (5559, 25000)
  let e2 : LowMeanIntegerExpr := .atom (7469, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (5, 1)
  let e4 : LowMeanIntegerExpr := .atom (39, 4)
  let e5 : LowMeanIntegerExpr := .neg (-39, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-19, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-141911, 4000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (747529, 4000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (2003, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (361, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (723083, 16000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-723083, 16000000) e11
  let e13 : LowMeanIntegerExpr := .add (2267033, 16000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (159, 3125)
  let e15 : LowMeanIntegerExpr := .atom (19, 29)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (7, 10)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-19, 29) e15
  let e21 : LowMeanIntegerExpr := .add (10, 29) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (190, 841) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-7, 10) e17
  let e24 : LowMeanIntegerExpr := .add (3, 10) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (21, 100) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (190, 841) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (190, 841) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (6042, 525625) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (6042, 105125) e29 e3
  let e31 : LowMeanIntegerExpr := .add (2679950753, 13456000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (8457, 10000)
  let e33 : LowMeanIntegerExpr := .pow (100000, 20511149) e21 5
  let e34 : LowMeanIntegerExpr := .mul (84570, 20511149) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-84570, 20511149) e34
  let e36 : LowMeanIntegerExpr := .add (64008198914917, 328178384000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (64011480698757, 328178384000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-64008198914917, 328178384000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0526 : LowMeanDirectSeedInput :=
  { record := 526, positions := [], target := { R := 5, expr := lowMeanSeedTargetExpr0526 } }

noncomputable def lowMeanSeedTargetExpr0527 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (5559, 25000)
  let e2 : LowMeanIntegerExpr := .atom (7469, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (6, 1)
  let e4 : LowMeanIntegerExpr := .atom (39, 4)
  let e5 : LowMeanIntegerExpr := .neg (-39, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-15, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-22407, 800000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (155481, 800000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (2003, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (225, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (18027, 640000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-18027, 640000) e11
  let e13 : LowMeanIntegerExpr := .add (531789, 3200000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (159, 3125)
  let e15 : LowMeanIntegerExpr := .atom (19, 29)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (7, 10)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-19, 29) e15
  let e21 : LowMeanIntegerExpr := .add (10, 29) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (190, 841) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-7, 10) e17
  let e24 : LowMeanIntegerExpr := .add (3, 10) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (21, 100) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (190, 841) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (190, 841) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (6042, 525625) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (36252, 525625) e29 e3
  let e31 : LowMeanIntegerExpr := .add (632844789, 2691200000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (8457, 10000)
  let e33 : LowMeanIntegerExpr := .pow (1000000, 594823321) e21 6
  let e34 : LowMeanIntegerExpr := .mul (845700, 594823321) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-845700, 594823321) e34
  let e36 : LowMeanIntegerExpr := .add (444892855208709, 1903434627200000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (444911889554981, 1903434627200000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-444892855208709, 1903434627200000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0527 : LowMeanDirectSeedInput :=
  { record := 527, positions := [], target := { R := 6, expr := lowMeanSeedTargetExpr0527 } }

noncomputable def lowMeanSeedGroup0512 : List LowMeanDirectSeedInput := [lowMeanSeedRecord0512, lowMeanSeedRecord0513, lowMeanSeedRecord0514, lowMeanSeedRecord0515, lowMeanSeedRecord0516, lowMeanSeedRecord0517, lowMeanSeedRecord0518, lowMeanSeedRecord0519, lowMeanSeedRecord0520, lowMeanSeedRecord0521, lowMeanSeedRecord0522, lowMeanSeedRecord0523, lowMeanSeedRecord0524, lowMeanSeedRecord0525, lowMeanSeedRecord0526, lowMeanSeedRecord0527]

end Erdos993Lean.Analytic.V213
