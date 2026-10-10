module

public import Erdos993Lean.Analytic.V213.LowMeanCoreAll
public import Erdos993Lean.Analytic.V213.LowMeanData.Seed0016
public import Erdos993Lean.Analytic.V213.LowMeanFiberSeed
public import Erdos993Lean.Analytic.V213.LowMeanIntegerExpr
public import Erdos993Lean.Analytic.V213.LowMeanSeedGeometry
public import Erdos993Lean.Analytic.V213.LowMeanWidthData
public import Erdos993Lean.Ceiling.Prefix
public import Erdos993Lean.Ceiling.Statement

/-! Exact core/budget keys and equation-51 targets for the direct fibers. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanSeedTargetExpr0128 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (88879, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (-1417, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (11, 1)
  let e4 : LowMeanIntegerExpr := .atom (10, 1)
  let e5 : LowMeanIntegerExpr := .neg (-10, 1) e4
  let e6 : LowMeanIntegerExpr := .add (1, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1417, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (43731, 500000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (303, 250000)
  let e10 : LowMeanIntegerExpr := .pow (1, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (303, 250000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-303, 250000) e11
  let e13 : LowMeanIntegerExpr := .add (69, 800) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (783, 25000)
  let e15 : LowMeanIntegerExpr := .atom (87, 187)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (23, 48)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-87, 187) e15
  let e21 : LowMeanIntegerExpr := .add (100, 187) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (8700, 34969) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-23, 48) e17
  let e24 : LowMeanIntegerExpr := .add (25, 48) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (575, 2304) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (575, 2304) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (575, 2304) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (575, 2304) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2001, 256000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (22011, 256000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (44091, 256000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (621, 500)
  let e33 : LowMeanIntegerExpr := .pow (10000000000000000000000, 9778171990537733621073763) e21 11
  let e34 : LowMeanIntegerExpr := .mul (12420000000000000000000, 9778171990537733621073763) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-12420000000000000000000, 9778171990537733621073763) e34
  let e36 : LowMeanIntegerExpr := .add (427949861234799213086763284433, 2503212029577659806994883328000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (10699372333877374742120830831657, 62580300739441495174872083200000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-427949861234799213086763284433, 2503212029577659806994883328000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0128 : LowMeanDirectSeedInput :=
  { record := 128, positions := [{ j := 4, mode := 0, left := 415, right := 0 }, { j := 6, mode := 0, left := 416, right := 0 }], target := { R := 11, expr := lowMeanSeedTargetExpr0128 } }

noncomputable def lowMeanSeedTargetExpr0129 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (88879, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (-1417, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (12, 1)
  let e4 : LowMeanIntegerExpr := .atom (10, 1)
  let e5 : LowMeanIntegerExpr := .neg (-10, 1) e4
  let e6 : LowMeanIntegerExpr := .add (2, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1417, 500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (17209, 200000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (303, 250000)
  let e10 : LowMeanIntegerExpr := .pow (4, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (303, 62500) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-303, 62500) e11
  let e13 : LowMeanIntegerExpr := .add (81197, 1000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (783, 25000)
  let e15 : LowMeanIntegerExpr := .atom (87, 187)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (23, 48)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-87, 187) e15
  let e21 : LowMeanIntegerExpr := .add (100, 187) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (8700, 34969) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-23, 48) e17
  let e24 : LowMeanIntegerExpr := .add (25, 48) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (575, 2304) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (575, 2304) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (575, 2304) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (575, 2304) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2001, 256000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (6003, 64000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (1399951, 8000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (621, 500)
  let e33 : LowMeanIntegerExpr := .pow (1000000000000000000000000, 1828518162230556187140793681) e21 12
  let e34 : LowMeanIntegerExpr := .mul (1242000000000000000000000, 1828518162230556187140793681) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1242000000000000000000000, 1828518162230556187140793681) e34
  let e36 : LowMeanIntegerExpr := .add (2549899829732829364743941254509631, 14628145297844449497126349448000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (2550046111185807809238912518004111, 14628145297844449497126349448000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-2549899829732829364743941254509631, 14628145297844449497126349448000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0129 : LowMeanDirectSeedInput :=
  { record := 129, positions := [{ j := 4, mode := 0, left := 417, right := 0 }, { j := 5, mode := 0, left := 418, right := 0 }, { j := 6, mode := 0, left := 419, right := 0 }], target := { R := 12, expr := lowMeanSeedTargetExpr0129 } }

noncomputable def lowMeanSeedTargetExpr0130 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (88879, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (-1417, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (13, 1)
  let e4 : LowMeanIntegerExpr := .atom (10, 1)
  let e5 : LowMeanIntegerExpr := .neg (-10, 1) e4
  let e6 : LowMeanIntegerExpr := .add (3, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-4251, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (21157, 250000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (303, 250000)
  let e10 : LowMeanIntegerExpr := .pow (9, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (2727, 250000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-2727, 250000) e11
  let e13 : LowMeanIntegerExpr := .add (1843, 25000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (783, 25000)
  let e15 : LowMeanIntegerExpr := .atom (87, 187)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (23, 48)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-87, 187) e15
  let e21 : LowMeanIntegerExpr := .add (100, 187) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (8700, 34969) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-23, 48) e17
  let e24 : LowMeanIntegerExpr := .add (25, 48) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (575, 2304) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (575, 2304) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (575, 2304) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (575, 2304) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2001, 256000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (26013, 256000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (1122133, 6400000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (621, 500)
  let e33 : LowMeanIntegerExpr := .pow (100000000000000000000000000, 341932896337114006995328418347) e21 13
  let e34 : LowMeanIntegerExpr := .mul (124200000000000000000000000, 341932896337114006995328418347) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-124200000000000000000000000, 341932896337114006995328418347) e34
  let e36 : LowMeanIntegerExpr := .add (382899306765454752011688864064974151, 2188370536557529644770101877420800000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (382921190470820327308136565083748359, 2188370536557529644770101877420800000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-382899306765454752011688864064974151, 2188370536557529644770101877420800000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0130 : LowMeanDirectSeedInput :=
  { record := 130, positions := [{ j := 5, mode := 0, left := 420, right := 0 }], target := { R := 13, expr := lowMeanSeedTargetExpr0130 } }

noncomputable def lowMeanSeedTargetExpr0131 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (3029, 50000)
  let e2 : LowMeanIntegerExpr := .atom (9609, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (0, 1)
  let e4 : LowMeanIntegerExpr := .atom (31, 2)
  let e5 : LowMeanIntegerExpr := .neg (-31, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-31, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-297879, 20000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (913721, 20000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (6041, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (961, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (5805401, 40000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-5805401, 40000000) e11
  let e13 : LowMeanIntegerExpr := .add (-3977959, 40000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (357, 25000)
  let e15 : LowMeanIntegerExpr := .atom (87, 187)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (23, 48)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-87, 187) e15
  let e21 : LowMeanIntegerExpr := .add (100, 187) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (8700, 34969) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-23, 48) e17
  let e24 : LowMeanIntegerExpr := .add (25, 48) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (575, 2304) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (575, 2304) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (575, 2304) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (575, 2304) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2737, 768000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (0, 1) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-3977959, 40000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (977, 500)
  let e33 : LowMeanIntegerExpr := .pow (1, 1) e21 0
  let e34 : LowMeanIntegerExpr := .mul (977, 500) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-977, 500) e34
  let e36 : LowMeanIntegerExpr := .add (-82137959, 40000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-82137559, 40000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (82137959, 40000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0131 : LowMeanDirectSeedInput :=
  { record := 131, positions := [], target := { R := 0, expr := lowMeanSeedTargetExpr0131 } }

noncomputable def lowMeanSeedTargetExpr0132 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (3029, 50000)
  let e2 : LowMeanIntegerExpr := .atom (9609, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (1, 1)
  let e4 : LowMeanIntegerExpr := .atom (31, 2)
  let e5 : LowMeanIntegerExpr := .neg (-31, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-29, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-278661, 20000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (932939, 20000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (6041, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (841, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (5080481, 40000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-5080481, 40000000) e11
  let e13 : LowMeanIntegerExpr := .add (-3214603, 40000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (357, 25000)
  let e15 : LowMeanIntegerExpr := .atom (87, 187)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (23, 48)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .neg (-87, 187) e15
  let e20 : LowMeanIntegerExpr := .add (100, 187) e3 e19
  let e21 : LowMeanIntegerExpr := .mul (8700, 34969) e15 e20
  let e22 : LowMeanIntegerExpr := .neg (-23, 48) e17
  let e23 : LowMeanIntegerExpr := .add (25, 48) e3 e22
  let e24 : LowMeanIntegerExpr := .mul (575, 2304) e17 e23
  let e25 : LowMeanIntegerExpr := .maximum (575, 2304) e21 e24
  let e26 : LowMeanIntegerExpr := .selectLE (575, 2304) e16 e17 e18 e25
  let e27 : LowMeanIntegerExpr := .selectLE (575, 2304) e15 e16 e26 e25
  let e28 : LowMeanIntegerExpr := .mul (2737, 768000) e14 e27
  let e29 : LowMeanIntegerExpr := .mul (2737, 768000) e28 e3
  let e30 : LowMeanIntegerExpr := .add (-36864611, 480000000) e13 e29
  let e31 : LowMeanIntegerExpr := .atom (977, 500)
  let e32 : LowMeanIntegerExpr := .pow (100, 187) e20 1
  let e33 : LowMeanIntegerExpr := .mul (977, 935) e31 e32
  let e34 : LowMeanIntegerExpr := .neg (-977, 935) e33
  let e35 : LowMeanIntegerExpr := .add (-100685682257, 89760000000) e30 e34
  let e36 : LowMeanIntegerExpr := .add (-100684784657, 89760000000) e0 e35
  let e37 : LowMeanIntegerExpr := .neg (100685682257, 89760000000) e35
  let e38 : LowMeanIntegerExpr := .add (1, 100000) e36 e37
  e38

noncomputable def lowMeanSeedRecord0132 : LowMeanDirectSeedInput :=
  { record := 132, positions := [], target := { R := 1, expr := lowMeanSeedTargetExpr0132 } }

noncomputable def lowMeanSeedTargetExpr0133 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (3029, 50000)
  let e2 : LowMeanIntegerExpr := .atom (9609, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (2, 1)
  let e4 : LowMeanIntegerExpr := .atom (31, 2)
  let e5 : LowMeanIntegerExpr := .neg (-31, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-27, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-259443, 20000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (952157, 20000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (6041, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (729, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (4403889, 40000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-4403889, 40000000) e11
  let e13 : LowMeanIntegerExpr := .add (-99983, 1600000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (357, 25000)
  let e15 : LowMeanIntegerExpr := .atom (87, 187)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (23, 48)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-87, 187) e15
  let e21 : LowMeanIntegerExpr := .add (100, 187) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (8700, 34969) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-23, 48) e17
  let e24 : LowMeanIntegerExpr := .add (25, 48) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (575, 2304) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (575, 2304) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (575, 2304) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (575, 2304) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2737, 768000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (2737, 384000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-531473, 9600000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (977, 500)
  let e33 : LowMeanIntegerExpr := .pow (10000, 34969) e21 2
  let e34 : LowMeanIntegerExpr := .mul (19540, 34969) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-19540, 34969) e34
  let e36 : LowMeanIntegerExpr := .add (-206169079337, 335702400000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-206165722313, 335702400000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (206169079337, 335702400000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0133 : LowMeanDirectSeedInput :=
  { record := 133, positions := [], target := { R := 2, expr := lowMeanSeedTargetExpr0133 } }

noncomputable def lowMeanSeedTargetExpr0134 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (3029, 50000)
  let e2 : LowMeanIntegerExpr := .atom (9609, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (3, 1)
  let e4 : LowMeanIntegerExpr := .atom (31, 2)
  let e5 : LowMeanIntegerExpr := .neg (-31, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-25, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-9609, 800000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (7771, 160000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (6041, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (625, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (6041, 64000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-6041, 64000) e11
  let e13 : LowMeanIntegerExpr := .add (-14663, 320000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (357, 25000)
  let e15 : LowMeanIntegerExpr := .atom (87, 187)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (23, 48)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-87, 187) e15
  let e21 : LowMeanIntegerExpr := .add (100, 187) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (8700, 34969) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-23, 48) e17
  let e24 : LowMeanIntegerExpr := .add (25, 48) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (575, 2304) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (575, 2304) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (575, 2304) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (575, 2304) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2737, 768000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (2737, 256000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-44967, 1280000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (977, 500)
  let e33 : LowMeanIntegerExpr := .pow (1000000, 6539203) e21 3
  let e34 : LowMeanIntegerExpr := .mul (1954000, 6539203) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1954000, 6539203) e34
  let e36 : LowMeanIntegerExpr := .add (-2795168341301, 8370179840000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-13975423197513, 41850899200000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (2795168341301, 8370179840000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0134 : LowMeanDirectSeedInput :=
  { record := 134, positions := [], target := { R := 3, expr := lowMeanSeedTargetExpr0134 } }

noncomputable def lowMeanSeedTargetExpr0135 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (3029, 50000)
  let e2 : LowMeanIntegerExpr := .atom (9609, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (4, 1)
  let e4 : LowMeanIntegerExpr := .atom (31, 2)
  let e5 : LowMeanIntegerExpr := .neg (-31, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-23, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-221007, 20000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (990593, 20000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (6041, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (529, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (3195689, 40000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-3195689, 40000000) e11
  let e13 : LowMeanIntegerExpr := .add (-1214503, 40000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (357, 25000)
  let e15 : LowMeanIntegerExpr := .atom (87, 187)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (23, 48)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-87, 187) e15
  let e21 : LowMeanIntegerExpr := .add (100, 187) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (8700, 34969) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-23, 48) e17
  let e24 : LowMeanIntegerExpr := .add (25, 48) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (575, 2304) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (575, 2304) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (575, 2304) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (575, 2304) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2737, 768000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (2737, 192000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-483221, 30000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (977, 500)
  let e33 : LowMeanIntegerExpr := .pow (100000000, 1222830961) e21 4
  let e34 : LowMeanIntegerExpr := .mul (195400000, 1222830961) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-195400000, 1222830961) e34
  let e36 : LowMeanIntegerExpr := .add (-6452897599805381, 36684928830000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-6452530750517081, 36684928830000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (6452897599805381, 36684928830000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0135 : LowMeanDirectSeedInput :=
  { record := 135, positions := [], target := { R := 4, expr := lowMeanSeedTargetExpr0135 } }

noncomputable def lowMeanSeedTargetExpr0136 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (3029, 50000)
  let e2 : LowMeanIntegerExpr := .atom (9609, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (5, 1)
  let e4 : LowMeanIntegerExpr := .atom (31, 2)
  let e5 : LowMeanIntegerExpr := .neg (-31, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-21, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-201789, 20000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (1009811, 20000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (6041, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (441, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (2664081, 40000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-2664081, 40000000) e11
  let e13 : LowMeanIntegerExpr := .add (-644459, 40000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (357, 25000)
  let e15 : LowMeanIntegerExpr := .atom (87, 187)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (23, 48)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-87, 187) e15
  let e21 : LowMeanIntegerExpr := .add (100, 187) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (8700, 34969) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-23, 48) e17
  let e24 : LowMeanIntegerExpr := .add (25, 48) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (575, 2304) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (575, 2304) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (575, 2304) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (575, 2304) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2737, 768000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (2737, 153600) e29 e3
  let e31 : LowMeanIntegerExpr := .add (819617, 480000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (977, 500)
  let e33 : LowMeanIntegerExpr := .pow (10000000000, 228669389707) e21 5
  let e34 : LowMeanIntegerExpr := .mul (19540000000, 228669389707) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-19540000000, 228669389707) e34
  let e36 : LowMeanIntegerExpr := .add (-9191778680816517781, 109761307059360000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-9190681067745924181, 109761307059360000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (9191778680816517781, 109761307059360000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0136 : LowMeanDirectSeedInput :=
  { record := 136, positions := [{ j := 4, mode := 0, left := 421, right := 0 }], target := { R := 5, expr := lowMeanSeedTargetExpr0136 } }

noncomputable def lowMeanSeedTargetExpr0137 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (3029, 50000)
  let e2 : LowMeanIntegerExpr := .atom (9609, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (6, 1)
  let e4 : LowMeanIntegerExpr := .atom (31, 2)
  let e5 : LowMeanIntegerExpr := .neg (-31, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-19, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-182571, 20000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (1029029, 20000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (6041, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (361, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (2180801, 40000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-2180801, 40000000) e11
  let e13 : LowMeanIntegerExpr := .add (-122743, 40000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (357, 25000)
  let e15 : LowMeanIntegerExpr := .atom (87, 187)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (23, 48)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-87, 187) e15
  let e21 : LowMeanIntegerExpr := .add (100, 187) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (8700, 34969) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-23, 48) e17
  let e24 : LowMeanIntegerExpr := .add (25, 48) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (575, 2304) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (575, 2304) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (575, 2304) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (575, 2304) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2737, 768000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (2737, 128000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (1465139, 80000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (977, 500)
  let e33 : LowMeanIntegerExpr := .pow (1000000000000, 42761175875209) e21 6
  let e34 : LowMeanIntegerExpr := .mul (1954000000000, 42761175875209) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1954000000000, 42761175875209) e34
  let e36 : LowMeanIntegerExpr := .add (-93668933539372160949, 3420894070016720000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-93634724598671993749, 3420894070016720000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (93668933539372160949, 3420894070016720000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0137 : LowMeanDirectSeedInput :=
  { record := 137, positions := [{ j := 5, mode := 0, left := 422, right := 0 }], target := { R := 6, expr := lowMeanSeedTargetExpr0137 } }

noncomputable def lowMeanSeedTargetExpr0138 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (3029, 50000)
  let e2 : LowMeanIntegerExpr := .atom (9609, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (7, 1)
  let e4 : LowMeanIntegerExpr := .atom (31, 2)
  let e5 : LowMeanIntegerExpr := .neg (-31, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-17, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-163353, 20000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (1048247, 20000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (6041, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (289, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1745849, 40000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1745849, 40000000) e11
  let e13 : LowMeanIntegerExpr := .add (70129, 8000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (357, 25000)
  let e15 : LowMeanIntegerExpr := .atom (87, 187)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (23, 48)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-87, 187) e15
  let e21 : LowMeanIntegerExpr := .add (100, 187) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (8700, 34969) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-23, 48) e17
  let e24 : LowMeanIntegerExpr := .add (25, 48) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (575, 2304) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (575, 2304) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (575, 2304) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (575, 2304) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2737, 768000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (19159, 768000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (3236423, 96000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (977, 500)
  let e33 : LowMeanIntegerExpr := .pow (100000000000000, 7996339888664083) e21 7
  let e34 : LowMeanIntegerExpr := .mul (195400000000000, 7996339888664083) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-195400000000000, 7996339888664083) e34
  let e36 : LowMeanIntegerExpr := .add (7121138331489877495109, 767648629311751968000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (7128814817782995014789, 767648629311751968000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-7121138331489877495109, 767648629311751968000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0138 : LowMeanDirectSeedInput :=
  { record := 138, positions := [{ j := 5, mode := 0, left := 423, right := 0 }], target := { R := 7, expr := lowMeanSeedTargetExpr0138 } }

noncomputable def lowMeanSeedTargetExpr0139 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (3029, 50000)
  let e2 : LowMeanIntegerExpr := .atom (9609, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (8, 1)
  let e4 : LowMeanIntegerExpr := .atom (31, 2)
  let e5 : LowMeanIntegerExpr := .neg (-31, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-15, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-28827, 4000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (213493, 4000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (6041, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (225, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (54369, 1600000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-54369, 1600000) e11
  let e13 : LowMeanIntegerExpr := .add (155141, 8000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (357, 25000)
  let e15 : LowMeanIntegerExpr := .atom (87, 187)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (23, 48)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-87, 187) e15
  let e21 : LowMeanIntegerExpr := .add (100, 187) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (8700, 34969) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-23, 48) e17
  let e24 : LowMeanIntegerExpr := .add (25, 48) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (575, 2304) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (575, 2304) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (575, 2304) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (575, 2304) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2737, 768000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (2737, 96000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (1149673, 24000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (977, 500)
  let e33 : LowMeanIntegerExpr := .pow (10000000000000000, 1495315559180183521) e21 8
  let e34 : LowMeanIntegerExpr := .mul (19540000000000000, 1495315559180183521) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-19540000000000000, 1495315559180183521) e34
  let e36 : LowMeanIntegerExpr := .add (1250163924869359129138633, 35887573420324404504000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (1250522800603562373183673, 35887573420324404504000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-1250163924869359129138633, 35887573420324404504000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0139 : LowMeanDirectSeedInput :=
  { record := 139, positions := [{ j := 6, mode := 0, left := 424, right := 0 }], target := { R := 8, expr := lowMeanSeedTargetExpr0139 } }

noncomputable def lowMeanSeedTargetExpr0140 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (3029, 50000)
  let e2 : LowMeanIntegerExpr := .atom (9609, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (9, 1)
  let e4 : LowMeanIntegerExpr := .atom (31, 2)
  let e5 : LowMeanIntegerExpr := .neg (-31, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-13, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-124917, 20000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (1086683, 20000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (6041, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (169, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1020929, 40000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1020929, 40000000) e11
  let e13 : LowMeanIntegerExpr := .add (1152437, 40000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (357, 25000)
  let e15 : LowMeanIntegerExpr := .atom (87, 187)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (23, 48)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-87, 187) e15
  let e21 : LowMeanIntegerExpr := .add (100, 187) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (8700, 34969) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-23, 48) e17
  let e24 : LowMeanIntegerExpr := .add (25, 48) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (575, 2304) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (575, 2304) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (575, 2304) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (575, 2304) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2737, 768000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (8211, 256000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (9741623, 160000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (977, 500)
  let e33 : LowMeanIntegerExpr := .pow (1000000000000000000, 279624009566694318427) e21 9
  let e34 : LowMeanIntegerExpr := .mul (1954000000000000000, 279624009566694318427) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1954000000000000000, 279624009566694318427) e34
  let e36 : LowMeanIntegerExpr := .add (2411351682947129406357787021, 44739841530671090948320000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (2411799081362436117267270221, 44739841530671090948320000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-2411351682947129406357787021, 44739841530671090948320000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0140 : LowMeanDirectSeedInput :=
  { record := 140, positions := [{ j := 6, mode := 0, left := 425, right := 0 }], target := { R := 9, expr := lowMeanSeedTargetExpr0140 } }

noncomputable def lowMeanSeedTargetExpr0141 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (3029, 50000)
  let e2 : LowMeanIntegerExpr := .atom (9609, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (10, 1)
  let e4 : LowMeanIntegerExpr := .atom (31, 2)
  let e5 : LowMeanIntegerExpr := .neg (-31, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-11, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-105699, 20000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (1105901, 20000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (6041, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (121, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (730961, 40000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-730961, 40000000) e11
  let e13 : LowMeanIntegerExpr := .add (1480841, 40000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (357, 25000)
  let e15 : LowMeanIntegerExpr := .atom (87, 187)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (23, 48)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-87, 187) e15
  let e21 : LowMeanIntegerExpr := .add (100, 187) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (8700, 34969) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-23, 48) e17
  let e24 : LowMeanIntegerExpr := .add (25, 48) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (575, 2304) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (575, 2304) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (575, 2304) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (575, 2304) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2737, 768000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (2737, 76800) e29 e3
  let e31 : LowMeanIntegerExpr := .add (17438171, 240000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (977, 500)
  let e33 : LowMeanIntegerExpr := .pow (100000000000000000000, 52289689788971837545849) e21 10
  let e34 : LowMeanIntegerExpr := .mul (195400000000000000000, 52289689788971837545849) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-195400000000000000000, 52289689788971837545849) e34
  let e36 : LowMeanIntegerExpr := .add (864940552077044817308735202179, 12549525549353241011003760000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (865066047332538349718845239779, 12549525549353241011003760000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-864940552077044817308735202179, 12549525549353241011003760000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0141 : LowMeanDirectSeedInput :=
  { record := 141, positions := [{ j := 7, mode := 0, left := 426, right := 0 }], target := { R := 10, expr := lowMeanSeedTargetExpr0141 } }

noncomputable def lowMeanSeedTargetExpr0142 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (3029, 50000)
  let e2 : LowMeanIntegerExpr := .atom (9609, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (11, 1)
  let e4 : LowMeanIntegerExpr := .atom (31, 2)
  let e5 : LowMeanIntegerExpr := .neg (-31, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-9, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-86481, 20000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (1125119, 20000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (6041, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (81, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (489321, 40000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-489321, 40000000) e11
  let e13 : LowMeanIntegerExpr := .add (1760917, 40000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (357, 25000)
  let e15 : LowMeanIntegerExpr := .atom (87, 187)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (23, 48)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-87, 187) e15
  let e21 : LowMeanIntegerExpr := .add (100, 187) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (8700, 34969) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-23, 48) e17
  let e24 : LowMeanIntegerExpr := .add (25, 48) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (575, 2304) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (575, 2304) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (575, 2304) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (575, 2304) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2737, 768000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (30107, 768000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (39947879, 480000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (977, 500)
  let e33 : LowMeanIntegerExpr := .pow (10000000000000000000000, 9778171990537733621073763) e21 11
  let e34 : LowMeanIntegerExpr := .mul (19540000000000000000000, 9778171990537733621073763) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-19540000000000000000000, 9778171990537733621073763) e34
  let e36 : LowMeanIntegerExpr := .add (381238031519190527628886534398677, 4693522555458112138115406240000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (381284966744745108750267688461077, 4693522555458112138115406240000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-381238031519190527628886534398677, 4693522555458112138115406240000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0142 : LowMeanDirectSeedInput :=
  { record := 142, positions := [{ j := 7, mode := 0, left := 427, right := 0 }], target := { R := 11, expr := lowMeanSeedTargetExpr0142 } }

noncomputable def lowMeanSeedTargetExpr0143 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (3029, 50000)
  let e2 : LowMeanIntegerExpr := .atom (9609, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (12, 1)
  let e4 : LowMeanIntegerExpr := .atom (31, 2)
  let e5 : LowMeanIntegerExpr := .neg (-31, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-7, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-67263, 20000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (1144337, 20000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (6041, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (49, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (296009, 40000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-296009, 40000000) e11
  let e13 : LowMeanIntegerExpr := .add (398533, 8000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (357, 25000)
  let e15 : LowMeanIntegerExpr := .atom (87, 187)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (23, 48)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-87, 187) e15
  let e21 : LowMeanIntegerExpr := .add (100, 187) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (8700, 34969) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-23, 48) e17
  let e24 : LowMeanIntegerExpr := .add (25, 48) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (575, 2304) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (575, 2304) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (575, 2304) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (575, 2304) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2737, 768000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (2737, 64000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (370329, 4000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (977, 500)
  let e33 : LowMeanIntegerExpr := .pow (1000000000000000000000000, 1828518162230556187140793681) e21 12
  let e34 : LowMeanIntegerExpr := .mul (1954000000000000000000000, 1828518162230556187140793681) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1954000000000000000000000, 1828518162230556187140793681) e34
  let e36 : LowMeanIntegerExpr := .add (669337302500679642227662983091049, 7314072648922224748563174724000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (669410443227168864475148614838289, 7314072648922224748563174724000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-669337302500679642227662983091049, 7314072648922224748563174724000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0143 : LowMeanDirectSeedInput :=
  { record := 143, positions := [{ j := 3, mode := 0, left := 428, right := 0 }], target := { R := 12, expr := lowMeanSeedTargetExpr0143 } }

noncomputable def lowMeanSeedGroup0128 : List LowMeanDirectSeedInput := [lowMeanSeedRecord0128, lowMeanSeedRecord0129, lowMeanSeedRecord0130, lowMeanSeedRecord0131, lowMeanSeedRecord0132, lowMeanSeedRecord0133, lowMeanSeedRecord0134, lowMeanSeedRecord0135, lowMeanSeedRecord0136, lowMeanSeedRecord0137, lowMeanSeedRecord0138, lowMeanSeedRecord0139, lowMeanSeedRecord0140, lowMeanSeedRecord0141, lowMeanSeedRecord0142, lowMeanSeedRecord0143]

end Erdos993Lean.Analytic.V213
