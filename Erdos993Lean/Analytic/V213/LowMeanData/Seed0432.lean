module

public import Erdos993Lean.Analytic.V213.LowMeanCoreAll
public import Erdos993Lean.Analytic.V213.LowMeanData.Seed0304
public import Erdos993Lean.Analytic.V213.LowMeanFiberSeed
public import Erdos993Lean.Analytic.V213.LowMeanIntegerExpr
public import Erdos993Lean.Analytic.V213.LowMeanSeedGeometry
public import Erdos993Lean.Analytic.V213.LowMeanWidthData
public import Erdos993Lean.Ceiling.Prefix
public import Erdos993Lean.Ceiling.Statement

/-! Exact core/budget keys and equation-51 targets for the direct fibers. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanSeedTargetExpr0432 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (16041, 100000)
  let e2 : LowMeanIntegerExpr := .atom (2637, 500000)
  let e3 : LowMeanIntegerExpr := .atom (3, 1)
  let e4 : LowMeanIntegerExpr := .atom (19, 2)
  let e5 : LowMeanIntegerExpr := .neg (-19, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-13, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-34281, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (126129, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1783, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (169, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (301327, 4000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-301327, 4000000) e11
  let e13 : LowMeanIntegerExpr := .add (203189, 4000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (3781, 100000)
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
  let e29 : LowMeanIntegerExpr := .mul (3781, 422500) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (11343, 422500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (52487741, 676000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (8501, 10000)
  let e33 : LowMeanIntegerExpr := .pow (125, 2197) e21 3
  let e34 : LowMeanIntegerExpr := .mul (8501, 175760) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-8501, 175760) e34
  let e36 : LowMeanIntegerExpr := .add (257290633, 8788000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (257378513, 8788000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-257290633, 8788000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0432 : LowMeanDirectSeedInput :=
  { record := 432, positions := [], target := { R := 3, expr := lowMeanSeedTargetExpr0432 } }

noncomputable def lowMeanSeedTargetExpr0433 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (16041, 100000)
  let e2 : LowMeanIntegerExpr := .atom (2637, 500000)
  let e3 : LowMeanIntegerExpr := .atom (4, 1)
  let e4 : LowMeanIntegerExpr := .atom (19, 2)
  let e5 : LowMeanIntegerExpr := .neg (-19, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-11, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-29007, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (131403, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1783, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (121, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (215743, 4000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-215743, 4000000) e11
  let e13 : LowMeanIntegerExpr := .add (309869, 4000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (3781, 100000)
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
  let e29 : LowMeanIntegerExpr := .mul (3781, 422500) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (3781, 105625) e29 e3
  let e31 : LowMeanIntegerExpr := .add (76566261, 676000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (8501, 10000)
  let e33 : LowMeanIntegerExpr := .pow (625, 28561) e21 4
  let e34 : LowMeanIntegerExpr := .mul (8501, 456976) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-8501, 456976) e34
  let e36 : LowMeanIntegerExpr := .add (10814448109, 114244000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (10815590549, 114244000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-10814448109, 114244000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0433 : LowMeanDirectSeedInput :=
  { record := 433, positions := [{ j := 1, mode := 0, left := 932, right := 0 }], target := { R := 4, expr := lowMeanSeedTargetExpr0433 } }

noncomputable def lowMeanSeedTargetExpr0434 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (16041, 100000)
  let e2 : LowMeanIntegerExpr := .atom (2637, 500000)
  let e3 : LowMeanIntegerExpr := .atom (5, 1)
  let e4 : LowMeanIntegerExpr := .atom (19, 2)
  let e5 : LowMeanIntegerExpr := .neg (-19, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-9, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-23733, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (136677, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1783, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (81, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (144423, 4000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-144423, 4000000) e11
  let e13 : LowMeanIntegerExpr := .add (80457, 800000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (3781, 100000)
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
  let e29 : LowMeanIntegerExpr := .mul (3781, 422500) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (3781, 84500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (19646833, 135200000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (8501, 10000)
  let e33 : LowMeanIntegerExpr := .pow (3125, 371293) e21 5
  let e34 : LowMeanIntegerExpr := .mul (42505, 5940688) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-42505, 5940688) e34
  let e36 : LowMeanIntegerExpr := .add (41038842101, 297034400000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (8208362489, 59406880000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-41038842101, 297034400000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0434 : LowMeanDirectSeedInput :=
  { record := 434, positions := [], target := { R := 5, expr := lowMeanSeedTargetExpr0434 } }

noncomputable def lowMeanSeedTargetExpr0435 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (16041, 100000)
  let e2 : LowMeanIntegerExpr := .atom (2637, 500000)
  let e3 : LowMeanIntegerExpr := .atom (6, 1)
  let e4 : LowMeanIntegerExpr := .atom (19, 2)
  let e5 : LowMeanIntegerExpr := .neg (-19, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-7, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-18459, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (141951, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1783, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (49, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (87367, 4000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-87367, 4000000) e11
  let e13 : LowMeanIntegerExpr := .add (480437, 4000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (3781, 100000)
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
  let e29 : LowMeanIntegerExpr := .mul (3781, 422500) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (11343, 211250) e29 e3
  let e31 : LowMeanIntegerExpr := .add (117491453, 676000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (8501, 10000)
  let e33 : LowMeanIntegerExpr := .pow (15625, 4826809) e21 6
  let e34 : LowMeanIntegerExpr := .mul (212525, 77228944) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-212525, 77228944) e34
  let e36 : LowMeanIntegerExpr := .add (3302542139133, 19307236000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (3302735211493, 19307236000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-3302542139133, 19307236000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0435 : LowMeanDirectSeedInput :=
  { record := 435, positions := [], target := { R := 6, expr := lowMeanSeedTargetExpr0435 } }

noncomputable def lowMeanSeedTargetExpr0436 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (16041, 100000)
  let e2 : LowMeanIntegerExpr := .atom (2637, 500000)
  let e3 : LowMeanIntegerExpr := .atom (7, 1)
  let e4 : LowMeanIntegerExpr := .atom (19, 2)
  let e5 : LowMeanIntegerExpr := .neg (-19, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-5, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-2637, 200000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (5889, 40000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1783, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (25, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1783, 160000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1783, 160000) e11
  let e13 : LowMeanIntegerExpr := .add (21773, 160000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (3781, 100000)
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
  let e29 : LowMeanIntegerExpr := .mul (3781, 422500) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (26467, 422500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (214941, 1081600) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (8501, 10000)
  let e33 : LowMeanIntegerExpr := .pow (78125, 62748517) e21 7
  let e34 : LowMeanIntegerExpr := .mul (1062625, 1003976272) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1062625, 1003976272) e34
  let e36 : LowMeanIntegerExpr := .add (79381038713, 401590508800) e31 e35
  let e37 : LowMeanIntegerExpr := .add (9923131827261, 50198813600000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-79381038713, 401590508800) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0436 : LowMeanDirectSeedInput :=
  { record := 436, positions := [{ j := 7, mode := 0, left := 933, right := 0 }], target := { R := 7, expr := lowMeanSeedTargetExpr0436 } }

noncomputable def lowMeanSeedTargetExpr0437 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (16041, 100000)
  let e2 : LowMeanIntegerExpr := .atom (2637, 500000)
  let e3 : LowMeanIntegerExpr := .atom (8, 1)
  let e4 : LowMeanIntegerExpr := .atom (19, 2)
  let e5 : LowMeanIntegerExpr := .neg (-19, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-3, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-7911, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (152499, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1783, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (9, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (16047, 4000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-16047, 4000000) e11
  let e13 : LowMeanIntegerExpr := .add (593949, 4000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (3781, 100000)
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
  let e29 : LowMeanIntegerExpr := .mul (3781, 422500) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (7562, 105625) e29 e3
  let e31 : LowMeanIntegerExpr := .add (148774181, 676000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (8501, 10000)
  let e33 : LowMeanIntegerExpr := .pow (390625, 815730721) e21 8
  let e34 : LowMeanIntegerExpr := .mul (5313125, 13051691536) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-5313125, 13051691536) e34
  let e36 : LowMeanIntegerExpr := .add (716776274568429, 3262922884000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (716808903797269, 3262922884000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-716776274568429, 3262922884000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0437 : LowMeanDirectSeedInput :=
  { record := 437, positions := [{ j := 4, mode := 0, left := 934, right := 0 }], target := { R := 8, expr := lowMeanSeedTargetExpr0437 } }

noncomputable def lowMeanSeedTargetExpr0438 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (16041, 100000)
  let e2 : LowMeanIntegerExpr := .atom (2637, 500000)
  let e3 : LowMeanIntegerExpr := .atom (9, 1)
  let e4 : LowMeanIntegerExpr := .atom (19, 2)
  let e5 : LowMeanIntegerExpr := .neg (-19, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-1, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-2637, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (157773, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1783, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (1, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1783, 4000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1783, 4000000) e11
  let e13 : LowMeanIntegerExpr := .add (629309, 4000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (3781, 100000)
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
  let e29 : LowMeanIntegerExpr := .mul (3781, 422500) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (34029, 422500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (160799621, 676000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (8501, 10000)
  let e33 : LowMeanIntegerExpr := .pow (1953125, 10604499373) e21 9
  let e34 : LowMeanIntegerExpr := .mul (26565625, 169671989968) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-26565625, 169671989968) e34
  let e36 : LowMeanIntegerExpr := .add (10083296345662057, 42417997492000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (10083720525636977, 42417997492000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-10083296345662057, 42417997492000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0438 : LowMeanDirectSeedInput :=
  { record := 438, positions := [{ j := 8, mode := 0, left := 935, right := 0 }], target := { R := 9, expr := lowMeanSeedTargetExpr0438 } }

noncomputable def lowMeanSeedTargetExpr0439 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (16041, 100000)
  let e2 : LowMeanIntegerExpr := .atom (2637, 500000)
  let e3 : LowMeanIntegerExpr := .atom (10, 1)
  let e4 : LowMeanIntegerExpr := .atom (19, 2)
  let e5 : LowMeanIntegerExpr := .neg (-19, 2) e4
  let e6 : LowMeanIntegerExpr := .add (1, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (2637, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (163047, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1783, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (1, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1783, 4000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1783, 4000000) e11
  let e13 : LowMeanIntegerExpr := .add (130081, 800000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (3781, 100000)
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
  let e29 : LowMeanIntegerExpr := .mul (3781, 422500) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (3781, 42250) e29 e3
  let e31 : LowMeanIntegerExpr := .add (34082889, 135200000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (8501, 10000)
  let e33 : LowMeanIntegerExpr := .pow (9765625, 137858491849) e21 10
  let e34 : LowMeanIntegerExpr := .mul (132828125, 2205735869584) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-132828125, 2205735869584) e34
  let e36 : LowMeanIntegerExpr := .add (27795818211482969, 110286793479200000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (27796921079417761, 110286793479200000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-27795818211482969, 110286793479200000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0439 : LowMeanDirectSeedInput :=
  { record := 439, positions := [{ j := 5, mode := 0, left := 936, right := 0 }, { j := 8, mode := 0, left := 937, right := 0 }, { j := 9, mode := 0, left := 938, right := 0 }], target := { R := 10, expr := lowMeanSeedTargetExpr0439 } }

noncomputable def lowMeanSeedTargetExpr0440 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (16041, 100000)
  let e2 : LowMeanIntegerExpr := .atom (2637, 500000)
  let e3 : LowMeanIntegerExpr := .atom (11, 1)
  let e4 : LowMeanIntegerExpr := .atom (19, 2)
  let e5 : LowMeanIntegerExpr := .neg (-19, 2) e4
  let e6 : LowMeanIntegerExpr := .add (3, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (7911, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (168321, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1783, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (9, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (16047, 4000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-16047, 4000000) e11
  let e13 : LowMeanIntegerExpr := .add (657237, 4000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (3781, 100000)
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
  let e29 : LowMeanIntegerExpr := .mul (3781, 422500) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (41591, 422500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (177618653, 676000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (8501, 10000)
  let e33 : LowMeanIntegerExpr := .pow (48828125, 1792160394037) e21 11
  let e34 : LowMeanIntegerExpr := .mul (664140625, 28674566304592) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-664140625, 28674566304592) e34
  let e36 : LowMeanIntegerExpr := .add (1883390859215354569, 7168641576148000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (1883462545631116049, 7168641576148000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-1883390859215354569, 7168641576148000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0440 : LowMeanDirectSeedInput :=
  { record := 440, positions := [{ j := 6, mode := 0, left := 939, right := 0 }, { j := 9, mode := 0, left := 940, right := 0 }], target := { R := 11, expr := lowMeanSeedTargetExpr0440 } }

noncomputable def lowMeanSeedTargetExpr0441 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (16041, 100000)
  let e2 : LowMeanIntegerExpr := .atom (2637, 500000)
  let e3 : LowMeanIntegerExpr := .atom (12, 1)
  let e4 : LowMeanIntegerExpr := .atom (19, 2)
  let e5 : LowMeanIntegerExpr := .neg (-19, 2) e4
  let e6 : LowMeanIntegerExpr := .add (5, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (2637, 200000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (34719, 200000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1783, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (25, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1783, 160000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1783, 160000) e11
  let e13 : LowMeanIntegerExpr := .add (129961, 800000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (3781, 100000)
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
  let e29 : LowMeanIntegerExpr := .mul (3781, 422500) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (11343, 105625) e29 e3
  let e31 : LowMeanIntegerExpr := .add (36482449, 135200000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (8501, 10000)
  let e33 : LowMeanIntegerExpr := .pow (244140625, 23298085122481) e21 12
  let e34 : LowMeanIntegerExpr := .mul (3320703125, 372769361959696) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-3320703125, 372769361959696) e34
  let e36 : LowMeanIntegerExpr := .add (5029249362941808201, 18638468097984800000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (5029435747622788049, 18638468097984800000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-5029249362941808201, 18638468097984800000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0441 : LowMeanDirectSeedInput :=
  { record := 441, positions := [{ j := 7, mode := 0, left := 941, right := 0 }, { j := 9, mode := 0, left := 942, right := 0 }, { j := 10, mode := 0, left := 943, right := 0 }], target := { R := 12, expr := lowMeanSeedTargetExpr0441 } }

noncomputable def lowMeanSeedTargetExpr0442 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (16041, 100000)
  let e2 : LowMeanIntegerExpr := .atom (2637, 500000)
  let e3 : LowMeanIntegerExpr := .atom (13, 1)
  let e4 : LowMeanIntegerExpr := .atom (19, 2)
  let e5 : LowMeanIntegerExpr := .neg (-19, 2) e4
  let e6 : LowMeanIntegerExpr := .add (7, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (18459, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (178869, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1783, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (49, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (87367, 4000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-87367, 4000000) e11
  let e13 : LowMeanIntegerExpr := .add (628109, 4000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (3781, 100000)
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
  let e29 : LowMeanIntegerExpr := .mul (3781, 422500) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (3781, 32500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (14215017, 52000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (8501, 10000)
  let e33 : LowMeanIntegerExpr := .pow (1220703125, 302875106592253) e21 13
  let e34 : LowMeanIntegerExpr := .mul (16603515625, 4846001705476048) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-16603515625, 4846001705476048) e34
  let e36 : LowMeanIntegerExpr := .add (331178525204608247177, 1211500426369012000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (331190640208871937297, 1211500426369012000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-331178525204608247177, 1211500426369012000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0442 : LowMeanDirectSeedInput :=
  { record := 442, positions := [{ j := 8, mode := 0, left := 944, right := 0 }, { j := 10, mode := 0, left := 945, right := 0 }, { j := 11, mode := 0, left := 946, right := 0 }], target := { R := 13, expr := lowMeanSeedTargetExpr0442 } }

noncomputable def lowMeanSeedTargetExpr0443 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (84077, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (129, 100000)
  let e3 : LowMeanIntegerExpr := .atom (0, 1)
  let e4 : LowMeanIntegerExpr := .atom (57, 2)
  let e5 : LowMeanIntegerExpr := .neg (-57, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-57, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-7353, 200000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (2957, 62500) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (137, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (3249, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (445113, 4000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-445113, 4000000) e11
  let e13 : LowMeanIntegerExpr := .add (-51173, 800000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (0, 1) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-51173, 800000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (79, 20)
  let e33 : LowMeanIntegerExpr := .pow (1, 1) e21 0
  let e34 : LowMeanIntegerExpr := .mul (79, 20) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-79, 20) e34
  let e36 : LowMeanIntegerExpr := .add (-3211173, 800000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-642233, 160000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (3211173, 800000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0443 : LowMeanDirectSeedInput :=
  { record := 443, positions := [], target := { R := 0, expr := lowMeanSeedTargetExpr0443 } }

noncomputable def lowMeanSeedTargetExpr0444 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (84077, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (129, 100000)
  let e3 : LowMeanIntegerExpr := .atom (1, 1)
  let e4 : LowMeanIntegerExpr := .atom (57, 2)
  let e5 : LowMeanIntegerExpr := .neg (-57, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-55, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1419, 40000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (24301, 500000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (137, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (3025, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (16577, 160000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-16577, 160000) e11
  let e13 : LowMeanIntegerExpr := .add (-220017, 4000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (2773, 500000)
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
  let e28 : LowMeanIntegerExpr := .mul (2773, 2112500) e14 e27
  let e29 : LowMeanIntegerExpr := .mul (2773, 2112500) e28 e3
  let e30 : LowMeanIntegerExpr := .add (-36295513, 676000000) e13 e29
  let e31 : LowMeanIntegerExpr := .atom (79, 20)
  let e32 : LowMeanIntegerExpr := .pow (5, 13) e20 1
  let e33 : LowMeanIntegerExpr := .mul (79, 52) e31 e32
  let e34 : LowMeanIntegerExpr := .neg (-79, 52) e33
  let e35 : LowMeanIntegerExpr := .add (-1063295513, 676000000) e30 e34
  let e36 : LowMeanIntegerExpr := .add (-1063288753, 676000000) e0 e35
  let e37 : LowMeanIntegerExpr := .neg (1063295513, 676000000) e35
  let e38 : LowMeanIntegerExpr := .add (1, 100000) e36 e37
  e38

noncomputable def lowMeanSeedRecord0444 : LowMeanDirectSeedInput :=
  { record := 444, positions := [], target := { R := 1, expr := lowMeanSeedTargetExpr0444 } }

noncomputable def lowMeanSeedTargetExpr0445 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (84077, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (129, 100000)
  let e3 : LowMeanIntegerExpr := .atom (2, 1)
  let e4 : LowMeanIntegerExpr := .atom (57, 2)
  let e5 : LowMeanIntegerExpr := .neg (-57, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-53, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-6837, 200000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (12473, 250000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (137, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (2809, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (384833, 4000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-384833, 4000000) e11
  let e13 : LowMeanIntegerExpr := .add (-37053, 800000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (2773, 1056250) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-5907013, 135200000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (79, 20)
  let e33 : LowMeanIntegerExpr := .pow (25, 169) e21 2
  let e34 : LowMeanIntegerExpr := .mul (395, 676) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-395, 676) e34
  let e36 : LowMeanIntegerExpr := .add (-84907013, 135200000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-84905661, 135200000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (84907013, 135200000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0445 : LowMeanDirectSeedInput :=
  { record := 445, positions := [], target := { R := 2, expr := lowMeanSeedTargetExpr0445 } }

noncomputable def lowMeanSeedTargetExpr0446 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (84077, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (129, 100000)
  let e3 : LowMeanIntegerExpr := .atom (3, 1)
  let e4 : LowMeanIntegerExpr := .atom (57, 2)
  let e5 : LowMeanIntegerExpr := .neg (-57, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-51, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-6579, 200000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (25591, 500000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (137, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (2601, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (356337, 4000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-356337, 4000000) e11
  let e13 : LowMeanIntegerExpr := .add (-151609, 4000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (8319, 2112500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-22959841, 676000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (79, 20)
  let e33 : LowMeanIntegerExpr := .pow (125, 2197) e21 3
  let e34 : LowMeanIntegerExpr := .mul (1975, 8788) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1975, 8788) e34
  let e36 : LowMeanIntegerExpr := .add (-2273477933, 8788000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-2273390053, 8788000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (2273477933, 8788000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0446 : LowMeanDirectSeedInput :=
  { record := 446, positions := [], target := { R := 3, expr := lowMeanSeedTargetExpr0446 } }

noncomputable def lowMeanSeedTargetExpr0447 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (84077, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (129, 100000)
  let e3 : LowMeanIntegerExpr := .atom (4, 1)
  let e4 : LowMeanIntegerExpr := .atom (57, 2)
  let e5 : LowMeanIntegerExpr := .neg (-57, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-49, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-6321, 200000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (6559, 125000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (137, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (2401, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (328937, 4000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-328937, 4000000) e11
  let e13 : LowMeanIntegerExpr := .add (-119049, 4000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (2773, 528125) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-16569841, 676000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (79, 20)
  let e33 : LowMeanIntegerExpr := .pow (625, 28561) e21 4
  let e34 : LowMeanIntegerExpr := .mul (9875, 114244) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-9875, 114244) e34
  let e36 : LowMeanIntegerExpr := .add (-12675303129, 114244000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-12674160689, 114244000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (12675303129, 114244000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0447 : LowMeanDirectSeedInput :=
  { record := 447, positions := [], target := { R := 4, expr := lowMeanSeedTargetExpr0447 } }

noncomputable def lowMeanSeedGroup0432 : List LowMeanDirectSeedInput := [lowMeanSeedRecord0432, lowMeanSeedRecord0433, lowMeanSeedRecord0434, lowMeanSeedRecord0435, lowMeanSeedRecord0436, lowMeanSeedRecord0437, lowMeanSeedRecord0438, lowMeanSeedRecord0439, lowMeanSeedRecord0440, lowMeanSeedRecord0441, lowMeanSeedRecord0442, lowMeanSeedRecord0443, lowMeanSeedRecord0444, lowMeanSeedRecord0445, lowMeanSeedRecord0446, lowMeanSeedRecord0447]

end Erdos993Lean.Analytic.V213
