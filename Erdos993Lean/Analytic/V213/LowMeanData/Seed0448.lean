module

public import Erdos993Lean.Analytic.V213.LowMeanCoreAll
public import Erdos993Lean.Analytic.V213.LowMeanData.Seed0336
public import Erdos993Lean.Analytic.V213.LowMeanFiberSeed
public import Erdos993Lean.Analytic.V213.LowMeanIntegerExpr
public import Erdos993Lean.Analytic.V213.LowMeanSeedGeometry
public import Erdos993Lean.Analytic.V213.LowMeanWidthData
public import Erdos993Lean.Ceiling.Prefix
public import Erdos993Lean.Ceiling.Statement

/-! Exact core/budget keys and equation-51 targets for the direct fibers. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanSeedTargetExpr0448 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (84077, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (129, 100000)
  let e3 : LowMeanIntegerExpr := .atom (5, 1)
  let e4 : LowMeanIntegerExpr := .atom (57, 2)
  let e5 : LowMeanIntegerExpr := .neg (-57, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-47, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-6063, 200000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (26881, 500000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (137, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (2209, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (302633, 4000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-302633, 4000000) e11
  let e13 : LowMeanIntegerExpr := .add (-17517, 800000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (2773, 422500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-2073013, 135200000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (79, 20)
  let e33 : LowMeanIntegerExpr := .pow (3125, 371293) e21 5
  let e34 : LowMeanIntegerExpr := .mul (49375, 1485172) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-49375, 1485172) e34
  let e36 : LowMeanIntegerExpr := .add (-14429409561, 297034400000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-14426439217, 297034400000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (14429409561, 297034400000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0448 : LowMeanDirectSeedInput :=
  { record := 448, positions := [{ j := 1, mode := 0, left := 947, right := 0 }], target := { R := 5, expr := lowMeanSeedTargetExpr0448 } }

noncomputable def lowMeanSeedTargetExpr0449 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (84077, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (129, 100000)
  let e3 : LowMeanIntegerExpr := .atom (6, 1)
  let e4 : LowMeanIntegerExpr := .atom (57, 2)
  let e5 : LowMeanIntegerExpr := .neg (-57, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-45, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1161, 40000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (13763, 250000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (137, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (2025, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (11097, 160000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-11097, 160000) e11
  let e13 : LowMeanIntegerExpr := .add (-57217, 4000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (8319, 1056250) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-4345513, 676000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (79, 20)
  let e33 : LowMeanIntegerExpr := .pow (15625, 4826809) e21 6
  let e34 : LowMeanIntegerExpr := .mul (246875, 19307236) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-246875, 19307236) e34
  let e36 : LowMeanIntegerExpr := .add (-370987196793, 19307236000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-370794124433, 19307236000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (370987196793, 19307236000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0449 : LowMeanDirectSeedInput :=
  { record := 449, positions := [{ j := 2, mode := 0, left := 948, right := 0 }], target := { R := 6, expr := lowMeanSeedTargetExpr0449 } }

noncomputable def lowMeanSeedTargetExpr0450 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (84077, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (129, 100000)
  let e3 : LowMeanIntegerExpr := .atom (7, 1)
  let e4 : LowMeanIntegerExpr := .atom (57, 2)
  let e5 : LowMeanIntegerExpr := .neg (-57, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-43, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-5547, 200000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (28171, 500000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (137, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (1849, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (253313, 4000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-253313, 4000000) e11
  let e13 : LowMeanIntegerExpr := .add (-5589, 800000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (19411, 2112500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (297763, 135200000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (79, 20)
  let e33 : LowMeanIntegerExpr := .pow (78125, 62748517) e21 7
  let e34 : LowMeanIntegerExpr := .mul (1234375, 250994068) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1234375, 250994068) e34
  let e36 : LowMeanIntegerExpr := .add (-136317682441, 50198813600000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-27163138861, 10039762720000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (136317682441, 50198813600000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0450 : LowMeanDirectSeedInput :=
  { record := 450, positions := [{ j := 2, mode := 0, left := 949, right := 0 }], target := { R := 7, expr := lowMeanSeedTargetExpr0450 } }

noncomputable def lowMeanSeedTargetExpr0451 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (84077, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (129, 100000)
  let e3 : LowMeanIntegerExpr := .atom (8, 1)
  let e4 : LowMeanIntegerExpr := .atom (57, 2)
  let e5 : LowMeanIntegerExpr := .neg (-57, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-41, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-5289, 200000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (1801, 31250) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (137, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (1681, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (230297, 4000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-230297, 4000000) e11
  let e13 : LowMeanIntegerExpr := .add (231, 4000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (5546, 528125) e29 e3
  let e31 : LowMeanIntegerExpr := .add (7137919, 676000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (79, 20)
  let e33 : LowMeanIntegerExpr := .pow (390625, 815730721) e21 8
  let e34 : LowMeanIntegerExpr := .mul (6171875, 3262922884) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-6171875, 3262922884) e34
  let e36 : LowMeanIntegerExpr := .add (28281496670471, 3262922884000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (28314125899311, 3262922884000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-28281496670471, 3262922884000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0451 : LowMeanDirectSeedInput :=
  { record := 451, positions := [{ j := 3, mode := 0, left := 950, right := 0 }], target := { R := 8, expr := lowMeanSeedTargetExpr0451 } }

noncomputable def lowMeanSeedTargetExpr0452 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (84077, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (129, 100000)
  let e3 : LowMeanIntegerExpr := .atom (9, 1)
  let e4 : LowMeanIntegerExpr := .atom (57, 2)
  let e5 : LowMeanIntegerExpr := .neg (-57, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-39, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-5031, 200000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (29461, 500000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (137, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (1521, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (208377, 4000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-208377, 4000000) e11
  let e13 : LowMeanIntegerExpr := .add (27311, 4000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (24957, 2112500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (12601799, 676000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (79, 20)
  let e33 : LowMeanIntegerExpr := .pow (1953125, 10604499373) e21 9
  let e34 : LowMeanIntegerExpr := .mul (30859375, 42417997492) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-30859375, 42417997492) e34
  let e36 : LowMeanIntegerExpr := .add (759884823782083, 42417997492000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (760309003757003, 42417997492000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-759884823782083, 42417997492000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0452 : LowMeanDirectSeedInput :=
  { record := 452, positions := [], target := { R := 9, expr := lowMeanSeedTargetExpr0452 } }

noncomputable def lowMeanSeedTargetExpr0453 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (84077, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (129, 100000)
  let e3 : LowMeanIntegerExpr := .atom (10, 1)
  let e4 : LowMeanIntegerExpr := .atom (57, 2)
  let e5 : LowMeanIntegerExpr := .neg (-57, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-37, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-4773, 200000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (15053, 250000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (137, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (1369, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (187553, 4000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-187553, 4000000) e11
  let e13 : LowMeanIntegerExpr := .add (10659, 800000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (2773, 211250) e29 e3
  let e31 : LowMeanIntegerExpr := .add (3576091, 135200000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (79, 20)
  let e33 : LowMeanIntegerExpr := .pow (9765625, 137858491849) e21 10
  let e34 : LowMeanIntegerExpr := .mul (154296875, 551433967396) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-154296875, 551433967396) e34
  let e36 : LowMeanIntegerExpr := .add (2886267914791611, 110286793479200000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (2887370782726403, 110286793479200000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-2886267914791611, 110286793479200000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0453 : LowMeanDirectSeedInput :=
  { record := 453, positions := [], target := { R := 10, expr := lowMeanSeedTargetExpr0453 } }

noncomputable def lowMeanSeedTargetExpr0454 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (84077, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (129, 100000)
  let e3 : LowMeanIntegerExpr := .atom (11, 1)
  let e4 : LowMeanIntegerExpr := .atom (57, 2)
  let e5 : LowMeanIntegerExpr := .neg (-57, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-35, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-903, 40000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (30751, 500000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (137, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (1225, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (6713, 160000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-6713, 160000) e11
  let e13 : LowMeanIntegerExpr := .add (78183, 4000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (30503, 2112500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (22973887, 676000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (79, 20)
  let e33 : LowMeanIntegerExpr := .pow (48828125, 1792160394037) e21 11
  let e34 : LowMeanIntegerExpr := .mul (771484375, 7168641576148) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-771484375, 7168641576148) e34
  let e36 : LowMeanIntegerExpr := .add (242855085911872851, 7168641576148000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (242926772327634331, 7168641576148000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-242855085911872851, 7168641576148000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0454 : LowMeanDirectSeedInput :=
  { record := 454, positions := [], target := { R := 11, expr := lowMeanSeedTargetExpr0454 } }

noncomputable def lowMeanSeedTargetExpr0455 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (84077, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (129, 100000)
  let e3 : LowMeanIntegerExpr := .atom (12, 1)
  let e4 : LowMeanIntegerExpr := .atom (57, 2)
  let e5 : LowMeanIntegerExpr := .neg (-57, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-33, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-4257, 200000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (7849, 125000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (137, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (1089, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (149193, 4000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-149193, 4000000) e11
  let e13 : LowMeanIntegerExpr := .add (4079, 160000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (8319, 528125) e29 e3
  let e31 : LowMeanIntegerExpr := .add (5576419, 135200000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (79, 20)
  let e33 : LowMeanIntegerExpr := .pow (244140625, 23298085122481) e21 12
  let e34 : LowMeanIntegerExpr := .mul (3857421875, 93192340489924) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-3857421875, 93192340489924) e34
  let e36 : LowMeanIntegerExpr := .add (767985228883108731, 18638468097984800000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (768171613564088579, 18638468097984800000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-767985228883108731, 18638468097984800000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0455 : LowMeanDirectSeedInput :=
  { record := 455, positions := [], target := { R := 12, expr := lowMeanSeedTargetExpr0455 } }

noncomputable def lowMeanSeedTargetExpr0456 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (84077, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (129, 100000)
  let e3 : LowMeanIntegerExpr := .atom (13, 1)
  let e4 : LowMeanIntegerExpr := .atom (57, 2)
  let e5 : LowMeanIntegerExpr := .neg (-57, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-31, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-3999, 200000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (32041, 500000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (137, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (961, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (131657, 4000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-131657, 4000000) e11
  let e13 : LowMeanIntegerExpr := .add (124671, 4000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (2773, 162500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (2508083, 52000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (79, 20)
  let e33 : LowMeanIntegerExpr := .pow (1220703125, 302875106592253) e21 13
  let e34 : LowMeanIntegerExpr := .mul (19287109375, 1211500426369012) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-19287109375, 1211500426369012) e34
  let e36 : LowMeanIntegerExpr := .add (58414244118872513923, 1211500426369012000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (58426359123136204043, 1211500426369012000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-58414244118872513923, 1211500426369012000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0456 : LowMeanDirectSeedInput :=
  { record := 456, positions := [], target := { R := 13, expr := lowMeanSeedTargetExpr0456 } }

noncomputable def lowMeanSeedTargetExpr0457 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (84077, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (129, 100000)
  let e3 : LowMeanIntegerExpr := .atom (14, 1)
  let e4 : LowMeanIntegerExpr := .atom (57, 2)
  let e5 : LowMeanIntegerExpr := .neg (-57, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-29, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-3741, 200000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (16343, 250000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (137, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (841, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (115217, 4000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-115217, 4000000) e11
  let e13 : LowMeanIntegerExpr := .add (146271, 4000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (19411, 1056250) e29 e3
  let e31 : LowMeanIntegerExpr := .add (37142839, 676000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (79, 20)
  let e33 : LowMeanIntegerExpr := .pow (6103515625, 3937376385699289) e21 14
  let e34 : LowMeanIntegerExpr := .mul (96435546875, 15749505542797156) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-96435546875, 15749505542797156) e34
  let e36 : LowMeanIntegerExpr := .add (865260589165732063559, 15749505542797156000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (865418084221160035119, 15749505542797156000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-865260589165732063559, 15749505542797156000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0457 : LowMeanDirectSeedInput :=
  { record := 457, positions := [], target := { R := 14, expr := lowMeanSeedTargetExpr0457 } }

noncomputable def lowMeanSeedTargetExpr0458 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (84077, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (129, 100000)
  let e3 : LowMeanIntegerExpr := .atom (15, 1)
  let e4 : LowMeanIntegerExpr := .atom (57, 2)
  let e5 : LowMeanIntegerExpr := .neg (-57, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-27, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-3483, 200000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (33331, 500000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (137, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (729, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (99873, 4000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-99873, 4000000) e11
  let e13 : LowMeanIntegerExpr := .add (6671, 160000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (8319, 422500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (331963, 5408000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (79, 20)
  let e33 : LowMeanIntegerExpr := .pow (30517578125, 51185893014090757) e21 15
  let e34 : LowMeanIntegerExpr := .mul (482177734375, 204743572056363028) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-482177734375, 204743572056363028) e34
  let e36 : LowMeanIntegerExpr := .add (100539471587809082639, 1637948576450904224000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (2513896276839339792031, 40948714411272605600000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-100539471587809082639, 1637948576450904224000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0458 : LowMeanDirectSeedInput :=
  { record := 458, positions := [], target := { R := 15, expr := lowMeanSeedTargetExpr0458 } }

noncomputable def lowMeanSeedTargetExpr0459 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (84077, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (129, 100000)
  let e3 : LowMeanIntegerExpr := .atom (16, 1)
  let e4 : LowMeanIntegerExpr := .atom (57, 2)
  let e5 : LowMeanIntegerExpr := .neg (-57, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-25, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-129, 8000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (4247, 62500) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (137, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (625, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (137, 6400) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-137, 6400) e11
  let e13 : LowMeanIntegerExpr := .add (186183, 4000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (11092, 528125) e29 e3
  let e31 : LowMeanIntegerExpr := .add (45662687, 676000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (79, 20)
  let e33 : LowMeanIntegerExpr := .pow (152587890625, 665416609183179841) e21 16
  let e34 : LowMeanIntegerExpr := .mul (2410888671875, 2661666436732719364) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-2410888671875, 2661666436732719364) e34
  let e36 : LowMeanIntegerExpr := .add (179788774612706034729543, 2661666436732719364000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (179815391277073361923183, 2661666436732719364000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-179788774612706034729543, 2661666436732719364000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0459 : LowMeanDirectSeedInput :=
  { record := 459, positions := [], target := { R := 16, expr := lowMeanSeedTargetExpr0459 } }

noncomputable def lowMeanSeedTargetExpr0460 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (84077, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (129, 100000)
  let e3 : LowMeanIntegerExpr := .atom (17, 1)
  let e4 : LowMeanIntegerExpr := .atom (57, 2)
  let e5 : LowMeanIntegerExpr := .neg (-57, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-23, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-2967, 200000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (34621, 500000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (137, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (529, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (72473, 4000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-72473, 4000000) e11
  let e13 : LowMeanIntegerExpr := .add (40899, 800000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (47141, 2112500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (1985791, 27040000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (79, 20)
  let e33 : LowMeanIntegerExpr := .pow (762939453125, 8650415919381337933) e21 17
  let e34 : LowMeanIntegerExpr := .mul (12054443359375, 34601663677525351732) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-12054443359375, 34601663677525351732) e34
  let e36 : LowMeanIntegerExpr := .add (101644003496609923433787, 1384066547101014069280000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (508289220810404667872399, 6920332735505070346400000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-101644003496609923433787, 1384066547101014069280000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0460 : LowMeanDirectSeedInput :=
  { record := 460, positions := [{ j := 15, mode := 0, left := 951, right := 0 }], target := { R := 17, expr := lowMeanSeedTargetExpr0460 } }

noncomputable def lowMeanSeedTargetExpr0461 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (84077, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (129, 100000)
  let e3 : LowMeanIntegerExpr := .atom (18, 1)
  let e4 : LowMeanIntegerExpr := .atom (57, 2)
  let e5 : LowMeanIntegerExpr := .neg (-57, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-21, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-2709, 200000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (17633, 250000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (137, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (441, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (60417, 4000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-60417, 4000000) e11
  let e13 : LowMeanIntegerExpr := .add (221711, 4000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (24957, 1056250) e29 e3
  let e31 : LowMeanIntegerExpr := .add (53441639, 676000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (79, 20)
  let e33 : LowMeanIntegerExpr := .pow (3814697265625, 112455406951957393129) e21 18
  let e34 : LowMeanIntegerExpr := .mul (60272216796875, 449821627807829572516) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-60272216796875, 449821627807829572516) e34
  let e36 : LowMeanIntegerExpr := .add (35560893940354785059799399, 449821627807829572516000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (35565392156632863355524559, 449821627807829572516000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-35560893940354785059799399, 449821627807829572516000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0461 : LowMeanDirectSeedInput :=
  { record := 461, positions := [{ j := 15, mode := 0, left := 952, right := 0 }, { j := 16, mode := 0, left := 953, right := 0 }], target := { R := 18, expr := lowMeanSeedTargetExpr0461 } }

noncomputable def lowMeanSeedTargetExpr0462 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (84077, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (129, 100000)
  let e3 : LowMeanIntegerExpr := .atom (19, 1)
  let e4 : LowMeanIntegerExpr := .atom (57, 2)
  let e5 : LowMeanIntegerExpr := .neg (-57, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-19, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-2451, 200000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (35911, 500000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (137, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (361, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (49457, 4000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-49457, 4000000) e11
  let e13 : LowMeanIntegerExpr := .add (237831, 4000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (52687, 2112500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (57053279, 676000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (79, 20)
  let e33 : LowMeanIntegerExpr := .pow (19073486328125, 1461920290375446110677) e21 19
  let e34 : LowMeanIntegerExpr := .mul (301361083984375, 5847681161501784442708) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-301361083984375, 5847681161501784442708) e34
  let e36 : LowMeanIntegerExpr := .add (493534291553420996109732307, 5847681161501784442708000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (493592768365036013954159387, 5847681161501784442708000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-493534291553420996109732307, 5847681161501784442708000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0462 : LowMeanDirectSeedInput :=
  { record := 462, positions := [{ j := 16, mode := 0, left := 954, right := 0 }], target := { R := 19, expr := lowMeanSeedTargetExpr0462 } }

noncomputable def lowMeanSeedTargetExpr0463 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (84077, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (129, 100000)
  let e3 : LowMeanIntegerExpr := .atom (20, 1)
  let e4 : LowMeanIntegerExpr := .atom (57, 2)
  let e5 : LowMeanIntegerExpr := .neg (-57, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-17, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-2193, 200000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (9139, 125000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (137, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (289, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (39593, 4000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-39593, 4000000) e11
  let e13 : LowMeanIntegerExpr := .add (50571, 800000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (2773, 105625) e29 e3
  let e31 : LowMeanIntegerExpr := .add (12095939, 135200000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (79, 20)
  let e33 : LowMeanIntegerExpr := .pow (95367431640625, 19004963774880799438801) e21 20
  let e34 : LowMeanIntegerExpr := .mul (1506805419921875, 76019855099523197755204) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1506805419921875, 76019855099523197755204) e34
  let e36 : LowMeanIntegerExpr := .add (1360253441349968573512403131, 15203971019904639551040800000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (1360405481060167619907913539, 15203971019904639551040800000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-1360253441349968573512403131, 15203971019904639551040800000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0463 : LowMeanDirectSeedInput :=
  { record := 463, positions := [{ j := 16, mode := 0, left := 955, right := 0 }, { j := 17, mode := 0, left := 956, right := 0 }], target := { R := 20, expr := lowMeanSeedTargetExpr0463 } }

noncomputable def lowMeanSeedGroup0448 : List LowMeanDirectSeedInput := [lowMeanSeedRecord0448, lowMeanSeedRecord0449, lowMeanSeedRecord0450, lowMeanSeedRecord0451, lowMeanSeedRecord0452, lowMeanSeedRecord0453, lowMeanSeedRecord0454, lowMeanSeedRecord0455, lowMeanSeedRecord0456, lowMeanSeedRecord0457, lowMeanSeedRecord0458, lowMeanSeedRecord0459, lowMeanSeedRecord0460, lowMeanSeedRecord0461, lowMeanSeedRecord0462, lowMeanSeedRecord0463]

end Erdos993Lean.Analytic.V213
