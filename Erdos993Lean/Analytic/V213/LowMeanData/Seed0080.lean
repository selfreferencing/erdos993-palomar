module

public import Erdos993Lean.Analytic.V213.LowMeanCoreAll
public import Erdos993Lean.Analytic.V213.LowMeanData.CoreBlock14
public import Erdos993Lean.Analytic.V213.LowMeanFiberSeed
public import Erdos993Lean.Analytic.V213.LowMeanIntegerExpr
public import Erdos993Lean.Analytic.V213.LowMeanSeedGeometry
public import Erdos993Lean.Analytic.V213.LowMeanWidthData
public import Erdos993Lean.Ceiling.Prefix
public import Erdos993Lean.Ceiling.Statement

/-! Exact core/budget keys and equation-51 targets for the direct fibers. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanSeedTargetExpr0080 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (11673, 100000)
  let e2 : LowMeanIntegerExpr := .atom (-251, 250000)
  let e3 : LowMeanIntegerExpr := .atom (0, 1)
  let e4 : LowMeanIntegerExpr := .atom (43, 4)
  let e5 : LowMeanIntegerExpr := .neg (-43, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-43, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (10793, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (127523, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1447, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (1849, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (2675503, 16000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-2675503, 16000000) e11
  let e13 : LowMeanIntegerExpr := .add (-127027, 3200000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (22, 625)
  let e15 : LowMeanIntegerExpr := .atom (39, 89)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (87, 187)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-39, 89) e15
  let e21 : LowMeanIntegerExpr := .add (50, 89) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (1950, 7921) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-87, 187) e17
  let e24 : LowMeanIntegerExpr := .add (100, 187) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (8700, 34969) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (8700, 34969) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (8700, 34969) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (8700, 34969) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (696, 79475) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (0, 1) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-127027, 3200000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1643, 1000)
  let e33 : LowMeanIntegerExpr := .pow (1, 1) e21 0
  let e34 : LowMeanIntegerExpr := .mul (1643, 1000) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1643, 1000) e34
  let e36 : LowMeanIntegerExpr := .add (-5384627, 3200000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-1076919, 640000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (5384627, 3200000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0080 : LowMeanDirectSeedInput :=
  { record := 80, positions := [], target := { R := 0, expr := lowMeanSeedTargetExpr0080 } }

noncomputable def lowMeanSeedTargetExpr0081 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (11673, 100000)
  let e2 : LowMeanIntegerExpr := .atom (-251, 250000)
  let e3 : LowMeanIntegerExpr := .atom (1, 1)
  let e4 : LowMeanIntegerExpr := .atom (43, 4)
  let e5 : LowMeanIntegerExpr := .neg (-43, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-39, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (9789, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (126519, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1447, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (1521, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (2200887, 16000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-2200887, 16000000) e11
  let e13 : LowMeanIntegerExpr := .add (-176583, 16000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (22, 625)
  let e15 : LowMeanIntegerExpr := .atom (39, 89)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (87, 187)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .neg (-39, 89) e15
  let e20 : LowMeanIntegerExpr := .add (50, 89) e3 e19
  let e21 : LowMeanIntegerExpr := .mul (1950, 7921) e15 e20
  let e22 : LowMeanIntegerExpr := .neg (-87, 187) e17
  let e23 : LowMeanIntegerExpr := .add (100, 187) e3 e22
  let e24 : LowMeanIntegerExpr := .mul (8700, 34969) e17 e23
  let e25 : LowMeanIntegerExpr := .maximum (8700, 34969) e21 e24
  let e26 : LowMeanIntegerExpr := .selectLE (8700, 34969) e16 e17 e18 e25
  let e27 : LowMeanIntegerExpr := .selectLE (8700, 34969) e15 e16 e26 e25
  let e28 : LowMeanIntegerExpr := .mul (696, 79475) e14 e27
  let e29 : LowMeanIntegerExpr := .mul (696, 79475) e28 e3
  let e30 : LowMeanIntegerExpr := .add (-115917357, 50864000000) e13 e29
  let e31 : LowMeanIntegerExpr := .atom (1643, 1000)
  let e32 : LowMeanIntegerExpr := .pow (50, 89) e20 1
  let e33 : LowMeanIntegerExpr := .mul (1643, 1780) e31 e32
  let e34 : LowMeanIntegerExpr := .neg (-1643, 1780) e33
  let e35 : LowMeanIntegerExpr := .add (-4188794244773, 4526896000000) e30 e34
  let e36 : LowMeanIntegerExpr := .add (-4188748975813, 4526896000000) e0 e35
  let e37 : LowMeanIntegerExpr := .neg (4188794244773, 4526896000000) e35
  let e38 : LowMeanIntegerExpr := .add (1, 100000) e36 e37
  e38

noncomputable def lowMeanSeedRecord0081 : LowMeanDirectSeedInput :=
  { record := 81, positions := [], target := { R := 1, expr := lowMeanSeedTargetExpr0081 } }

noncomputable def lowMeanSeedTargetExpr0082 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (11673, 100000)
  let e2 : LowMeanIntegerExpr := .atom (-251, 250000)
  let e3 : LowMeanIntegerExpr := .atom (2, 1)
  let e4 : LowMeanIntegerExpr := .atom (43, 4)
  let e5 : LowMeanIntegerExpr := .neg (-43, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-35, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (1757, 200000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (25103, 200000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1447, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (1225, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (70903, 640000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-70903, 640000) e11
  let e13 : LowMeanIntegerExpr := .add (47133, 3200000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (22, 625)
  let e15 : LowMeanIntegerExpr := .atom (39, 89)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (87, 187)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-39, 89) e15
  let e21 : LowMeanIntegerExpr := .add (50, 89) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (1950, 7921) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-87, 187) e17
  let e24 : LowMeanIntegerExpr := .add (100, 187) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (8700, 34969) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (8700, 34969) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (8700, 34969) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (8700, 34969) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (696, 79475) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (1392, 79475) e29 e3
  let e31 : LowMeanIntegerExpr := .add (328011807, 10172800000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1643, 1000)
  let e33 : LowMeanIntegerExpr := .pow (2500, 7921) e21 2
  let e34 : LowMeanIntegerExpr := .mul (8215, 15842) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-8215, 15842) e34
  let e36 : LowMeanIntegerExpr := .add (-39186594476753, 80578748800000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-7837157737853, 16115749760000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (39186594476753, 80578748800000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0082 : LowMeanDirectSeedInput :=
  { record := 82, positions := [], target := { R := 2, expr := lowMeanSeedTargetExpr0082 } }

noncomputable def lowMeanSeedTargetExpr0083 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (11673, 100000)
  let e2 : LowMeanIntegerExpr := .atom (-251, 250000)
  let e3 : LowMeanIntegerExpr := .atom (3, 1)
  let e4 : LowMeanIntegerExpr := .atom (43, 4)
  let e5 : LowMeanIntegerExpr := .neg (-43, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-31, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (7781, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (124511, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1447, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (961, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1390567, 16000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1390567, 16000000) e11
  let e13 : LowMeanIntegerExpr := .add (601609, 16000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (22, 625)
  let e15 : LowMeanIntegerExpr := .atom (39, 89)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (87, 187)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-39, 89) e15
  let e21 : LowMeanIntegerExpr := .add (50, 89) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (1950, 7921) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-87, 187) e17
  let e24 : LowMeanIntegerExpr := .add (100, 187) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (8700, 34969) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (8700, 34969) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (8700, 34969) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (8700, 34969) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (696, 79475) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (2088, 79475) e29 e3
  let e31 : LowMeanIntegerExpr := .add (3248835011, 50864000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1643, 1000)
  let e33 : LowMeanIntegerExpr := .pow (125000, 704969) e21 3
  let e34 : LowMeanIntegerExpr := .mul (205375, 704969) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-205375, 704969) e34
  let e36 : LowMeanIntegerExpr := .add (-8155866031130341, 35857543216000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-8155507455698181, 35857543216000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (8155866031130341, 35857543216000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0083 : LowMeanDirectSeedInput :=
  { record := 83, positions := [{ j := 3, mode := 0, left := 341, right := 0 }], target := { R := 3, expr := lowMeanSeedTargetExpr0083 } }

noncomputable def lowMeanSeedTargetExpr0084 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (11673, 100000)
  let e2 : LowMeanIntegerExpr := .atom (-251, 250000)
  let e3 : LowMeanIntegerExpr := .atom (4, 1)
  let e4 : LowMeanIntegerExpr := .atom (43, 4)
  let e5 : LowMeanIntegerExpr := .neg (-43, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-27, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (6777, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (123507, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1447, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (729, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1054863, 16000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1054863, 16000000) e11
  let e13 : LowMeanIntegerExpr := .add (921249, 16000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (22, 625)
  let e15 : LowMeanIntegerExpr := .atom (39, 89)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (87, 187)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-39, 89) e15
  let e21 : LowMeanIntegerExpr := .add (50, 89) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (1950, 7921) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-87, 187) e17
  let e24 : LowMeanIntegerExpr := .add (100, 187) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (8700, 34969) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (8700, 34969) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (8700, 34969) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (8700, 34969) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (696, 79475) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (2784, 79475) e29 e3
  let e31 : LowMeanIntegerExpr := .add (4710410571, 50864000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1643, 1000)
  let e33 : LowMeanIntegerExpr := .pow (6250000, 62742241) e21 4
  let e34 : LowMeanIntegerExpr := .mul (10268750, 62742241) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-10268750, 62742241) e34
  let e36 : LowMeanIntegerExpr := .add (-226767984745370389, 3191321346224000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-226736071531908149, 3191321346224000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (226767984745370389, 3191321346224000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0084 : LowMeanDirectSeedInput :=
  { record := 84, positions := [], target := { R := 4, expr := lowMeanSeedTargetExpr0084 } }

noncomputable def lowMeanSeedTargetExpr0085 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (11673, 100000)
  let e2 : LowMeanIntegerExpr := .atom (-251, 250000)
  let e3 : LowMeanIntegerExpr := .atom (5, 1)
  let e4 : LowMeanIntegerExpr := .atom (43, 4)
  let e5 : LowMeanIntegerExpr := .neg (-43, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-23, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (5773, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (122503, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1447, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (529, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (765463, 16000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-765463, 16000000) e11
  let e13 : LowMeanIntegerExpr := .add (238917, 3200000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (22, 625)
  let e15 : LowMeanIntegerExpr := .atom (39, 89)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (87, 187)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-39, 89) e15
  let e21 : LowMeanIntegerExpr := .add (50, 89) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (1950, 7921) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-87, 187) e17
  let e24 : LowMeanIntegerExpr := .add (100, 187) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (8700, 34969) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (8700, 34969) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (8700, 34969) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (8700, 34969) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (696, 79475) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (696, 15895) e29 e3
  let e31 : LowMeanIntegerExpr := .add (1204957143, 10172800000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1643, 1000)
  let e33 : LowMeanIntegerExpr := .pow (312500000, 5584059449) e21 5
  let e34 : LowMeanIntegerExpr := .mul (513437500, 5584059449) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-513437500, 5584059449) e34
  let e36 : LowMeanIntegerExpr := .add (1505455320009194207, 56805519962787200000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (1506023375208822079, 56805519962787200000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-1505455320009194207, 56805519962787200000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0085 : LowMeanDirectSeedInput :=
  { record := 85, positions := [{ j := 0, mode := 0, left := 342, right := 0 }, { j := 4, mode := 0, left := 343, right := 0 }], target := { R := 5, expr := lowMeanSeedTargetExpr0085 } }

noncomputable def lowMeanSeedTargetExpr0086 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (11673, 100000)
  let e2 : LowMeanIntegerExpr := .atom (-251, 250000)
  let e3 : LowMeanIntegerExpr := .atom (6, 1)
  let e4 : LowMeanIntegerExpr := .atom (43, 4)
  let e5 : LowMeanIntegerExpr := .neg (-43, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-19, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (4769, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (121499, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1447, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (361, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (522367, 16000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-522367, 16000000) e11
  let e13 : LowMeanIntegerExpr := .add (1421617, 16000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (22, 625)
  let e15 : LowMeanIntegerExpr := .atom (39, 89)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (87, 187)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-39, 89) e15
  let e21 : LowMeanIntegerExpr := .add (50, 89) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (1950, 7921) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-87, 187) e17
  let e24 : LowMeanIntegerExpr := .add (100, 187) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (8700, 34969) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (8700, 34969) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (8700, 34969) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (8700, 34969) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (696, 79475) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (4176, 79475) e29 e3
  let e31 : LowMeanIntegerExpr := .add (7191960443, 50864000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1643, 1000)
  let e33 : LowMeanIntegerExpr := .pow (15625000000, 496981290961) e21 6
  let e34 : LowMeanIntegerExpr := .mul (25671875000, 496981290961) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-25671875000, 496981290961) e34
  let e36 : LowMeanIntegerExpr := .add (2268495535502585455723, 25278456383440304000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (2268748320066419858763, 25278456383440304000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-2268495535502585455723, 25278456383440304000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0086 : LowMeanDirectSeedInput :=
  { record := 86, positions := [{ j := 4, mode := 0, left := 344, right := 0 }], target := { R := 6, expr := lowMeanSeedTargetExpr0086 } }

noncomputable def lowMeanSeedTargetExpr0087 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (11673, 100000)
  let e2 : LowMeanIntegerExpr := .atom (-251, 250000)
  let e3 : LowMeanIntegerExpr := .atom (7, 1)
  let e4 : LowMeanIntegerExpr := .atom (43, 4)
  let e5 : LowMeanIntegerExpr := .neg (-43, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-15, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (753, 200000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (24099, 200000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1447, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (225, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (13023, 640000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-13023, 640000) e11
  let e13 : LowMeanIntegerExpr := .add (320469, 3200000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (22, 625)
  let e15 : LowMeanIntegerExpr := .atom (39, 89)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (87, 187)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-39, 89) e15
  let e21 : LowMeanIntegerExpr := .add (50, 89) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (1950, 7921) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-87, 187) e17
  let e24 : LowMeanIntegerExpr := .add (100, 187) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (8700, 34969) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (8700, 34969) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (8700, 34969) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (8700, 34969) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (696, 79475) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (4872, 79475) e29 e3
  let e31 : LowMeanIntegerExpr := .add (1642386951, 10172800000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1643, 1000)
  let e33 : LowMeanIntegerExpr := .pow (781250000000, 44231334895529) e21 7
  let e34 : LowMeanIntegerExpr := .mul (1283593750000, 44231334895529) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1283593750000, 44231334895529) e34
  let e36 : LowMeanIntegerExpr := .add (59587224757727777842079, 449956523625237411200000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (59591724322964030216191, 449956523625237411200000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-59587224757727777842079, 449956523625237411200000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0087 : LowMeanDirectSeedInput :=
  { record := 87, positions := [{ j := 1, mode := 0, left := 345, right := 0 }, { j := 5, mode := 0, left := 346, right := 0 }], target := { R := 7, expr := lowMeanSeedTargetExpr0087 } }

noncomputable def lowMeanSeedTargetExpr0088 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (11673, 100000)
  let e2 : LowMeanIntegerExpr := .atom (-251, 250000)
  let e3 : LowMeanIntegerExpr := .atom (8, 1)
  let e4 : LowMeanIntegerExpr := .atom (43, 4)
  let e5 : LowMeanIntegerExpr := .neg (-43, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-11, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (2761, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (119491, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1447, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (121, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (175087, 16000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-175087, 16000000) e11
  let e13 : LowMeanIntegerExpr := .add (1736769, 16000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (22, 625)
  let e15 : LowMeanIntegerExpr := .atom (39, 89)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (87, 187)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-39, 89) e15
  let e21 : LowMeanIntegerExpr := .add (50, 89) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (1950, 7921) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-87, 187) e17
  let e24 : LowMeanIntegerExpr := .add (100, 187) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (8700, 34969) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (8700, 34969) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (8700, 34969) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (8700, 34969) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (696, 79475) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (5568, 79475) e29 e3
  let e31 : LowMeanIntegerExpr := .add (9084708651, 50864000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1643, 1000)
  let e33 : LowMeanIntegerExpr := .pow (39062500000000, 3936588805702081) e21 8
  let e34 : LowMeanIntegerExpr := .mul (64179687500000, 3936588805702081) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-64179687500000, 3936588805702081) e34
  let e36 : LowMeanIntegerExpr := .add (32498326753591453389402731, 200230653013230647984000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (32500329060121585695882571, 200230653013230647984000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-32498326753591453389402731, 200230653013230647984000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0088 : LowMeanDirectSeedInput :=
  { record := 88, positions := [{ j := 1, mode := 0, left := 347, right := 0 }, { j := 2, mode := 0, left := 348, right := 0 }, { j := 5, mode := 0, left := 349, right := 0 }], target := { R := 8, expr := lowMeanSeedTargetExpr0088 } }

noncomputable def lowMeanSeedTargetExpr0089 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (11673, 100000)
  let e2 : LowMeanIntegerExpr := .atom (-251, 250000)
  let e3 : LowMeanIntegerExpr := .atom (9, 1)
  let e4 : LowMeanIntegerExpr := .atom (43, 4)
  let e5 : LowMeanIntegerExpr := .neg (-43, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-7, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (1757, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (118487, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1447, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (49, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (70903, 16000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-70903, 16000000) e11
  let e13 : LowMeanIntegerExpr := .add (1824889, 16000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (22, 625)
  let e15 : LowMeanIntegerExpr := .atom (39, 89)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (87, 187)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-39, 89) e15
  let e21 : LowMeanIntegerExpr := .add (50, 89) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (1950, 7921) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-87, 187) e17
  let e24 : LowMeanIntegerExpr := .add (100, 187) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (8700, 34969) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (8700, 34969) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (8700, 34969) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (8700, 34969) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (696, 79475) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (6264, 79475) e29 e3
  let e31 : LowMeanIntegerExpr := .add (9810282131, 50864000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1643, 1000)
  let e33 : LowMeanIntegerExpr := .pow (1953125000000000, 350356403707485209) e21 9
  let e34 : LowMeanIntegerExpr := .mul (3208984375000000, 350356403707485209) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-3208984375000000, 350356403707485209) e34
  let e36 : LowMeanIntegerExpr := .add (3273873385522964296799500379, 17820528118177527670576000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (3274051590804146072076206139, 17820528118177527670576000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-3273873385522964296799500379, 17820528118177527670576000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0089 : LowMeanDirectSeedInput :=
  { record := 89, positions := [{ j := 2, mode := 0, left := 350, right := 0 }, { j := 6, mode := 0, left := 351, right := 0 }], target := { R := 9, expr := lowMeanSeedTargetExpr0089 } }

noncomputable def lowMeanSeedTargetExpr0090 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (11673, 100000)
  let e2 : LowMeanIntegerExpr := .atom (-251, 250000)
  let e3 : LowMeanIntegerExpr := .atom (10, 1)
  let e4 : LowMeanIntegerExpr := .atom (43, 4)
  let e5 : LowMeanIntegerExpr := .neg (-43, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-3, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (753, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (117483, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1447, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (9, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (13023, 16000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-13023, 16000000) e11
  let e13 : LowMeanIntegerExpr := .add (373341, 3200000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (22, 625)
  let e15 : LowMeanIntegerExpr := .atom (39, 89)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (87, 187)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-39, 89) e15
  let e21 : LowMeanIntegerExpr := .add (50, 89) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (1950, 7921) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-87, 187) e17
  let e24 : LowMeanIntegerExpr := .add (100, 187) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (8700, 34969) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (8700, 34969) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (8700, 34969) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (8700, 34969) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (696, 79475) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (1392, 15895) e29 e3
  let e31 : LowMeanIntegerExpr := .add (2077731039, 10172800000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1643, 1000)
  let e33 : LowMeanIntegerExpr := .pow (97656250000000000, 31181719929966183601) e21 10
  let e34 : LowMeanIntegerExpr := .mul (160449218750000000, 31181719929966183601) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-160449218750000000, 31181719929966183601) e34
  let e36 : LowMeanIntegerExpr := .add (63155009535395645888170491439, 317205400503559992536252800000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (63158181589400681488095853967, 317205400503559992536252800000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-63155009535395645888170491439, 317205400503559992536252800000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0090 : LowMeanDirectSeedInput :=
  { record := 90, positions := [{ j := 2, mode := 0, left := 352, right := 0 }, { j := 3, mode := 0, left := 353, right := 0 }, { j := 6, mode := 0, left := 354, right := 0 }], target := { R := 10, expr := lowMeanSeedTargetExpr0090 } }

noncomputable def lowMeanSeedTargetExpr0091 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (11673, 100000)
  let e2 : LowMeanIntegerExpr := .atom (-251, 250000)
  let e3 : LowMeanIntegerExpr := .atom (11, 1)
  let e4 : LowMeanIntegerExpr := .atom (43, 4)
  let e5 : LowMeanIntegerExpr := .neg (-43, 4) e4
  let e6 : LowMeanIntegerExpr := .add (1, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-251, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (116479, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1447, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (1, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1447, 16000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1447, 16000000) e11
  let e13 : LowMeanIntegerExpr := .add (1862217, 16000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (22, 625)
  let e15 : LowMeanIntegerExpr := .atom (39, 89)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (87, 187)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-39, 89) e15
  let e21 : LowMeanIntegerExpr := .add (50, 89) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (1950, 7921) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-87, 187) e17
  let e24 : LowMeanIntegerExpr := .add (100, 187) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (8700, 34969) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (8700, 34969) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (8700, 34969) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (8700, 34969) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (696, 79475) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (696, 7225) e29 e3
  let e31 : LowMeanIntegerExpr := .add (983620713, 4624000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1643, 1000)
  let e33 : LowMeanIntegerExpr := .pow (4882812500000000000, 2775173073766990340489) e21 11
  let e34 : LowMeanIntegerExpr := .mul (8022460937500000000, 2775173073766990340489) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-8022460937500000000, 2775173073766990340489) e34
  let e36 : LowMeanIntegerExpr := .add (2692621858142088634575902948657, 12832400293098563334421136000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (2692750182145019620209247160017, 12832400293098563334421136000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-2692621858142088634575902948657, 12832400293098563334421136000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0091 : LowMeanDirectSeedInput :=
  { record := 91, positions := [{ j := 3, mode := 0, left := 355, right := 0 }, { j := 6, mode := 0, left := 356, right := 0 }], target := { R := 11, expr := lowMeanSeedTargetExpr0091 } }

noncomputable def lowMeanSeedTargetExpr0092 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (11673, 100000)
  let e2 : LowMeanIntegerExpr := .atom (-251, 250000)
  let e3 : LowMeanIntegerExpr := .atom (12, 1)
  let e4 : LowMeanIntegerExpr := .atom (43, 4)
  let e5 : LowMeanIntegerExpr := .neg (-43, 4) e4
  let e6 : LowMeanIntegerExpr := .add (5, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-251, 200000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (4619, 40000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1447, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (25, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1447, 640000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1447, 640000) e11
  let e13 : LowMeanIntegerExpr := .add (72457, 640000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (22, 625)
  let e15 : LowMeanIntegerExpr := .atom (39, 89)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (87, 187)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-39, 89) e15
  let e21 : LowMeanIntegerExpr := .add (50, 89) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (1950, 7921) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-87, 187) e17
  let e24 : LowMeanIntegerExpr := .add (100, 187) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (8700, 34969) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (8700, 34969) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (8700, 34969) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (8700, 34969) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (696, 79475) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (8352, 79475) e29 e3
  let e31 : LowMeanIntegerExpr := .add (444152003, 2034560000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1643, 1000)
  let e33 : LowMeanIntegerExpr := .pow (244140625000000000000, 246990403565262140303521) e21 12
  let e34 : LowMeanIntegerExpr := .mul (401123046875000000000, 246990403565262140303521) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-401123046875000000000, 246990403565262140303521) e34
  let e36 : LowMeanIntegerExpr := .add (108885173559039520835875880102563, 502516795477739740175931685760000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (544450993634971491166388197097103, 2512583977388698700879658428800000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-108885173559039520835875880102563, 502516795477739740175931685760000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0092 : LowMeanDirectSeedInput :=
  { record := 92, positions := [{ j := 3, mode := 0, left := 357, right := 0 }, { j := 4, mode := 0, left := 358, right := 0 }, { j := 6, mode := 0, left := 359, right := 0 }], target := { R := 12, expr := lowMeanSeedTargetExpr0092 } }

noncomputable def lowMeanSeedTargetExpr0093 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (11673, 100000)
  let e2 : LowMeanIntegerExpr := .atom (-251, 250000)
  let e3 : LowMeanIntegerExpr := .atom (13, 1)
  let e4 : LowMeanIntegerExpr := .atom (43, 4)
  let e5 : LowMeanIntegerExpr := .neg (-43, 4) e4
  let e6 : LowMeanIntegerExpr := .add (9, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-2259, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (114471, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1447, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (81, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (117207, 16000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-117207, 16000000) e11
  let e13 : LowMeanIntegerExpr := .add (1714329, 16000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (22, 625)
  let e15 : LowMeanIntegerExpr := .atom (39, 89)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (87, 187)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-39, 89) e15
  let e21 : LowMeanIntegerExpr := .add (50, 89) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (1950, 7921) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-87, 187) e17
  let e24 : LowMeanIntegerExpr := .add (100, 187) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (8700, 34969) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (8700, 34969) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (8700, 34969) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (8700, 34969) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (696, 79475) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (9048, 79475) e29 e3
  let e31 : LowMeanIntegerExpr := .add (11240571891, 50864000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1643, 1000)
  let e33 : LowMeanIntegerExpr := .pow (12207031250000000000000, 21982145917308330487013369) e21 13
  let e34 : LowMeanIntegerExpr := .mul (20056152343750000000000, 21982145917308330487013369) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-20056152343750000000000, 21982145917308330487013369) e34
  let e36 : LowMeanIntegerExpr := .add (246071755369143930052460816122610779, 1118099869937970921891448000816000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (246082936367843309761679730602618939, 1118099869937970921891448000816000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-246071755369143930052460816122610779, 1118099869937970921891448000816000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0093 : LowMeanDirectSeedInput :=
  { record := 93, positions := [{ j := 4, mode := 0, left := 360, right := 0 }, { j := 5, mode := 0, left := 361, right := 0 }, { j := 6, mode := 0, left := 362, right := 0 }, { j := 7, mode := 0, left := 363, right := 0 }], target := { R := 13, expr := lowMeanSeedTargetExpr0093 } }

noncomputable def lowMeanSeedTargetExpr0094 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (11673, 100000)
  let e2 : LowMeanIntegerExpr := .atom (-251, 250000)
  let e3 : LowMeanIntegerExpr := .atom (14, 1)
  let e4 : LowMeanIntegerExpr := .atom (43, 4)
  let e5 : LowMeanIntegerExpr := .neg (-43, 4) e4
  let e6 : LowMeanIntegerExpr := .add (13, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-3263, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (113467, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1447, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (169, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (244543, 16000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-244543, 16000000) e11
  let e13 : LowMeanIntegerExpr := .add (1570929, 16000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (22, 625)
  let e15 : LowMeanIntegerExpr := .atom (39, 89)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (87, 187)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-39, 89) e15
  let e21 : LowMeanIntegerExpr := .add (50, 89) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (1950, 7921) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-87, 187) e17
  let e24 : LowMeanIntegerExpr := .add (100, 187) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (8700, 34969) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (8700, 34969) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (8700, 34969) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (8700, 34969) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (696, 79475) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (9744, 79475) e29 e3
  let e31 : LowMeanIntegerExpr := .add (11230143291, 50864000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1643, 1000)
  let e33 : LowMeanIntegerExpr := .pow (610351562500000000000000, 1956410986640441413344189841) e21 14
  let e34 : LowMeanIntegerExpr := .mul (1002807617187500000000000, 1956410986640441413344189841) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1002807617187500000000000, 1956410986640441413344189841) e34
  let e36 : LowMeanIntegerExpr := .add (21919768909418218767345811416736506731, 99510888424479412048338872072624000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (21920764018302463561466294805457232971, 99510888424479412048338872072624000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-21919768909418218767345811416736506731, 99510888424479412048338872072624000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0094 : LowMeanDirectSeedInput :=
  { record := 94, positions := [{ j := 5, mode := 0, left := 364, right := 0 }, { j := 7, mode := 0, left := 365, right := 0 }], target := { R := 14, expr := lowMeanSeedTargetExpr0094 } }

noncomputable def lowMeanSeedTargetExpr0095 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (56593, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (363, 200000)
  let e3 : LowMeanIntegerExpr := .atom (0, 1)
  let e4 : LowMeanIntegerExpr := .atom (33, 2)
  let e5 : LowMeanIntegerExpr := .neg (-33, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-33, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-11979, 400000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (53291, 2000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (4727, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (1089, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (5147703, 40000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-5147703, 40000000) e11
  let e13 : LowMeanIntegerExpr := .add (-4081883, 40000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (113, 10000)
  let e15 : LowMeanIntegerExpr := .atom (39, 89)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (87, 187)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-39, 89) e15
  let e21 : LowMeanIntegerExpr := .add (50, 89) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (1950, 7921) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-87, 187) e17
  let e24 : LowMeanIntegerExpr := .add (100, 187) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (8700, 34969) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (8700, 34969) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (8700, 34969) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (8700, 34969) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (9831, 3496900) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (0, 1) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-4081883, 40000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1619, 1000)
  let e33 : LowMeanIntegerExpr := .pow (1, 1) e21 0
  let e34 : LowMeanIntegerExpr := .mul (1619, 1000) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1619, 1000) e34
  let e36 : LowMeanIntegerExpr := .add (-68841883, 40000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-68841483, 40000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (68841883, 40000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0095 : LowMeanDirectSeedInput :=
  { record := 95, positions := [], target := { R := 0, expr := lowMeanSeedTargetExpr0095 } }

noncomputable def lowMeanSeedGroup0080 : List LowMeanDirectSeedInput := [lowMeanSeedRecord0080, lowMeanSeedRecord0081, lowMeanSeedRecord0082, lowMeanSeedRecord0083, lowMeanSeedRecord0084, lowMeanSeedRecord0085, lowMeanSeedRecord0086, lowMeanSeedRecord0087, lowMeanSeedRecord0088, lowMeanSeedRecord0089, lowMeanSeedRecord0090, lowMeanSeedRecord0091, lowMeanSeedRecord0092, lowMeanSeedRecord0093, lowMeanSeedRecord0094, lowMeanSeedRecord0095]

end Erdos993Lean.Analytic.V213
