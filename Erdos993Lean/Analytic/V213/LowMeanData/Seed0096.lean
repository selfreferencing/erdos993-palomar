module

public import Erdos993Lean.Analytic.V213.LowMeanCoreAll
public import Erdos993Lean.Analytic.V213.LowMeanData.Seed0032
public import Erdos993Lean.Analytic.V213.LowMeanFiberSeed
public import Erdos993Lean.Analytic.V213.LowMeanIntegerExpr
public import Erdos993Lean.Analytic.V213.LowMeanSeedGeometry
public import Erdos993Lean.Analytic.V213.LowMeanWidthData
public import Erdos993Lean.Ceiling.Prefix
public import Erdos993Lean.Ceiling.Statement

/-! Exact core/budget keys and equation-51 targets for the direct fibers. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanSeedTargetExpr0096 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (56593, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (363, 200000)
  let e3 : LowMeanIntegerExpr := .atom (1, 1)
  let e4 : LowMeanIntegerExpr := .atom (33, 2)
  let e5 : LowMeanIntegerExpr := .neg (-33, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-31, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-11253, 400000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (56921, 2000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (4727, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (961, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (4542647, 40000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-4542647, 40000000) e11
  let e13 : LowMeanIntegerExpr := .add (-3404227, 40000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (113, 10000)
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
  let e28 : LowMeanIntegerExpr := .mul (9831, 3496900) e14 e27
  let e29 : LowMeanIntegerExpr := .mul (9831, 3496900) e28 e3
  let e30 : LowMeanIntegerExpr := .add (-115110013963, 1398760000000) e13 e29
  let e31 : LowMeanIntegerExpr := .atom (1619, 1000)
  let e32 : LowMeanIntegerExpr := .pow (50, 89) e20 1
  let e33 : LowMeanIntegerExpr := .mul (1619, 1780) e31 e32
  let e34 : LowMeanIntegerExpr := .neg (-1619, 1780) e33
  let e35 : LowMeanIntegerExpr := .add (-123474413242707, 124489640000000) e30 e34
  let e36 : LowMeanIntegerExpr := .add (-123473168346307, 124489640000000) e0 e35
  let e37 : LowMeanIntegerExpr := .neg (123474413242707, 124489640000000) e35
  let e38 : LowMeanIntegerExpr := .add (1, 100000) e36 e37
  e38

noncomputable def lowMeanSeedRecord0096 : LowMeanDirectSeedInput :=
  { record := 96, positions := [], target := { R := 1, expr := lowMeanSeedTargetExpr0096 } }

noncomputable def lowMeanSeedTargetExpr0097 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (56593, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (363, 200000)
  let e3 : LowMeanIntegerExpr := .atom (2, 1)
  let e4 : LowMeanIntegerExpr := .atom (33, 2)
  let e5 : LowMeanIntegerExpr := .neg (-33, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-29, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-10527, 400000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (60551, 2000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (4727, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (841, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (3975407, 40000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-3975407, 40000000) e11
  let e13 : LowMeanIntegerExpr := .add (-2764387, 40000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (9831, 1748450) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-88803049003, 1398760000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1619, 1000)
  let e33 : LowMeanIntegerExpr := .pow (2500, 7921) e21 2
  let e34 : LowMeanIntegerExpr := .mul (8095, 15842) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-8095, 15842) e34
  let e36 : LowMeanIntegerExpr := .add (-6364890051152763, 11079577960000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-6364779255373163, 11079577960000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (6364890051152763, 11079577960000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0097 : LowMeanDirectSeedInput :=
  { record := 97, positions := [], target := { R := 2, expr := lowMeanSeedTargetExpr0097 } }

noncomputable def lowMeanSeedTargetExpr0098 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (56593, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (363, 200000)
  let e3 : LowMeanIntegerExpr := .atom (3, 1)
  let e4 : LowMeanIntegerExpr := .atom (33, 2)
  let e5 : LowMeanIntegerExpr := .neg (-33, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-27, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-9801, 400000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (64181, 2000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (4727, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (729, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (3445983, 40000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-3445983, 40000000) e11
  let e13 : LowMeanIntegerExpr := .add (-2162363, 40000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (29493, 3496900) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-63818471747, 1398760000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1619, 1000)
  let e33 : LowMeanIntegerExpr := .pow (125000, 704969) e21 3
  let e34 : LowMeanIntegerExpr := .mul (202375, 704969) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-202375, 704969) e34
  let e36 : LowMeanIntegerExpr := .add (-328064099209010843, 986082438440000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-328054238384626443, 986082438440000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (328064099209010843, 986082438440000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0098 : LowMeanDirectSeedInput :=
  { record := 98, positions := [], target := { R := 3, expr := lowMeanSeedTargetExpr0098 } }

noncomputable def lowMeanSeedTargetExpr0099 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (56593, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (363, 200000)
  let e3 : LowMeanIntegerExpr := .atom (4, 1)
  let e4 : LowMeanIntegerExpr := .atom (33, 2)
  let e5 : LowMeanIntegerExpr := .neg (-33, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-25, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-363, 16000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (67811, 2000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (4727, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (625, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (4727, 64000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-4727, 64000) e11
  let e13 : LowMeanIntegerExpr := .add (-319631, 8000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (9831, 874225) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-8031256439, 279752000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1619, 1000)
  let e33 : LowMeanIntegerExpr := .pow (6250000, 62742241) e21 4
  let e34 : LowMeanIntegerExpr := .mul (10118750, 62742241) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-10118750, 62742241) e34
  let e36 : LowMeanIntegerExpr := .add (-3334639577028539799, 17552267404232000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-3334464054354497479, 17552267404232000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (3334639577028539799, 17552267404232000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0099 : LowMeanDirectSeedInput :=
  { record := 99, positions := [], target := { R := 4, expr := lowMeanSeedTargetExpr0099 } }

noncomputable def lowMeanSeedTargetExpr0100 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (56593, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (363, 200000)
  let e3 : LowMeanIntegerExpr := .atom (5, 1)
  let e4 : LowMeanIntegerExpr := .atom (33, 2)
  let e5 : LowMeanIntegerExpr := .neg (-33, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-23, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-8349, 400000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (71441, 2000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (4727, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (529, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (2500583, 40000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-2500583, 40000000) e11
  let e13 : LowMeanIntegerExpr := .add (-1071763, 40000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (9831, 699380) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-17816480347, 1398760000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1619, 1000)
  let e33 : LowMeanIntegerExpr := .pow (312500000, 5584059449) e21 5
  let e34 : LowMeanIntegerExpr := .mul (505937500, 5584059449) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-505937500, 5584059449) e34
  let e36 : LowMeanIntegerExpr := .add (-807173422929588148803, 7810758994883240000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-807095315339639316403, 7810758994883240000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (807173422929588148803, 7810758994883240000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0100 : LowMeanDirectSeedInput :=
  { record := 100, positions := [{ j := 4, mode := 0, left := 366, right := 0 }], target := { R := 5, expr := lowMeanSeedTargetExpr0100 } }

noncomputable def lowMeanSeedTargetExpr0101 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (56593, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (363, 200000)
  let e3 : LowMeanIntegerExpr := .atom (6, 1)
  let e4 : LowMeanIntegerExpr := .atom (33, 2)
  let e5 : LowMeanIntegerExpr := .neg (-33, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-21, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-7623, 400000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (75071, 2000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (4727, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (441, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (2084607, 40000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-2084607, 40000000) e11
  let e13 : LowMeanIntegerExpr := .add (-583187, 40000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (29493, 1748450) e29 e3
  let e31 : LowMeanIntegerExpr := .add (3200933797, 1398760000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1619, 1000)
  let e33 : LowMeanIntegerExpr := .pow (15625000000, 496981290961) e21 6
  let e34 : LowMeanIntegerExpr := .mul (25296875000, 496981290961) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-25296875000, 496981290961) e34
  let e36 : LowMeanIntegerExpr := .add (-33793452664286244491083, 695157550544608360000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-33786501088780798407483, 695157550544608360000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (33793452664286244491083, 695157550544608360000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0101 : LowMeanDirectSeedInput :=
  { record := 101, positions := [{ j := 5, mode := 0, left := 367, right := 0 }], target := { R := 6, expr := lowMeanSeedTargetExpr0101 } }

noncomputable def lowMeanSeedTargetExpr0102 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (56593, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (363, 200000)
  let e3 : LowMeanIntegerExpr := .atom (7, 1)
  let e4 : LowMeanIntegerExpr := .atom (33, 2)
  let e5 : LowMeanIntegerExpr := .neg (-33, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-19, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-6897, 400000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (78701, 2000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (4727, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (361, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1706447, 40000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1706447, 40000000) e11
  let e13 : LowMeanIntegerExpr := .add (-132427, 40000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (68817, 3496900) e29 e3
  let e31 : LowMeanIntegerExpr := .add (22895960237, 1398760000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1619, 1000)
  let e33 : LowMeanIntegerExpr := .pow (781250000000, 44231334895529) e21 7
  let e34 : LowMeanIntegerExpr := .mul (1264843750000, 44231334895529) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1264843750000, 44231334895529) e34
  let e36 : LowMeanIntegerExpr := .add (-756493958752537466919627, 61869021998470144040000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-755875268532552765479227, 61869021998470144040000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (756493958752537466919627, 61869021998470144040000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0102 : LowMeanDirectSeedInput :=
  { record := 102, positions := [{ j := 5, mode := 0, left := 368, right := 0 }], target := { R := 7, expr := lowMeanSeedTargetExpr0102 } }

noncomputable def lowMeanSeedTargetExpr0103 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (56593, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (363, 200000)
  let e3 : LowMeanIntegerExpr := .atom (8, 1)
  let e4 : LowMeanIntegerExpr := .atom (33, 2)
  let e5 : LowMeanIntegerExpr := .neg (-33, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-17, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-6171, 400000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (82331, 2000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (4727, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (289, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1366103, 40000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1366103, 40000000) e11
  let e13 : LowMeanIntegerExpr := .add (280517, 40000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (19662, 874225) e29 e3
  let e31 : LowMeanIntegerExpr := .add (41268598973, 1398760000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1619, 1000)
  let e33 : LowMeanIntegerExpr := .pow (39062500000000, 3936588805702081) e21 8
  let e34 : LowMeanIntegerExpr := .mul (63242187500000, 3936588805702081) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-63242187500000, 3936588805702081) e34
  let e36 : LowMeanIntegerExpr := .add (73996862556620196500562813, 5506342957863842819560000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (74051925986198834928758413, 5506342957863842819560000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-73996862556620196500562813, 5506342957863842819560000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0103 : LowMeanDirectSeedInput :=
  { record := 103, positions := [{ j := 1, mode := 0, left := 369, right := 0 }, { j := 6, mode := 0, left := 370, right := 0 }], target := { R := 8, expr := lowMeanSeedTargetExpr0103 } }

noncomputable def lowMeanSeedTargetExpr0104 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (56593, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (363, 200000)
  let e3 : LowMeanIntegerExpr := .atom (9, 1)
  let e4 : LowMeanIntegerExpr := .atom (33, 2)
  let e5 : LowMeanIntegerExpr := .neg (-33, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-15, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1089, 80000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (85961, 2000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (4727, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (225, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (42543, 1600000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-42543, 1600000) e11
  let e13 : LowMeanIntegerExpr := .add (131129, 8000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (88479, 3496900) e29 e3
  let e31 : LowMeanIntegerExpr := .add (11663770001, 279752000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1619, 1000)
  let e33 : LowMeanIntegerExpr := .pow (1953125000000000, 350356403707485209) e21 9
  let e34 : LowMeanIntegerExpr := .mul (3162109375000000, 350356403707485209) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-3162109375000000, 350356403707485209) e34
  let e36 : LowMeanIntegerExpr := .add (3201870089346611159885415209, 98012904649976402188168000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (3202850218393110923907296889, 98012904649976402188168000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-3201870089346611159885415209, 98012904649976402188168000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0104 : LowMeanDirectSeedInput :=
  { record := 104, positions := [{ j := 1, mode := 0, left := 371, right := 0 }, { j := 6, mode := 0, left := 372, right := 0 }], target := { R := 9, expr := lowMeanSeedTargetExpr0104 } }

noncomputable def lowMeanSeedTargetExpr0105 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (56593, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (363, 200000)
  let e3 : LowMeanIntegerExpr := .atom (10, 1)
  let e4 : LowMeanIntegerExpr := .atom (33, 2)
  let e5 : LowMeanIntegerExpr := .neg (-33, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-13, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-4719, 400000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (89591, 2000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (4727, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (169, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (798863, 40000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-798863, 40000000) e11
  let e13 : LowMeanIntegerExpr := .add (992957, 40000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (9831, 349690) e29 e3
  let e31 : LowMeanIntegerExpr := .add (74046713333, 1398760000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1619, 1000)
  let e33 : LowMeanIntegerExpr := .pow (97656250000000000, 31181719929966183601) e21 10
  let e34 : LowMeanIntegerExpr := .mul (158105468750000000, 31181719929966183601) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-158105468750000000, 31181719929966183601) e34
  let e36 : LowMeanIntegerExpr := .add (2087752271415348833487292652133, 43615742569239498973734760000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (2088188428841041228477029999733, 43615742569239498973734760000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-2087752271415348833487292652133, 43615742569239498973734760000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0105 : LowMeanDirectSeedInput :=
  { record := 105, positions := [{ j := 2, mode := 0, left := 373, right := 0 }, { j := 7, mode := 0, left := 374, right := 0 }], target := { R := 10, expr := lowMeanSeedTargetExpr0105 } }

noncomputable def lowMeanSeedTargetExpr0106 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (56593, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (363, 200000)
  let e3 : LowMeanIntegerExpr := .atom (11, 1)
  let e4 : LowMeanIntegerExpr := .atom (33, 2)
  let e5 : LowMeanIntegerExpr := .neg (-33, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-11, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-3993, 400000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (93221, 2000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (4727, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (121, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (571967, 40000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-571967, 40000000) e11
  let e13 : LowMeanIntegerExpr := .add (1292453, 40000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (9831, 317900) e29 e3
  let e31 : LowMeanIntegerExpr := .add (8041108087, 127160000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1619, 1000)
  let e33 : LowMeanIntegerExpr := .pow (4882812500000000000, 2775173073766990340489) e21 11
  let e34 : LowMeanIntegerExpr := .mul (7905273437500000000, 2775173073766990340489) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-7905273437500000000, 2775173073766990340489) e34
  let e36 : LowMeanIntegerExpr := .add (21310232075979893580556981434543, 352891008060210491696581240000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (21313760986060495685473947246943, 352891008060210491696581240000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-21310232075979893580556981434543, 352891008060210491696581240000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0106 : LowMeanDirectSeedInput :=
  { record := 106, positions := [{ j := 2, mode := 0, left := 375, right := 0 }, { j := 7, mode := 0, left := 376, right := 0 }], target := { R := 11, expr := lowMeanSeedTargetExpr0106 } }

noncomputable def lowMeanSeedTargetExpr0107 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (56593, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (363, 200000)
  let e3 : LowMeanIntegerExpr := .atom (12, 1)
  let e4 : LowMeanIntegerExpr := .atom (33, 2)
  let e5 : LowMeanIntegerExpr := .neg (-33, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-9, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-3267, 400000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (96851, 2000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (4727, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (81, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (382887, 40000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-382887, 40000000) e11
  let e13 : LowMeanIntegerExpr := .add (1554133, 40000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (29493, 874225) e29 e3
  let e31 : LowMeanIntegerExpr := .add (101535276877, 1398760000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1619, 1000)
  let e33 : LowMeanIntegerExpr := .pow (244140625000000000000, 246990403565262140303521) e21 12
  let e34 : LowMeanIntegerExpr := .mul (395263671875000000000, 246990403565262140303521) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-395263671875000000000, 246990403565262140303521) e34
  let e36 : LowMeanIntegerExpr := .add (24525359998288984354803625552983917, 345480296890946071370953033960000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (24528814801257893815517335083323517, 345480296890946071370953033960000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-24525359998288984354803625552983917, 345480296890946071370953033960000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0107 : LowMeanDirectSeedInput :=
  { record := 107, positions := [{ j := 3, mode := 0, left := 377, right := 0 }, { j := 8, mode := 0, left := 378, right := 0 }], target := { R := 12, expr := lowMeanSeedTargetExpr0107 } }

noncomputable def lowMeanSeedTargetExpr0108 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (56593, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (363, 200000)
  let e3 : LowMeanIntegerExpr := .atom (13, 1)
  let e4 : LowMeanIntegerExpr := .atom (33, 2)
  let e5 : LowMeanIntegerExpr := .neg (-33, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-7, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-2541, 400000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (100481, 2000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (4727, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (49, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (231623, 40000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-231623, 40000000) e11
  let e13 : LowMeanIntegerExpr := .add (1777997, 40000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (127803, 3496900) e29 e3
  let e31 : LowMeanIntegerExpr := .add (113295977093, 1398760000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1619, 1000)
  let e33 : LowMeanIntegerExpr := .pow (12207031250000000000000, 21982145917308330487013369) e21 13
  let e34 : LowMeanIntegerExpr := .mul (19763183593750000000000, 21982145917308330487013369) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-19763183593750000000000, 21982145917308330487013369) e34
  let e36 : LowMeanIntegerExpr := .add (2462844749618754333074740188208756317, 30747746423294200352014820022440000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (2463152227082987275078260336408980717, 30747746423294200352014820022440000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-2462844749618754333074740188208756317, 30747746423294200352014820022440000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0108 : LowMeanDirectSeedInput :=
  { record := 108, positions := [{ j := 3, mode := 0, left := 379, right := 0 }, { j := 8, mode := 0, left := 380, right := 0 }], target := { R := 13, expr := lowMeanSeedTargetExpr0108 } }

noncomputable def lowMeanSeedTargetExpr0109 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (56593, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (363, 200000)
  let e3 : LowMeanIntegerExpr := .atom (14, 1)
  let e4 : LowMeanIntegerExpr := .atom (33, 2)
  let e5 : LowMeanIntegerExpr := .neg (-33, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-5, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-363, 80000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (104111, 2000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (4727, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (25, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (4727, 1600000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-4727, 1600000) e11
  let e13 : LowMeanIntegerExpr := .add (392809, 8000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (68817, 1748450) e29 e3
  let e31 : LowMeanIntegerExpr := .add (24746857921, 279752000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1619, 1000)
  let e33 : LowMeanIntegerExpr := .pow (610351562500000000000000, 1956410986640441413344189841) e21 14
  let e34 : LowMeanIntegerExpr := .mul (988159179687500000000000, 1956410986640441413344189841) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-988159179687500000000000, 1956410986640441413344189841) e34
  let e36 : LowMeanIntegerExpr := .add (48138585214638495268753099466078580561, 547309886334636766265863796399432000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (48144058313501841636415758104042574881, 547309886334636766265863796399432000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-48138585214638495268753099466078580561, 547309886334636766265863796399432000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0109 : LowMeanDirectSeedInput :=
  { record := 109, positions := [{ j := 3, mode := 0, left := 381, right := 0 }, { j := 4, mode := 0, left := 382, right := 0 }, { j := 8, mode := 0, left := 383, right := 0 }], target := { R := 14, expr := lowMeanSeedTargetExpr0109 } }

noncomputable def lowMeanSeedTargetExpr0110 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (56593, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (363, 200000)
  let e3 : LowMeanIntegerExpr := .atom (15, 1)
  let e4 : LowMeanIntegerExpr := .atom (33, 2)
  let e5 : LowMeanIntegerExpr := .neg (-33, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-3, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1089, 400000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (107741, 2000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (4727, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (9, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (42543, 40000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-42543, 40000000) e11
  let e13 : LowMeanIntegerExpr := .add (2112277, 40000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (29493, 699380) e29 e3
  let e31 : LowMeanIntegerExpr := .add (132850214413, 1398760000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1619, 1000)
  let e33 : LowMeanIntegerExpr := .pow (30517578125000000000000000, 174120577810999285787632895849) e21 15
  let e34 : LowMeanIntegerExpr := .mul (49407958984375000000000000, 174120577810999285787632895849) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-49407958984375000000000000, 174120577810999285787632895849) e34
  let e36 : LowMeanIntegerExpr := .add (23062846219197720931676893797271747671637, 243552899418913360988309389397747240000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (23065281748191910065286776891165725144037, 243552899418913360988309389397747240000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-23062846219197720931676893797271747671637, 243552899418913360988309389397747240000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0110 : LowMeanDirectSeedInput :=
  { record := 110, positions := [{ j := 4, mode := 0, left := 384, right := 0 }, { j := 9, mode := 0, left := 385, right := 0 }], target := { R := 15, expr := lowMeanSeedTargetExpr0110 } }

noncomputable def lowMeanSeedTargetExpr0111 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (56593, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (363, 200000)
  let e3 : LowMeanIntegerExpr := .atom (16, 1)
  let e4 : LowMeanIntegerExpr := .atom (33, 2)
  let e5 : LowMeanIntegerExpr := .neg (-33, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-1, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-363, 400000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (111371, 2000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (4727, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (1, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (4727, 40000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-4727, 40000000) e11
  let e13 : LowMeanIntegerExpr := .add (2222693, 40000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (39324, 874225) e29 e3
  let e31 : LowMeanIntegerExpr := .add (140643751517, 1398760000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1619, 1000)
  let e33 : LowMeanIntegerExpr := .pow (1525878906250000000000000000, 15496731425178936435099327730561) e21 16
  let e34 : LowMeanIntegerExpr := .mul (2470397949218750000000000000, 15496731425178936435099327730561) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-2470397949218750000000000000, 15496731425178936435099327730561) e34
  let e36 : LowMeanIntegerExpr := .add (2176062950053102394490447646550768811011037, 21676208048283289127959535656399504360000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (2176279712133585227381727241907332806054637, 21676208048283289127959535656399504360000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-2176062950053102394490447646550768811011037, 21676208048283289127959535656399504360000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0111 : LowMeanDirectSeedInput :=
  { record := 111, positions := [{ j := 4, mode := 0, left := 386, right := 0 }, { j := 5, mode := 0, left := 387, right := 0 }, { j := 9, mode := 0, left := 388, right := 0 }], target := { R := 16, expr := lowMeanSeedTargetExpr0111 } }

noncomputable def lowMeanSeedGroup0096 : List LowMeanDirectSeedInput := [lowMeanSeedRecord0096, lowMeanSeedRecord0097, lowMeanSeedRecord0098, lowMeanSeedRecord0099, lowMeanSeedRecord0100, lowMeanSeedRecord0101, lowMeanSeedRecord0102, lowMeanSeedRecord0103, lowMeanSeedRecord0104, lowMeanSeedRecord0105, lowMeanSeedRecord0106, lowMeanSeedRecord0107, lowMeanSeedRecord0108, lowMeanSeedRecord0109, lowMeanSeedRecord0110, lowMeanSeedRecord0111]

end Erdos993Lean.Analytic.V213
