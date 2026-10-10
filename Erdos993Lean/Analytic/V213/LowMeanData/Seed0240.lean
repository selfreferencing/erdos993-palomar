module

public import Erdos993Lean.Analytic.V213.LowMeanCoreAll
public import Erdos993Lean.Analytic.V213.LowMeanData.Seed0096
public import Erdos993Lean.Analytic.V213.LowMeanFiberSeed
public import Erdos993Lean.Analytic.V213.LowMeanIntegerExpr
public import Erdos993Lean.Analytic.V213.LowMeanSeedGeometry
public import Erdos993Lean.Analytic.V213.LowMeanWidthData
public import Erdos993Lean.Ceiling.Prefix
public import Erdos993Lean.Ceiling.Statement

/-! Exact core/budget keys and equation-51 targets for the direct fibers. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanSeedTargetExpr0240 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (31903, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (571, 500000)
  let e3 : LowMeanIntegerExpr := .atom (12, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-4, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-571, 125000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (5467, 200000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (89, 250000)
  let e10 : LowMeanIntegerExpr := .pow (16, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (89, 15625) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-89, 15625) e11
  let e13 : LowMeanIntegerExpr := .add (21639, 1000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (3761, 500000)
  let e15 : LowMeanIntegerExpr := .atom (103, 203)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (107, 207)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-103, 203) e15
  let e21 : LowMeanIntegerExpr := .add (100, 203) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (10300, 41209) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-107, 207) e17
  let e24 : LowMeanIntegerExpr := .add (100, 207) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (10700, 42849) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (10300, 41209) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (10300, 41209) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (387383, 206045000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (1162149, 51511250) e29 e3
  let e31 : LowMeanIntegerExpr := .add (1821440751, 41209000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (779, 500)
  let e33 : LowMeanIntegerExpr := .pow (1000000000000000000000000, 4897252030306448390395044241) e21 12
  let e34 : LowMeanIntegerExpr := .mul (1558000000000000000000000, 4897252030306448390395044241) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1558000000000000000000000, 4897252030306448390395044241) e34
  let e36 : LowMeanIntegerExpr := .add (214900890434556822935375538571799, 4897252030306448390395044241000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (214949862954859887419279489014209, 4897252030306448390395044241000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-214900890434556822935375538571799, 4897252030306448390395044241000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0240 : LowMeanDirectSeedInput :=
  { record := 240, positions := [{ j := 4, mode := 0, left := 591, right := 0 }], target := { R := 12, expr := lowMeanSeedTargetExpr0240 } }

noncomputable def lowMeanSeedTargetExpr0241 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (31903, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (571, 500000)
  let e3 : LowMeanIntegerExpr := .atom (13, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-3, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1713, 500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (28477, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (89, 250000)
  let e10 : LowMeanIntegerExpr := .pow (9, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (801, 250000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-801, 250000) e11
  let e13 : LowMeanIntegerExpr := .add (25273, 1000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (3761, 500000)
  let e15 : LowMeanIntegerExpr := .atom (103, 203)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (107, 207)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-103, 203) e15
  let e21 : LowMeanIntegerExpr := .add (100, 203) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (10300, 41209) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-107, 207) e17
  let e24 : LowMeanIntegerExpr := .add (100, 207) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (10700, 42849) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (10300, 41209) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (10300, 41209) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (387383, 206045000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (5035979, 206045000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (2048670857, 41209000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (779, 500)
  let e33 : LowMeanIntegerExpr := .pow (100000000000000000000000000, 994142162152209023250193980923) e21 13
  let e34 : LowMeanIntegerExpr := .mul (155800000000000000000000000, 994142162152209023250193980923) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-155800000000000000000000000, 994142162152209023250193980923) e34
  let e36 : LowMeanIntegerExpr := .add (49267143418093111313186629821489579, 994142162152209023250193980923000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (49277084839714633403419131761298809, 994142162152209023250193980923000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-49267143418093111313186629821489579, 994142162152209023250193980923000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0241 : LowMeanDirectSeedInput :=
  { record := 241, positions := [{ j := 9, mode := 0, left := 592, right := 0 }], target := { R := 13, expr := lowMeanSeedTargetExpr0241 } }

noncomputable def lowMeanSeedTargetExpr0242 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (31903, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (571, 500000)
  let e3 : LowMeanIntegerExpr := .atom (14, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-2, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-571, 250000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (29619, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (89, 250000)
  let e10 : LowMeanIntegerExpr := .pow (4, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (89, 62500) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-89, 62500) e11
  let e13 : LowMeanIntegerExpr := .add (5639, 200000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (3761, 500000)
  let e15 : LowMeanIntegerExpr := .atom (103, 203)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (107, 207)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-103, 203) e15
  let e21 : LowMeanIntegerExpr := .add (100, 203) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (10300, 41209) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-107, 207) e17
  let e24 : LowMeanIntegerExpr := .add (100, 207) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (10700, 42849) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (10300, 41209) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (10300, 41209) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (387383, 206045000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (387383, 14717500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (64187433, 1177400000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (779, 500)
  let e33 : LowMeanIntegerExpr := .pow (10000000000000000000000000000, 201810858916898431719789378127369) e21 14
  let e34 : LowMeanIntegerExpr := .mul (15580000000000000000000000000, 201810858916898431719789378127369) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-15580000000000000000000000000, 201810858916898431719789378127369) e34
  let e36 : LowMeanIntegerExpr := .add (2197278256055863878685078220258563471, 40362171783379686343957875625473800000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (2197681877773697675548517799014818209, 40362171783379686343957875625473800000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-2197278256055863878685078220258563471, 40362171783379686343957875625473800000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0242 : LowMeanDirectSeedInput :=
  { record := 242, positions := [{ j := 5, mode := 0, left := 593, right := 0 }, { j := 9, mode := 0, left := 594, right := 0 }], target := { R := 14, expr := lowMeanSeedTargetExpr0242 } }

noncomputable def lowMeanSeedTargetExpr0243 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (31903, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (571, 500000)
  let e3 : LowMeanIntegerExpr := .atom (15, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-1, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-571, 500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (30761, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (89, 250000)
  let e10 : LowMeanIntegerExpr := .pow (1, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (89, 250000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-89, 250000) e11
  let e13 : LowMeanIntegerExpr := .add (6081, 200000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (3761, 500000)
  let e15 : LowMeanIntegerExpr := .atom (103, 203)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (107, 207)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-103, 203) e15
  let e21 : LowMeanIntegerExpr := .add (100, 203) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (10300, 41209) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-107, 207) e17
  let e24 : LowMeanIntegerExpr := .add (100, 207) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (10700, 42849) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (10300, 41209) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (10300, 41209) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (387383, 206045000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (1162149, 41209000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (483021729, 8241800000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (779, 500)
  let e33 : LowMeanIntegerExpr := .pow (1000000000000000000000000000000, 40967604360130381639117243759855907) e21 15
  let e34 : LowMeanIntegerExpr := .mul (1558000000000000000000000000000, 40967604360130381639117243759855907) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1558000000000000000000000000000, 40967604360130381639117243759855907) e34
  let e36 : LowMeanIntegerExpr := .add (479880666034558363579709896250820475867, 8193520872026076327823448751971181400000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (479962601243278624342988130738340187681, 8193520872026076327823448751971181400000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-479880666034558363579709896250820475867, 8193520872026076327823448751971181400000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0243 : LowMeanDirectSeedInput :=
  { record := 243, positions := [{ j := 6, mode := 0, left := 595, right := 0 }, { j := 10, mode := 0, left := 596, right := 0 }], target := { R := 15, expr := lowMeanSeedTargetExpr0243 } }

noncomputable def lowMeanSeedTargetExpr0244 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (31903, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (571, 500000)
  let e3 : LowMeanIntegerExpr := .atom (16, 1)
  let e4 : LowMeanIntegerExpr := .neg (-16, 1) e3
  let e5 : LowMeanIntegerExpr := .add (0, 1) e3 e4
  let e6 : LowMeanIntegerExpr := .mul (0, 1) e2 e5
  let e7 : LowMeanIntegerExpr := .add (31903, 1000000) e1 e6
  let e8 : LowMeanIntegerExpr := .atom (89, 250000)
  let e9 : LowMeanIntegerExpr := .pow (0, 1) e5 2
  let e10 : LowMeanIntegerExpr := .mul (0, 1) e8 e9
  let e11 : LowMeanIntegerExpr := .neg (0, 1) e10
  let e12 : LowMeanIntegerExpr := .add (31903, 1000000) e7 e11
  let e13 : LowMeanIntegerExpr := .atom (3761, 500000)
  let e14 : LowMeanIntegerExpr := .atom (103, 203)
  let e15 : LowMeanIntegerExpr := .atom (1, 2)
  let e16 : LowMeanIntegerExpr := .atom (107, 207)
  let e17 : LowMeanIntegerExpr := .atom (1, 4)
  let e18 : LowMeanIntegerExpr := .atom (1, 1)
  let e19 : LowMeanIntegerExpr := .neg (-103, 203) e14
  let e20 : LowMeanIntegerExpr := .add (100, 203) e18 e19
  let e21 : LowMeanIntegerExpr := .mul (10300, 41209) e14 e20
  let e22 : LowMeanIntegerExpr := .neg (-107, 207) e16
  let e23 : LowMeanIntegerExpr := .add (100, 207) e18 e22
  let e24 : LowMeanIntegerExpr := .mul (10700, 42849) e16 e23
  let e25 : LowMeanIntegerExpr := .maximum (10300, 41209) e21 e24
  let e26 : LowMeanIntegerExpr := .selectLE (1, 4) e15 e16 e17 e25
  let e27 : LowMeanIntegerExpr := .selectLE (10300, 41209) e14 e15 e26 e25
  let e28 : LowMeanIntegerExpr := .mul (387383, 206045000) e13 e27
  let e29 : LowMeanIntegerExpr := .mul (774766, 25755625) e28 e3
  let e30 : LowMeanIntegerExpr := .add (2554316327, 41209000000) e12 e29
  let e31 : LowMeanIntegerExpr := .atom (779, 500)
  let e32 : LowMeanIntegerExpr := .pow (100000000000000000000000000000000, 8316423685106467472740800483250749121) e20 16
  let e33 : LowMeanIntegerExpr := .mul (155800000000000000000000000000000, 8316423685106467472740800483250749121) e31 e32
  let e34 : LowMeanIntegerExpr := .neg (-155800000000000000000000000000000, 8316423685106467472740800483250749121) e33
  let e35 : LowMeanIntegerExpr := .add (515332971897327200342552697551915322253663, 8316423685106467472740800483250749121000000) e30 e34
  let e36 : LowMeanIntegerExpr := .add (515416136134178265017280105556747829744873, 8316423685106467472740800483250749121000000) e0 e35
  let e37 : LowMeanIntegerExpr := .neg (-515332971897327200342552697551915322253663, 8316423685106467472740800483250749121000000) e35
  let e38 : LowMeanIntegerExpr := .add (1, 100000) e36 e37
  e38

noncomputable def lowMeanSeedRecord0244 : LowMeanDirectSeedInput :=
  { record := 244, positions := [{ j := 6, mode := 0, left := 597, right := 0 }, { j := 10, mode := 0, left := 598, right := 0 }], target := { R := 16, expr := lowMeanSeedTargetExpr0244 } }

noncomputable def lowMeanSeedTargetExpr0245 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (31903, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (571, 500000)
  let e3 : LowMeanIntegerExpr := .atom (17, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (1, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (571, 500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (6609, 200000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (89, 250000)
  let e10 : LowMeanIntegerExpr := .pow (1, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (89, 250000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-89, 250000) e11
  let e13 : LowMeanIntegerExpr := .add (32689, 1000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (3761, 500000)
  let e15 : LowMeanIntegerExpr := .atom (103, 203)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (107, 207)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-103, 203) e15
  let e21 : LowMeanIntegerExpr := .add (100, 203) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (10300, 41209) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-107, 207) e17
  let e24 : LowMeanIntegerExpr := .add (100, 207) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (10700, 42849) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (10300, 41209) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (10300, 41209) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (387383, 206045000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (6585511, 206045000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (2664183201, 41209000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (779, 500)
  let e33 : LowMeanIntegerExpr := .pow (10000000000000000000000000000000000, 1688234008076612896966382498099902071563) e21 17
  let e34 : LowMeanIntegerExpr := .mul (15580000000000000000000000000000000, 1688234008076612896966382498099902071563) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-15580000000000000000000000000000000, 1688234008076612896966382498099902071563) e34
  let e36 : LowMeanIntegerExpr := .add (109129623321473716932655005294430185610018307, 1688234008076612896966382498099902071563000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (109146505661554483061624669119411184630733937, 1688234008076612896966382498099902071563000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-109129623321473716932655005294430185610018307, 1688234008076612896966382498099902071563000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0245 : LowMeanDirectSeedInput :=
  { record := 245, positions := [{ j := 7, mode := 0, left := 599, right := 0 }, { j := 10, mode := 0, left := 600, right := 0 }, { j := 11, mode := 0, left := 601, right := 0 }], target := { R := 17, expr := lowMeanSeedTargetExpr0245 } }

noncomputable def lowMeanSeedTargetExpr0246 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (31903, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (571, 500000)
  let e3 : LowMeanIntegerExpr := .atom (18, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (2, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (571, 250000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (34187, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (89, 250000)
  let e10 : LowMeanIntegerExpr := .pow (4, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (89, 62500) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-89, 62500) e11
  let e13 : LowMeanIntegerExpr := .add (32763, 1000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (3761, 500000)
  let e15 : LowMeanIntegerExpr := .atom (103, 203)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (107, 207)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-103, 203) e15
  let e21 : LowMeanIntegerExpr := .add (100, 203) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (10300, 41209) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-107, 207) e17
  let e24 : LowMeanIntegerExpr := .add (100, 207) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (10700, 42849) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (10300, 41209) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (10300, 41209) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (387383, 206045000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (3486447, 103022500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (2744709267, 41209000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (779, 500)
  let e33 : LowMeanIntegerExpr := .pow (1000000000000000000000000000000000000, 342711503639552418084175647114280120527289) e21 18
  let e34 : LowMeanIntegerExpr := .mul (1558000000000000000000000000000000000, 342711503639552418084175647114280120527289) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1558000000000000000000000000000000000, 342711503639552418084175647114280120527289) e34
  let e36 : LowMeanIntegerExpr := .add (22824607156810011154065744975376409397100804307, 342711503639552418084175647114280120527289000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (22828034271846406678246586731847552198306077197, 342711503639552418084175647114280120527289000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-22824607156810011154065744975376409397100804307, 342711503639552418084175647114280120527289000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0246 : LowMeanDirectSeedInput :=
  { record := 246, positions := [{ j := 8, mode := 0, left := 602, right := 0 }, { j := 11, mode := 0, left := 603, right := 0 }], target := { R := 18, expr := lowMeanSeedTargetExpr0246 } }

noncomputable def lowMeanSeedTargetExpr0247 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (31903, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (571, 500000)
  let e3 : LowMeanIntegerExpr := .atom (20, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (4, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (571, 125000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (36471, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (89, 250000)
  let e10 : LowMeanIntegerExpr := .pow (16, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (89, 15625) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-89, 15625) e11
  let e13 : LowMeanIntegerExpr := .add (1231, 40000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (3761, 500000)
  let e15 : LowMeanIntegerExpr := .atom (103, 203)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (107, 207)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-103, 203) e15
  let e21 : LowMeanIntegerExpr := .add (100, 203) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (10300, 41209) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-107, 207) e17
  let e24 : LowMeanIntegerExpr := .add (100, 207) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (10700, 42849) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (10300, 41209) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (10300, 41209) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (387383, 206045000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (387383, 10302250) e29 e3
  let e31 : LowMeanIntegerExpr := .add (112709559, 1648360000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (779, 500)
  let e33 : LowMeanIntegerExpr := .pow (10000000000000000000000000000000000000000, 14122798353482315596830794241932369486809052401) e21 20
  let e34 : LowMeanIntegerExpr := .mul (15580000000000000000000000000000000000000, 14122798353482315596830794241932369486809052401) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-15580000000000000000000000000000000000000, 14122798353482315596830794241932369486809052401) e34
  let e36 : LowMeanIntegerExpr := .add (38626239239440847999651062064790134987097590655551, 564911934139292623873231769677294779472362096040000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (193159441793911204629448971912434539674461571382557, 2824559670696463119366158848386473897361810480200000) e0 e36
  let e38 : LowMeanIntegerExpr := .atom (19, 1)
  let e39 : LowMeanIntegerExpr := .add (3, 1) e38 e5
  let e40 : LowMeanIntegerExpr := .mul (1713, 500000) e2 e39
  let e41 : LowMeanIntegerExpr := .add (35329, 1000000) e1 e40
  let e42 : LowMeanIntegerExpr := .pow (9, 1) e39 2
  let e43 : LowMeanIntegerExpr := .mul (801, 250000) e9 e42
  let e44 : LowMeanIntegerExpr := .neg (-801, 250000) e43
  let e45 : LowMeanIntegerExpr := .add (257, 8000) e41 e44
  let e46 : LowMeanIntegerExpr := .mul (7360277, 206045000) e29 e38
  let e47 : LowMeanIntegerExpr := .add (111835781, 1648360000) e45 e46
  let e48 : LowMeanIntegerExpr := .pow (100000000000000000000000000000000000000, 69570435238829140871087656364198864467039667) e21 19
  let e49 : LowMeanIntegerExpr := .mul (155800000000000000000000000000000000000, 69570435238829140871087656364198864467039667) e32 e48
  let e50 : LowMeanIntegerExpr := .neg (-155800000000000000000000000000000000000, 69570435238829140871087656364198864467039667) e49
  let e51 : LowMeanIntegerExpr := .add (188798736804008311166907917419733564196765995703, 2782817409553165634843506254567954578681586680000) e47 e50
  let e52 : LowMeanIntegerExpr := .neg (-188798736804008311166907917419733564196765995703, 2782817409553165634843506254567954578681586680000) e51
  let e53 : LowMeanIntegerExpr := .add (382180984460692198759358932851243003686021436003, 706139917674115779841539712096618474340452620050000) e37 e52
  e53

noncomputable def lowMeanSeedRecord0247 : LowMeanDirectSeedInput :=
  { record := 247, positions := [{ j := 8, mode := 0, left := 604, right := 0 }, { j := 9, mode := 0, left := 605, right := 0 }, { j := 11, mode := 0, left := 606, right := 0 }], target := { R := 20, expr := lowMeanSeedTargetExpr0247 } }

noncomputable def lowMeanSeedTargetExpr0248 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (85209, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (-123, 50000)
  let e3 : LowMeanIntegerExpr := .atom (0, 1)
  let e4 : LowMeanIntegerExpr := .atom (33, 4)
  let e5 : LowMeanIntegerExpr := .neg (-33, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-33, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (4059, 200000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (3297, 31250) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1511, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (1089, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1645479, 16000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1645479, 16000000) e11
  let e13 : LowMeanIntegerExpr := .add (8517, 3200000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (901, 25000)
  let e15 : LowMeanIntegerExpr := .atom (107, 207)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (11, 21)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-107, 207) e15
  let e21 : LowMeanIntegerExpr := .add (100, 207) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (10700, 42849) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-11, 21) e17
  let e24 : LowMeanIntegerExpr := .add (10, 21) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (110, 441) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (10700, 42849) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (10700, 42849) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (96407, 10712250) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (0, 1) e29 e3
  let e31 : LowMeanIntegerExpr := .add (8517, 3200000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (9441, 10000)
  let e33 : LowMeanIntegerExpr := .pow (1, 1) e21 0
  let e34 : LowMeanIntegerExpr := .mul (9441, 10000) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-9441, 10000) e34
  let e36 : LowMeanIntegerExpr := .add (-3012603, 3200000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-3012571, 3200000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (3012603, 3200000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0248 : LowMeanDirectSeedInput :=
  { record := 248, positions := [], target := { R := 0, expr := lowMeanSeedTargetExpr0248 } }

noncomputable def lowMeanSeedTargetExpr0249 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (85209, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (-123, 50000)
  let e3 : LowMeanIntegerExpr := .atom (1, 1)
  let e4 : LowMeanIntegerExpr := .atom (33, 4)
  let e5 : LowMeanIntegerExpr := .neg (-33, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-29, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (3567, 200000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (25761, 250000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1511, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (841, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1270751, 16000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1270751, 16000000) e11
  let e13 : LowMeanIntegerExpr := .add (377953, 16000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (901, 25000)
  let e15 : LowMeanIntegerExpr := .atom (107, 207)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (11, 21)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .neg (-107, 207) e15
  let e20 : LowMeanIntegerExpr := .add (100, 207) e3 e19
  let e21 : LowMeanIntegerExpr := .mul (10700, 42849) e15 e20
  let e22 : LowMeanIntegerExpr := .neg (-11, 21) e17
  let e23 : LowMeanIntegerExpr := .add (10, 21) e3 e22
  let e24 : LowMeanIntegerExpr := .mul (110, 441) e17 e23
  let e25 : LowMeanIntegerExpr := .maximum (10700, 42849) e21 e24
  let e26 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e25
  let e27 : LowMeanIntegerExpr := .selectLE (10700, 42849) e15 e16 e26 e25
  let e28 : LowMeanIntegerExpr := .mul (96407, 10712250) e14 e27
  let e29 : LowMeanIntegerExpr := .mul (96407, 10712250) e28 e3
  let e30 : LowMeanIntegerExpr := .add (22364956097, 685584000000) e13 e29
  let e31 : LowMeanIntegerExpr := .atom (9441, 10000)
  let e32 : LowMeanIntegerExpr := .pow (100, 207) e20 1
  let e33 : LowMeanIntegerExpr := .mul (1049, 2300) e31 e32
  let e34 : LowMeanIntegerExpr := .neg (-1049, 2300) e33
  let e35 : LowMeanIntegerExpr := .add (-290320963903, 685584000000) e30 e34
  let e36 : LowMeanIntegerExpr := .add (-290314108063, 685584000000) e0 e35
  let e37 : LowMeanIntegerExpr := .neg (290320963903, 685584000000) e35
  let e38 : LowMeanIntegerExpr := .add (1, 100000) e36 e37
  e38

noncomputable def lowMeanSeedRecord0249 : LowMeanDirectSeedInput :=
  { record := 249, positions := [], target := { R := 1, expr := lowMeanSeedTargetExpr0249 } }

noncomputable def lowMeanSeedTargetExpr0250 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (85209, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (-123, 50000)
  let e3 : LowMeanIntegerExpr := .atom (2, 1)
  let e4 : LowMeanIntegerExpr := .atom (33, 4)
  let e5 : LowMeanIntegerExpr := .neg (-33, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-25, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (123, 8000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (12573, 125000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1511, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (625, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1511, 25600) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1511, 25600) e11
  let e13 : LowMeanIntegerExpr := .add (664969, 16000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (901, 25000)
  let e15 : LowMeanIntegerExpr := .atom (107, 207)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (11, 21)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-107, 207) e15
  let e21 : LowMeanIntegerExpr := .add (100, 207) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (10700, 42849) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-11, 21) e17
  let e24 : LowMeanIntegerExpr := .add (10, 21) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (110, 441) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (10700, 42849) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (10700, 42849) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (96407, 10712250) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (96407, 5356125) e29 e3
  let e31 : LowMeanIntegerExpr := .add (40833352681, 685584000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (9441, 10000)
  let e33 : LowMeanIntegerExpr := .pow (10000, 42849) e21 2
  let e34 : LowMeanIntegerExpr := .mul (1049, 4761) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1049, 4761) e34
  let e36 : LowMeanIntegerExpr := .add (-110222647319, 685584000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-110215791479, 685584000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (110222647319, 685584000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0250 : LowMeanDirectSeedInput :=
  { record := 250, positions := [], target := { R := 2, expr := lowMeanSeedTargetExpr0250 } }

noncomputable def lowMeanSeedTargetExpr0251 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (85209, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (-123, 50000)
  let e3 : LowMeanIntegerExpr := .atom (3, 1)
  let e4 : LowMeanIntegerExpr := .atom (33, 4)
  let e5 : LowMeanIntegerExpr := .neg (-33, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-21, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (2583, 200000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (24531, 250000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1511, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (441, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (666351, 16000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-666351, 16000000) e11
  let e13 : LowMeanIntegerExpr := .add (903633, 16000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (901, 25000)
  let e15 : LowMeanIntegerExpr := .atom (107, 207)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (11, 21)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-107, 207) e15
  let e21 : LowMeanIntegerExpr := .add (100, 207) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (10700, 42849) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-11, 21) e17
  let e24 : LowMeanIntegerExpr := .add (10, 21) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (110, 441) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (10700, 42849) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (10700, 42849) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (96407, 10712250) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (96407, 3570750) e29 e3
  let e31 : LowMeanIntegerExpr := .add (19076638139, 228528000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (9441, 10000)
  let e33 : LowMeanIntegerExpr := .pow (1000000, 8869743) e21 3
  let e34 : LowMeanIntegerExpr := .mul (104900, 985527) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-104900, 985527) e34
  let e36 : LowMeanIntegerExpr := .add (-362111968409, 15768432000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-361954284089, 15768432000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (362111968409, 15768432000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0251 : LowMeanDirectSeedInput :=
  { record := 251, positions := [{ j := 0, mode := 0, left := 607, right := 0 }], target := { R := 3, expr := lowMeanSeedTargetExpr0251 } }

noncomputable def lowMeanSeedTargetExpr0252 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (85209, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (-123, 50000)
  let e3 : LowMeanIntegerExpr := .atom (4, 1)
  let e4 : LowMeanIntegerExpr := .atom (33, 4)
  let e5 : LowMeanIntegerExpr := .neg (-33, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-17, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (2091, 200000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (5979, 62500) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1511, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (289, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (436679, 16000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-436679, 16000000) e11
  let e13 : LowMeanIntegerExpr := .add (218789, 3200000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (901, 25000)
  let e15 : LowMeanIntegerExpr := .atom (107, 207)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (11, 21)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-107, 207) e15
  let e21 : LowMeanIntegerExpr := .add (100, 207) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (10700, 42849) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-11, 21) e17
  let e24 : LowMeanIntegerExpr := .add (10, 21) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (110, 441) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (10700, 42849) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (10700, 42849) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (96407, 10712250) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (192814, 5356125) e29 e3
  let e31 : LowMeanIntegerExpr := .add (14310928261, 137116800000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (9441, 10000)
  let e33 : LowMeanIntegerExpr := .pow (100000000, 1836036801) e21 4
  let e34 : LowMeanIntegerExpr := .mul (10490000, 204004089) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-10490000, 204004089) e34
  let e36 : LowMeanIntegerExpr := .add (34566329450621, 652813084800000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (34572857581469, 652813084800000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-34566329450621, 652813084800000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0252 : LowMeanDirectSeedInput :=
  { record := 252, positions := [{ j := 4, mode := 0, left := 608, right := 0 }], target := { R := 4, expr := lowMeanSeedTargetExpr0252 } }

noncomputable def lowMeanSeedTargetExpr0253 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (85209, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (-123, 50000)
  let e3 : LowMeanIntegerExpr := .atom (5, 1)
  let e4 : LowMeanIntegerExpr := .atom (33, 4)
  let e5 : LowMeanIntegerExpr := .neg (-33, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-13, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (1599, 200000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (23301, 250000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1511, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (169, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (255359, 16000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-255359, 16000000) e11
  let e13 : LowMeanIntegerExpr := .add (247181, 3200000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (901, 25000)
  let e15 : LowMeanIntegerExpr := .atom (107, 207)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (11, 21)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-107, 207) e15
  let e21 : LowMeanIntegerExpr := .add (100, 207) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (10700, 42849) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-11, 21) e17
  let e24 : LowMeanIntegerExpr := .add (10, 21) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (110, 441) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (10700, 42849) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (10700, 42849) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (96407, 10712250) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (96407, 2142450) e29 e3
  let e31 : LowMeanIntegerExpr := .add (16761506669, 137116800000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (9441, 10000)
  let e33 : LowMeanIntegerExpr := .pow (10000000000, 380059617807) e21 5
  let e34 : LowMeanIntegerExpr := .mul (1049000000, 42228846423) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1049000000, 42228846423) e34
  let e36 : LowMeanIntegerExpr := .add (13162117382979563, 135132308553600000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (13163468706065099, 135132308553600000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-13162117382979563, 135132308553600000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0253 : LowMeanDirectSeedInput :=
  { record := 253, positions := [{ j := 1, mode := 0, left := 609, right := 0 }], target := { R := 5, expr := lowMeanSeedTargetExpr0253 } }

noncomputable def lowMeanSeedTargetExpr0254 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (85209, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (-123, 50000)
  let e3 : LowMeanIntegerExpr := .atom (6, 1)
  let e4 : LowMeanIntegerExpr := .atom (33, 4)
  let e5 : LowMeanIntegerExpr := .neg (-33, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-9, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (1107, 200000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (11343, 125000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1511, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (81, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (122391, 16000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-122391, 16000000) e11
  let e13 : LowMeanIntegerExpr := .add (1329513, 16000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (901, 25000)
  let e15 : LowMeanIntegerExpr := .atom (107, 207)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (11, 21)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-107, 207) e15
  let e21 : LowMeanIntegerExpr := .add (100, 207) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (10700, 42849) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-11, 21) e17
  let e24 : LowMeanIntegerExpr := .add (10, 21) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (110, 441) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (10700, 42849) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (10700, 42849) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (96407, 10712250) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (96407, 1785375) e29 e3
  let e31 : LowMeanIntegerExpr := .add (31329530179, 228528000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (9441, 10000)
  let e33 : LowMeanIntegerExpr := .pow (1000000000000, 78672340886049) e21 6
  let e34 : LowMeanIntegerExpr := .mul (104900000000, 8741371209561) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-104900000000, 8741371209561) e34
  let e36 : LowMeanIntegerExpr := .add (17495656788894705793, 139861939352976000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (17497055408288235553, 139861939352976000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-17495656788894705793, 139861939352976000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0254 : LowMeanDirectSeedInput :=
  { record := 254, positions := [{ j := 5, mode := 0, left := 610, right := 0 }], target := { R := 6, expr := lowMeanSeedTargetExpr0254 } }

noncomputable def lowMeanSeedTargetExpr0255 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (85209, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (-123, 50000)
  let e3 : LowMeanIntegerExpr := .atom (7, 1)
  let e4 : LowMeanIntegerExpr := .atom (33, 4)
  let e5 : LowMeanIntegerExpr := .neg (-33, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-5, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (123, 40000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (22071, 250000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1511, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (25, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1511, 640000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1511, 640000) e11
  let e13 : LowMeanIntegerExpr := .add (1374769, 16000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (901, 25000)
  let e15 : LowMeanIntegerExpr := .atom (107, 207)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (11, 21)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-107, 207) e15
  let e21 : LowMeanIntegerExpr := .add (100, 207) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (10700, 42849) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-11, 21) e17
  let e24 : LowMeanIntegerExpr := .add (10, 21) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (110, 441) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (10700, 42849) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (10700, 42849) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (96407, 10712250) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (674849, 10712250) e29 e3
  let e31 : LowMeanIntegerExpr := .add (102097812881, 685584000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (9441, 10000)
  let e33 : LowMeanIntegerExpr := .pow (100000000000000, 16285174563412143) e21 7
  let e34 : LowMeanIntegerExpr := .mul (10490000000000, 1809463840379127) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-10490000000000, 1809463840379127) e34
  let e36 : LowMeanIntegerExpr := .add (4143632860275940174663, 28951421446066032000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (4143922374490400834983, 28951421446066032000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-4143632860275940174663, 28951421446066032000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0255 : LowMeanDirectSeedInput :=
  { record := 255, positions := [{ j := 5, mode := 0, left := 611, right := 0 }], target := { R := 7, expr := lowMeanSeedTargetExpr0255 } }

noncomputable def lowMeanSeedGroup0240 : List LowMeanDirectSeedInput := [lowMeanSeedRecord0240, lowMeanSeedRecord0241, lowMeanSeedRecord0242, lowMeanSeedRecord0243, lowMeanSeedRecord0244, lowMeanSeedRecord0245, lowMeanSeedRecord0246, lowMeanSeedRecord0247, lowMeanSeedRecord0248, lowMeanSeedRecord0249, lowMeanSeedRecord0250, lowMeanSeedRecord0251, lowMeanSeedRecord0252, lowMeanSeedRecord0253, lowMeanSeedRecord0254, lowMeanSeedRecord0255]

end Erdos993Lean.Analytic.V213
