module

public import Erdos993Lean.Analytic.V213.LowMeanCoreAll
public import Erdos993Lean.Analytic.V213.LowMeanData.Seed0144
public import Erdos993Lean.Analytic.V213.LowMeanFiberSeed
public import Erdos993Lean.Analytic.V213.LowMeanIntegerExpr
public import Erdos993Lean.Analytic.V213.LowMeanSeedGeometry
public import Erdos993Lean.Analytic.V213.LowMeanWidthData
public import Erdos993Lean.Ceiling.Prefix
public import Erdos993Lean.Ceiling.Statement

/-! Exact core/budget keys and equation-51 targets for the direct fibers. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanSeedTargetExpr0224 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (26161, 500000)
  let e2 : LowMeanIntegerExpr := .atom (6403, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (12, 1)
  let e4 : LowMeanIntegerExpr := .atom (45, 4)
  let e5 : LowMeanIntegerExpr := .neg (-45, 4) e4
  let e6 : LowMeanIntegerExpr := .add (3, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (19209, 40000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (2112089, 40000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (7621, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (9, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (68589, 160000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-68589, 160000000) e11
  let e13 : LowMeanIntegerExpr := .add (8379767, 160000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (7, 400)
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
  let e29 : LowMeanIntegerExpr := .mul (103, 23548) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (309, 5887) e29 e3
  let e31 : LowMeanIntegerExpr := .add (98771688329, 941920000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (576, 625)
  let e33 : LowMeanIntegerExpr := .pow (1000000000000000000000000, 4897252030306448390395044241) e21 12
  let e34 : LowMeanIntegerExpr := .mul (921600000000000000000000, 4897252030306448390395044241) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-921600000000000000000000, 4897252030306448390395044241) e34
  let e36 : LowMeanIntegerExpr := .add (82018307751654659890440466614271847, 783560324849031742463207078560000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (82026143354903150207865098685057447, 783560324849031742463207078560000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-82018307751654659890440466614271847, 783560324849031742463207078560000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0224 : LowMeanDirectSeedInput :=
  { record := 224, positions := [{ j := 5, mode := 0, left := 577, right := 0 }, { j := 8, mode := 0, left := 578, right := 0 }], target := { R := 12, expr := lowMeanSeedTargetExpr0224 } }

noncomputable def lowMeanSeedTargetExpr0225 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (26161, 500000)
  let e2 : LowMeanIntegerExpr := .atom (6403, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (13, 1)
  let e4 : LowMeanIntegerExpr := .atom (45, 4)
  let e5 : LowMeanIntegerExpr := .neg (-45, 4) e4
  let e6 : LowMeanIntegerExpr := .add (7, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (44821, 40000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (2137701, 40000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (7621, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (49, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (373429, 160000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-373429, 160000000) e11
  let e13 : LowMeanIntegerExpr := .add (65419, 1280000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (7, 400)
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
  let e29 : LowMeanIntegerExpr := .mul (103, 23548) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (1339, 23548) e29 e3
  let e31 : LowMeanIntegerExpr := .add (813601653, 7535360000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (576, 625)
  let e33 : LowMeanIntegerExpr := .pow (100000000000000000000000000, 994142162152209023250193980923) e21 13
  let e34 : LowMeanIntegerExpr := .mul (92160000000000000000000000, 994142162152209023250193980923) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-92160000000000000000000000, 994142162152209023250193980923) e34
  let e36 : LowMeanIntegerExpr := .add (137275564407411465758089562671921737, 1272501967554827549760248295581440000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (686441447135435070167935825774387757, 6362509837774137748801241477907200000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-137275564407411465758089562671921737, 1272501967554827549760248295581440000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0225 : LowMeanDirectSeedInput :=
  { record := 225, positions := [{ j := 6, mode := 0, left := 579, right := 0 }, { j := 8, mode := 0, left := 580, right := 0 }], target := { R := 13, expr := lowMeanSeedTargetExpr0225 } }

noncomputable def lowMeanSeedTargetExpr0226 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (26161, 500000)
  let e2 : LowMeanIntegerExpr := .atom (6403, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (14, 1)
  let e4 : LowMeanIntegerExpr := .atom (45, 4)
  let e5 : LowMeanIntegerExpr := .neg (-45, 4) e4
  let e6 : LowMeanIntegerExpr := .add (11, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (70433, 40000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (2163313, 40000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (7621, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (121, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (922141, 160000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-922141, 160000000) e11
  let e13 : LowMeanIntegerExpr := .add (7731111, 160000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (7, 400)
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
  let e29 : LowMeanIntegerExpr := .mul (103, 23548) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (103, 1682) e29 e3
  let e31 : LowMeanIntegerExpr := .add (14741864351, 134560000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (576, 625)
  let e33 : LowMeanIntegerExpr := .pow (10000000000000000000000000000, 201810858916898431719789378127369) e21 14
  let e34 : LowMeanIntegerExpr := .mul (9216000000000000000000000000, 201810858916898431719789378127369) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-9216000000000000000000000000, 201810858916898431719789378127369) e34
  let e36 : LowMeanIntegerExpr := .add (3536062071048413153457515641669821876959, 32289737426703749075166300500379040000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (3536384968422680190948267304674825667359, 32289737426703749075166300500379040000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-3536062071048413153457515641669821876959, 32289737426703749075166300500379040000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0226 : LowMeanDirectSeedInput :=
  { record := 226, positions := [{ j := 7, mode := 0, left := 581, right := 0 }, { j := 8, mode := 0, left := 582, right := 0 }], target := { R := 14, expr := lowMeanSeedTargetExpr0226 } }

noncomputable def lowMeanSeedTargetExpr0227 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (26161, 500000)
  let e2 : LowMeanIntegerExpr := .atom (6403, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (15, 1)
  let e4 : LowMeanIntegerExpr := .atom (45, 4)
  let e5 : LowMeanIntegerExpr := .neg (-45, 4) e4
  let e6 : LowMeanIntegerExpr := .add (15, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (19209, 8000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (87557, 1600000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (7621, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (225, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (68589, 6400000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-68589, 6400000) e11
  let e13 : LowMeanIntegerExpr := .add (281639, 6400000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (7, 400)
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
  let e29 : LowMeanIntegerExpr := .mul (103, 23548) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (1545, 23548) e29 e3
  let e31 : LowMeanIntegerExpr := .add (4130008793, 37676800000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (576, 625)
  let e33 : LowMeanIntegerExpr := .pow (1000000000000000000000000000000, 40967604360130381639117243759855907) e21 15
  let e34 : LowMeanIntegerExpr := .mul (921600000000000000000000000000, 40967604360130381639117243759855907) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-921600000000000000000000000000, 40967604360130381639117243759855907) e34
  let e36 : LowMeanIntegerExpr := .add (28734812858264585492780698061173649791573, 262192667904834442490350360063077804800000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (28737434784943633837205601564774280569621, 262192667904834442490350360063077804800000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-28734812858264585492780698061173649791573, 262192667904834442490350360063077804800000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0227 : LowMeanDirectSeedInput :=
  { record := 227, positions := [], target := { R := 15, expr := lowMeanSeedTargetExpr0227 } }

noncomputable def lowMeanSeedTargetExpr0228 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (31903, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (571, 500000)
  let e3 : LowMeanIntegerExpr := .atom (0, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-16, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-571, 31250) e2 e6
  let e8 : LowMeanIntegerExpr := .add (13631, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (89, 250000)
  let e10 : LowMeanIntegerExpr := .pow (256, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1424, 15625) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1424, 15625) e11
  let e13 : LowMeanIntegerExpr := .add (-15501, 200000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (0, 1) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-15501, 200000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (779, 500)
  let e33 : LowMeanIntegerExpr := .pow (1, 1) e21 0
  let e34 : LowMeanIntegerExpr := .mul (779, 500) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-779, 500) e34
  let e36 : LowMeanIntegerExpr := .add (-327101, 200000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-327099, 200000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (327101, 200000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0228 : LowMeanDirectSeedInput :=
  { record := 228, positions := [], target := { R := 0, expr := lowMeanSeedTargetExpr0228 } }

noncomputable def lowMeanSeedTargetExpr0229 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (31903, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (571, 500000)
  let e3 : LowMeanIntegerExpr := .atom (1, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-15, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1713, 100000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (14773, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (89, 250000)
  let e10 : LowMeanIntegerExpr := .pow (225, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (801, 10000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-801, 10000) e11
  let e13 : LowMeanIntegerExpr := .add (-65327, 1000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (3761, 500000)
  let e15 : LowMeanIntegerExpr := .atom (103, 203)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (107, 207)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .neg (-103, 203) e15
  let e20 : LowMeanIntegerExpr := .add (100, 203) e3 e19
  let e21 : LowMeanIntegerExpr := .mul (10300, 41209) e15 e20
  let e22 : LowMeanIntegerExpr := .neg (-107, 207) e17
  let e23 : LowMeanIntegerExpr := .add (100, 207) e3 e22
  let e24 : LowMeanIntegerExpr := .mul (10700, 42849) e17 e23
  let e25 : LowMeanIntegerExpr := .maximum (10300, 41209) e21 e24
  let e26 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e25
  let e27 : LowMeanIntegerExpr := .selectLE (10300, 41209) e15 e16 e26 e25
  let e28 : LowMeanIntegerExpr := .mul (387383, 206045000) e14 e27
  let e29 : LowMeanIntegerExpr := .mul (387383, 206045000) e28 e3
  let e30 : LowMeanIntegerExpr := .add (-2614583743, 41209000000) e13 e29
  let e31 : LowMeanIntegerExpr := .atom (779, 500)
  let e32 : LowMeanIntegerExpr := .pow (100, 203) e20 1
  let e33 : LowMeanIntegerExpr := .mul (779, 1015) e31 e32
  let e34 : LowMeanIntegerExpr := .neg (-779, 1015) e33
  let e35 : LowMeanIntegerExpr := .add (-34241983743, 41209000000) e30 e34
  let e36 : LowMeanIntegerExpr := .add (-34241571653, 41209000000) e0 e35
  let e37 : LowMeanIntegerExpr := .neg (34241983743, 41209000000) e35
  let e38 : LowMeanIntegerExpr := .add (1, 100000) e36 e37
  e38

noncomputable def lowMeanSeedRecord0229 : LowMeanDirectSeedInput :=
  { record := 229, positions := [], target := { R := 1, expr := lowMeanSeedTargetExpr0229 } }

noncomputable def lowMeanSeedTargetExpr0230 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (31903, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (571, 500000)
  let e3 : LowMeanIntegerExpr := .atom (2, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-14, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-3997, 250000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (3183, 200000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (89, 250000)
  let e10 : LowMeanIntegerExpr := .pow (196, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (4361, 62500) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-4361, 62500) e11
  let e13 : LowMeanIntegerExpr := .add (-53861, 1000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (387383, 103022500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-2064604749, 41209000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (779, 500)
  let e33 : LowMeanIntegerExpr := .pow (10000, 41209) e21 2
  let e34 : LowMeanIntegerExpr := .mul (15580, 41209) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-15580, 41209) e34
  let e36 : LowMeanIntegerExpr := .add (-17644604749, 41209000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-17644192659, 41209000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (17644604749, 41209000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0230 : LowMeanDirectSeedInput :=
  { record := 230, positions := [], target := { R := 2, expr := lowMeanSeedTargetExpr0230 } }

noncomputable def lowMeanSeedTargetExpr0231 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (31903, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (571, 500000)
  let e3 : LowMeanIntegerExpr := .atom (3, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-13, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-7423, 500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (17057, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (89, 250000)
  let e10 : LowMeanIntegerExpr := .pow (169, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (15041, 250000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-15041, 250000) e11
  let e13 : LowMeanIntegerExpr := .add (-43107, 1000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (1162149, 206045000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-1543966563, 41209000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (779, 500)
  let e33 : LowMeanIntegerExpr := .pow (1000000, 8365427) e21 3
  let e34 : LowMeanIntegerExpr := .mul (1558000, 8365427) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1558000, 8365427) e34
  let e36 : LowMeanIntegerExpr := .add (-1871425212289, 8365427000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-1871341558019, 8365427000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (1871425212289, 8365427000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0231 : LowMeanDirectSeedInput :=
  { record := 231, positions := [], target := { R := 3, expr := lowMeanSeedTargetExpr0231 } }

noncomputable def lowMeanSeedTargetExpr0232 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (31903, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (571, 500000)
  let e3 : LowMeanIntegerExpr := .atom (4, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-12, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1713, 125000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (18199, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (89, 250000)
  let e10 : LowMeanIntegerExpr := .pow (144, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (801, 15625) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-801, 15625) e11
  let e13 : LowMeanIntegerExpr := .add (-6613, 200000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (387383, 51511250) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-210533837, 8241800000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (779, 500)
  let e33 : LowMeanIntegerExpr := .pow (100000000, 1698181681) e21 4
  let e34 : LowMeanIntegerExpr := .mul (155800000, 1698181681) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-155800000, 1698181681) e34
  let e36 : LowMeanIntegerExpr := .add (-39835888888933, 339636336200000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-39832492525571, 339636336200000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (39835888888933, 339636336200000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0232 : LowMeanDirectSeedInput :=
  { record := 232, positions := [], target := { R := 4, expr := lowMeanSeedTargetExpr0232 } }

noncomputable def lowMeanSeedTargetExpr0233 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (31903, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (571, 500000)
  let e3 : LowMeanIntegerExpr := .atom (5, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-11, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-6281, 500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (19341, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (89, 250000)
  let e10 : LowMeanIntegerExpr := .pow (121, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (10769, 250000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-10769, 250000) e11
  let e13 : LowMeanIntegerExpr := .add (-4747, 200000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (387383, 41209000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-118142523, 8241800000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (779, 500)
  let e33 : LowMeanIntegerExpr := .pow (10000000000, 344730881243) e21 5
  let e34 : LowMeanIntegerExpr := .mul (15580000000, 344730881243) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-15580000000, 344730881243) e34
  let e36 : LowMeanIntegerExpr := .add (-4104312651752321, 68946176248600000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-820724637997967, 13789235249720000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (4104312651752321, 68946176248600000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0233 : LowMeanDirectSeedInput :=
  { record := 233, positions := [], target := { R := 5, expr := lowMeanSeedTargetExpr0233 } }

noncomputable def lowMeanSeedTargetExpr0234 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (31903, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (571, 500000)
  let e3 : LowMeanIntegerExpr := .atom (6, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-10, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-571, 50000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (20483, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (89, 250000)
  let e10 : LowMeanIntegerExpr := .pow (100, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (89, 2500) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-89, 2500) e11
  let e13 : LowMeanIntegerExpr := .add (-15117, 1000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (1162149, 103022500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-158096853, 41209000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (779, 500)
  let e33 : LowMeanIntegerExpr := .pow (1000000000000, 69980368892329) e21 6
  let e34 : LowMeanIntegerExpr := .mul (1558000000000, 69980368892329) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1558000000000, 69980368892329) e34
  let e36 : LowMeanIntegerExpr := .add (-1826477179588349893, 69980368892329000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-1825777375899426603, 69980368892329000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (1826477179588349893, 69980368892329000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0234 : LowMeanDirectSeedInput :=
  { record := 234, positions := [{ j := 1, mode := 0, left := 583, right := 0 }], target := { R := 6, expr := lowMeanSeedTargetExpr0234 } }

noncomputable def lowMeanSeedTargetExpr0235 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (31903, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (571, 500000)
  let e3 : LowMeanIntegerExpr := .atom (7, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-9, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-5139, 500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (173, 8000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (89, 250000)
  let e10 : LowMeanIntegerExpr := .pow (81, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (7209, 250000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-7209, 250000) e11
  let e13 : LowMeanIntegerExpr := .add (-7211, 1000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (387383, 29435000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (35025443, 5887000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (779, 500)
  let e33 : LowMeanIntegerExpr := .pow (100000000000000, 14206014885142787) e21 7
  let e34 : LowMeanIntegerExpr := .mul (155800000000000, 14206014885142787) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-155800000000000, 14206014885142787) e34
  let e36 : LowMeanIntegerExpr := .add (-71279537180784740457, 14206014885142787000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-71137477031933312587, 14206014885142787000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (71279537180784740457, 14206014885142787000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0235 : LowMeanDirectSeedInput :=
  { record := 235, positions := [{ j := 1, mode := 0, left := 584, right := 0 }, { j := 6, mode := 0, left := 585, right := 0 }], target := { R := 7, expr := lowMeanSeedTargetExpr0235 } }

noncomputable def lowMeanSeedTargetExpr0236 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (31903, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (571, 500000)
  let e3 : LowMeanIntegerExpr := .atom (8, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-8, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-571, 62500) e2 e6
  let e8 : LowMeanIntegerExpr := .add (22767, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (89, 250000)
  let e10 : LowMeanIntegerExpr := .pow (64, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (356, 15625) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-356, 15625) e11
  let e13 : LowMeanIntegerExpr := .add (-17, 1000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (387383, 25755625) e29 e3
  let e31 : LowMeanIntegerExpr := .add (619112247, 41209000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (779, 500)
  let e33 : LowMeanIntegerExpr := .pow (10000000000000000, 2883821021683985761) e21 8
  let e34 : LowMeanIntegerExpr := .mul (15580000000000000, 2883821021683985761) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-15580000000000000, 2883821021683985761) e34
  let e36 : LowMeanIntegerExpr := .add (27745703430818708253263, 2883821021683985761000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (27774541641035548110873, 2883821021683985761000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-27745703430818708253263, 2883821021683985761000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0236 : LowMeanDirectSeedInput :=
  { record := 236, positions := [{ j := 2, mode := 0, left := 586, right := 0 }], target := { R := 8, expr := lowMeanSeedTargetExpr0236 } }

noncomputable def lowMeanSeedTargetExpr0237 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (31903, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (571, 500000)
  let e3 : LowMeanIntegerExpr := .atom (9, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-7, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-3997, 500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (23909, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (89, 250000)
  let e10 : LowMeanIntegerExpr := .pow (49, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (4361, 250000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-4361, 250000) e11
  let e13 : LowMeanIntegerExpr := .add (1293, 200000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (3486447, 206045000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (192741117, 8241800000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (779, 500)
  let e33 : LowMeanIntegerExpr := .pow (1000000000000000000, 585415667401849109483) e21 9
  let e34 : LowMeanIntegerExpr := .mul (1558000000000000000, 585415667401849109483) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1558000000000000000, 585415667401849109483) e34
  let e36 : LowMeanIntegerExpr := .add (2426483177081047470873079, 117083133480369821896600000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (485530801683170233818409, 23416626696073964379320000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-2426483177081047470873079, 117083133480369821896600000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0237 : LowMeanDirectSeedInput :=
  { record := 237, positions := [{ j := 2, mode := 0, left := 587, right := 0 }, { j := 7, mode := 0, left := 588, right := 0 }], target := { R := 9, expr := lowMeanSeedTargetExpr0237 } }

noncomputable def lowMeanSeedTargetExpr0238 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (31903, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (571, 500000)
  let e3 : LowMeanIntegerExpr := .atom (10, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-6, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1713, 250000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (25051, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (89, 250000)
  let e10 : LowMeanIntegerExpr := .pow (36, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (801, 62500) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-801, 62500) e11
  let e13 : LowMeanIntegerExpr := .add (2447, 200000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (387383, 20604500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (255791623, 8241800000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (779, 500)
  let e33 : LowMeanIntegerExpr := .pow (100000000000000000000, 118839380482575369225049) e21 10
  let e34 : LowMeanIntegerExpr := .mul (155800000000000000000, 118839380482575369225049) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-155800000000000000000, 118839380482575369225049) e34
  let e36 : LowMeanIntegerExpr := .add (706497259578064910915080103, 23767876096515073845009800000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (706734938339030061653530201, 23767876096515073845009800000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-706497259578064910915080103, 23767876096515073845009800000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0238 : LowMeanDirectSeedInput :=
  { record := 238, positions := [{ j := 3, mode := 0, left := 589, right := 0 }], target := { R := 10, expr := lowMeanSeedTargetExpr0238 } }

noncomputable def lowMeanSeedTargetExpr0239 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (31903, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (571, 500000)
  let e3 : LowMeanIntegerExpr := .atom (11, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-5, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-571, 100000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (26193, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (89, 250000)
  let e10 : LowMeanIntegerExpr := .pow (25, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (89, 10000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-89, 10000) e11
  let e13 : LowMeanIntegerExpr := .add (17293, 1000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (4261213, 206045000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (1564869837, 41209000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (779, 500)
  let e33 : LowMeanIntegerExpr := .pow (10000000000000000000000, 24124394237962799952684947) e21 11
  let e34 : LowMeanIntegerExpr := .mul (15580000000000000000000, 24124394237962799952684947) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-15580000000000000000000, 24124394237962799952684947) e34
  let e36 : LowMeanIntegerExpr := .add (900519320024377829455257364271, 24124394237962799952684947000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (900760563966757457454784213741, 24124394237962799952684947000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-900519320024377829455257364271, 24124394237962799952684947000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0239 : LowMeanDirectSeedInput :=
  { record := 239, positions := [{ j := 8, mode := 0, left := 590, right := 0 }], target := { R := 11, expr := lowMeanSeedTargetExpr0239 } }

noncomputable def lowMeanSeedGroup0224 : List LowMeanDirectSeedInput := [lowMeanSeedRecord0224, lowMeanSeedRecord0225, lowMeanSeedRecord0226, lowMeanSeedRecord0227, lowMeanSeedRecord0228, lowMeanSeedRecord0229, lowMeanSeedRecord0230, lowMeanSeedRecord0231, lowMeanSeedRecord0232, lowMeanSeedRecord0233, lowMeanSeedRecord0234, lowMeanSeedRecord0235, lowMeanSeedRecord0236, lowMeanSeedRecord0237, lowMeanSeedRecord0238, lowMeanSeedRecord0239]

end Erdos993Lean.Analytic.V213
