module

public import Erdos993Lean.Analytic.V213.LowMeanCoreAll
public import Erdos993Lean.Analytic.V213.LowMeanData.Seed0128
public import Erdos993Lean.Analytic.V213.LowMeanFiberSeed
public import Erdos993Lean.Analytic.V213.LowMeanIntegerExpr
public import Erdos993Lean.Analytic.V213.LowMeanSeedGeometry
public import Erdos993Lean.Analytic.V213.LowMeanWidthData
public import Erdos993Lean.Ceiling.Prefix
public import Erdos993Lean.Ceiling.Statement

/-! Exact core/budget keys and equation-51 targets for the direct fibers. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanSeedTargetExpr0208 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (86799, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (-1229, 500000)
  let e3 : LowMeanIntegerExpr := .atom (9, 1)
  let e4 : LowMeanIntegerExpr := .atom (17, 2)
  let e5 : LowMeanIntegerExpr := .neg (-17, 2) e4
  let e6 : LowMeanIntegerExpr := .add (1, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1229, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (8557, 100000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (227, 200000)
  let e10 : LowMeanIntegerExpr := .pow (1, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (227, 800000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-227, 800000) e11
  let e13 : LowMeanIntegerExpr := .add (68229, 800000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (3957, 100000)
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
  let e29 : LowMeanIntegerExpr := .mul (407571, 41209000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (3668139, 41209000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (5746160061, 32967200000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (9851, 10000)
  let e33 : LowMeanIntegerExpr := .pow (1000000000000000000, 585415667401849109483) e21 9
  let e34 : LowMeanIntegerExpr := .mul (985100000000000000, 585415667401849109483) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-985100000000000000, 585415667401849109483) e34
  let e36 : LowMeanIntegerExpr := .add (80841955358978984941630007, 468332533921479287586400000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (80846638684318199734505871, 468332533921479287586400000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-80841955358978984941630007, 468332533921479287586400000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0208 : LowMeanDirectSeedInput :=
  { record := 208, positions := [], target := { R := 9, expr := lowMeanSeedTargetExpr0208 } }

noncomputable def lowMeanSeedTargetExpr0209 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (86799, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (-1229, 500000)
  let e3 : LowMeanIntegerExpr := .atom (10, 1)
  let e4 : LowMeanIntegerExpr := .atom (17, 2)
  let e5 : LowMeanIntegerExpr := .neg (-17, 2) e4
  let e6 : LowMeanIntegerExpr := .add (3, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-3687, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (10389, 125000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (227, 200000)
  let e10 : LowMeanIntegerExpr := .pow (9, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (2043, 800000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-2043, 800000) e11
  let e13 : LowMeanIntegerExpr := .add (322233, 4000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (3957, 100000)
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
  let e29 : LowMeanIntegerExpr := .mul (407571, 41209000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (407571, 4120900) e29 e3
  let e31 : LowMeanIntegerExpr := .add (29581739697, 164836000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (9851, 10000)
  let e33 : LowMeanIntegerExpr := .pow (100000000000000000000, 118839380482575369225049) e21 10
  let e34 : LowMeanIntegerExpr := .mul (98510000000000000000, 118839380482575369225049) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-98510000000000000000, 118839380482575369225049) e34
  let e36 : LowMeanIntegerExpr := .add (84914402796192259375356454417, 475357521930301476900196000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (84919156371411562390125456377, 475357521930301476900196000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-84914402796192259375356454417, 475357521930301476900196000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0209 : LowMeanDirectSeedInput :=
  { record := 209, positions := [{ j := 6, mode := 0, left := 562, right := 0 }], target := { R := 10, expr := lowMeanSeedTargetExpr0209 } }

noncomputable def lowMeanSeedTargetExpr0210 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (86799, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (-1229, 500000)
  let e3 : LowMeanIntegerExpr := .atom (11, 1)
  let e4 : LowMeanIntegerExpr := .atom (17, 2)
  let e5 : LowMeanIntegerExpr := .neg (-17, 2) e4
  let e6 : LowMeanIntegerExpr := .add (5, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1229, 200000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (40327, 500000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (227, 200000)
  let e10 : LowMeanIntegerExpr := .pow (25, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (227, 32000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-227, 32000) e11
  let e13 : LowMeanIntegerExpr := .add (294241, 4000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (3957, 100000)
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
  let e29 : LowMeanIntegerExpr := .mul (407571, 41209000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (4483281, 41209000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (30058501369, 164836000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (9851, 10000)
  let e33 : LowMeanIntegerExpr := .pow (10000000000000000000000, 24124394237962799952684947) e21 11
  let e34 : LowMeanIntegerExpr := .mul (9851000000000000000000, 24124394237962799952684947) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-9851000000000000000000, 24124394237962799952684947) e34
  let e36 : LowMeanIntegerExpr := .add (17557313640032530130526186382227, 96497576951851199810739788000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (17558278615802048642524293780107, 96497576951851199810739788000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-17557313640032530130526186382227, 96497576951851199810739788000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0210 : LowMeanDirectSeedInput :=
  { record := 210, positions := [{ j := 5, mode := 0, left := 563, right := 0 }, { j := 6, mode := 0, left := 564, right := 0 }], target := { R := 11, expr := lowMeanSeedTargetExpr0210 } }

noncomputable def lowMeanSeedTargetExpr0211 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (86799, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (-1229, 500000)
  let e3 : LowMeanIntegerExpr := .atom (12, 1)
  let e4 : LowMeanIntegerExpr := .atom (17, 2)
  let e5 : LowMeanIntegerExpr := .neg (-17, 2) e4
  let e6 : LowMeanIntegerExpr := .add (7, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-8603, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (19549, 250000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (227, 200000)
  let e10 : LowMeanIntegerExpr := .pow (49, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (11123, 800000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-11123, 800000) e11
  let e13 : LowMeanIntegerExpr := .add (257169, 4000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (3957, 100000)
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
  let e29 : LowMeanIntegerExpr := .mul (407571, 41209000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (1222713, 10302250) e29 e3
  let e31 : LowMeanIntegerExpr := .add (30161085321, 164836000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (9851, 10000)
  let e33 : LowMeanIntegerExpr := .pow (1000000000000000000000000, 4897252030306448390395044241) e21 12
  let e34 : LowMeanIntegerExpr := .mul (985100000000000000000000, 4897252030306448390395044241) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-985100000000000000000000, 4897252030306448390395044241) e34
  let e36 : LowMeanIntegerExpr := .add (3580384294229737865009780539405729, 19589008121225793561580176964000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (3580580184310950122945396341175369, 19589008121225793561580176964000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-3580384294229737865009780539405729, 19589008121225793561580176964000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0211 : LowMeanDirectSeedInput :=
  { record := 211, positions := [{ j := 6, mode := 0, left := 565, right := 0 }], target := { R := 12, expr := lowMeanSeedTargetExpr0211 } }

noncomputable def lowMeanSeedTargetExpr0212 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (26161, 500000)
  let e2 : LowMeanIntegerExpr := .atom (6403, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (0, 1)
  let e4 : LowMeanIntegerExpr := .atom (45, 4)
  let e5 : LowMeanIntegerExpr := .neg (-45, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-45, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-57627, 8000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (360949, 8000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (7621, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (2025, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (617301, 6400000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-617301, 6400000) e11
  let e13 : LowMeanIntegerExpr := .add (-1642709, 32000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (0, 1) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-1642709, 32000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (576, 625)
  let e33 : LowMeanIntegerExpr := .pow (1, 1) e21 0
  let e34 : LowMeanIntegerExpr := .mul (576, 625) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-576, 625) e34
  let e36 : LowMeanIntegerExpr := .add (-31133909, 32000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-31133589, 32000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (31133909, 32000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0212 : LowMeanDirectSeedInput :=
  { record := 212, positions := [], target := { R := 0, expr := lowMeanSeedTargetExpr0212 } }

noncomputable def lowMeanSeedTargetExpr0213 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (26161, 500000)
  let e2 : LowMeanIntegerExpr := .atom (6403, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (1, 1)
  let e4 : LowMeanIntegerExpr := .atom (45, 4)
  let e5 : LowMeanIntegerExpr := .neg (-45, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-41, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-262523, 40000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (1830357, 40000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (7621, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (1681, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (12810901, 160000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-12810901, 160000000) e11
  let e13 : LowMeanIntegerExpr := .add (-5489473, 160000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (7, 400)
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
  let e28 : LowMeanIntegerExpr := .mul (103, 23548) e14 e27
  let e29 : LowMeanIntegerExpr := .mul (103, 23548) e28 e3
  let e30 : LowMeanIntegerExpr := .add (-28196527551, 941920000000) e13 e29
  let e31 : LowMeanIntegerExpr := .atom (576, 625)
  let e32 : LowMeanIntegerExpr := .pow (100, 203) e20 1
  let e33 : LowMeanIntegerExpr := .mul (2304, 5075) e31 e32
  let e34 : LowMeanIntegerExpr := .neg (-2304, 5075) e33
  let e35 : LowMeanIntegerExpr := .add (-455818927551, 941920000000) e30 e34
  let e36 : LowMeanIntegerExpr := .add (-455809508351, 941920000000) e0 e35
  let e37 : LowMeanIntegerExpr := .neg (455818927551, 941920000000) e35
  let e38 : LowMeanIntegerExpr := .add (1, 100000) e36 e37
  e38

noncomputable def lowMeanSeedRecord0213 : LowMeanDirectSeedInput :=
  { record := 213, positions := [], target := { R := 1, expr := lowMeanSeedTargetExpr0213 } }

noncomputable def lowMeanSeedTargetExpr0214 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (26161, 500000)
  let e2 : LowMeanIntegerExpr := .atom (6403, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (2, 1)
  let e4 : LowMeanIntegerExpr := .atom (45, 4)
  let e5 : LowMeanIntegerExpr := .neg (-45, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-37, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-236911, 40000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (1855969, 40000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (7621, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (1369, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (10433149, 160000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-10433149, 160000000) e11
  let e13 : LowMeanIntegerExpr := .add (-3009273, 160000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (103, 11774) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-9475590151, 941920000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (576, 625)
  let e33 : LowMeanIntegerExpr := .pow (10000, 41209) e21 2
  let e34 : LowMeanIntegerExpr := .mul (9216, 41209) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-9216, 41209) e34
  let e36 : LowMeanIntegerExpr := .add (-1540889131057, 6593440000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-1540823196657, 6593440000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (1540889131057, 6593440000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0214 : LowMeanDirectSeedInput :=
  { record := 214, positions := [], target := { R := 2, expr := lowMeanSeedTargetExpr0214 } }

noncomputable def lowMeanSeedTargetExpr0215 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (26161, 500000)
  let e2 : LowMeanIntegerExpr := .atom (6403, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (3, 1)
  let e4 : LowMeanIntegerExpr := .atom (45, 4)
  let e5 : LowMeanIntegerExpr := .neg (-45, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-33, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-211299, 40000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (1881581, 40000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (7621, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (1089, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (8299269, 160000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-8299269, 160000000) e11
  let e13 : LowMeanIntegerExpr := .add (-154589, 32000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (309, 23548) e29 e3
  let e31 : LowMeanIntegerExpr := .add (1561934557, 188384000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (576, 625)
  let e33 : LowMeanIntegerExpr := .pow (1000000, 8365427) e21 3
  let e34 : LowMeanIntegerExpr := .mul (921600, 8365427) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-921600, 8365427) e34
  let e36 : LowMeanIntegerExpr := .add (-27271690994503, 267693664000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-27269014057863, 267693664000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (27271690994503, 267693664000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0215 : LowMeanDirectSeedInput :=
  { record := 215, positions := [{ j := 0, mode := 0, left := 566, right := 0 }], target := { R := 3, expr := lowMeanSeedTargetExpr0215 } }

noncomputable def lowMeanSeedTargetExpr0216 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (26161, 500000)
  let e2 : LowMeanIntegerExpr := .atom (6403, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (4, 1)
  let e4 : LowMeanIntegerExpr := .atom (45, 4)
  let e5 : LowMeanIntegerExpr := .neg (-45, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-29, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-185687, 40000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (1907193, 40000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (7621, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (841, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (6409261, 160000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-6409261, 160000000) e11
  let e13 : LowMeanIntegerExpr := .add (1219511, 160000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (103, 5887) e29 e3
  let e31 : LowMeanIntegerExpr := .add (23659261257, 941920000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (576, 625)
  let e33 : LowMeanIntegerExpr := .pow (100000000, 1698181681) e21 4
  let e34 : LowMeanIntegerExpr := .mul (92160000, 1698181681) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-92160000, 1698181681) e34
  let e36 : LowMeanIntegerExpr := .add (-7920778520022009, 271709068960000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-7918061429332409, 271709068960000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (7920778520022009, 271709068960000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0216 : LowMeanDirectSeedInput :=
  { record := 216, positions := [{ j := 0, mode := 0, left := 567, right := 0 }, { j := 4, mode := 0, left := 568, right := 0 }], target := { R := 4, expr := lowMeanSeedTargetExpr0216 } }

noncomputable def lowMeanSeedTargetExpr0217 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (26161, 500000)
  let e2 : LowMeanIntegerExpr := .atom (6403, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (5, 1)
  let e4 : LowMeanIntegerExpr := .atom (45, 4)
  let e5 : LowMeanIntegerExpr := .neg (-45, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-25, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-6403, 1600000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (386561, 8000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (7621, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (625, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (7621, 256000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-7621, 256000) e11
  let e13 : LowMeanIntegerExpr := .add (593619, 32000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (515, 23548) e29 e3
  let e31 : LowMeanIntegerExpr := .add (7614635053, 188384000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (576, 625)
  let e33 : LowMeanIntegerExpr := .pow (10000000000, 344730881243) e21 5
  let e34 : LowMeanIntegerExpr := .mul (9216000000, 344730881243) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-9216000000, 344730881243) e34
  let e36 : LowMeanIntegerExpr := .add (150985715672588417, 11031388199776000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (151096029554586177, 11031388199776000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-150985715672588417, 11031388199776000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0217 : LowMeanDirectSeedInput :=
  { record := 217, positions := [{ j := 1, mode := 0, left := 569, right := 0 }], target := { R := 5, expr := lowMeanSeedTargetExpr0217 } }

noncomputable def lowMeanSeedTargetExpr0218 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (26161, 500000)
  let e2 : LowMeanIntegerExpr := .atom (6403, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (6, 1)
  let e4 : LowMeanIntegerExpr := .atom (45, 4)
  let e5 : LowMeanIntegerExpr := .neg (-45, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-21, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-134463, 40000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (1958417, 40000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (7621, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (441, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (3360861, 160000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-3360861, 160000000) e11
  let e13 : LowMeanIntegerExpr := .add (4472807, 160000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (309, 11774) e29 e3
  let e31 : LowMeanIntegerExpr := .add (51051414809, 941920000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (576, 625)
  let e33 : LowMeanIntegerExpr := .pow (1000000000000, 69980368892329) e21 6
  let e34 : LowMeanIntegerExpr := .mul (921600000000, 69980368892329) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-921600000000, 69980368892329) e34
  let e36 : LowMeanIntegerExpr := .add (459406041924431397503, 11196859022772640000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (459518010514659123903, 11196859022772640000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-459406041924431397503, 11196859022772640000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0218 : LowMeanDirectSeedInput :=
  { record := 218, positions := [{ j := 1, mode := 0, left := 570, right := 0 }, { j := 5, mode := 0, left := 571, right := 0 }], target := { R := 6, expr := lowMeanSeedTargetExpr0218 } }

noncomputable def lowMeanSeedTargetExpr0219 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (26161, 500000)
  let e2 : LowMeanIntegerExpr := .atom (6403, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (7, 1)
  let e4 : LowMeanIntegerExpr := .atom (45, 4)
  let e5 : LowMeanIntegerExpr := .neg (-45, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-17, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-108851, 40000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (1984029, 40000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (7621, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (289, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (2202469, 160000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-2202469, 160000000) e11
  let e13 : LowMeanIntegerExpr := .add (5733647, 160000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (103, 3364) e29 e3
  let e31 : LowMeanIntegerExpr := .add (8941997127, 134560000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (576, 625)
  let e33 : LowMeanIntegerExpr := .pow (100000000000000, 14206014885142787) e21 7
  let e34 : LowMeanIntegerExpr := .mul (92160000000000, 14206014885142787) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-92160000000000, 14206014885142787) e34
  let e36 : LowMeanIntegerExpr := .add (136300944933491125254189, 2272962381622845920000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (136323674557307353713389, 2272962381622845920000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-136300944933491125254189, 2272962381622845920000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0219 : LowMeanDirectSeedInput :=
  { record := 219, positions := [{ j := 2, mode := 0, left := 572, right := 0 }], target := { R := 7, expr := lowMeanSeedTargetExpr0219 } }

noncomputable def lowMeanSeedTargetExpr0220 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (26161, 500000)
  let e2 : LowMeanIntegerExpr := .atom (6403, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (8, 1)
  let e4 : LowMeanIntegerExpr := .atom (45, 4)
  let e5 : LowMeanIntegerExpr := .neg (-45, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-13, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-83239, 40000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (2009641, 40000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (7621, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (169, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1287949, 160000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1287949, 160000000) e11
  let e13 : LowMeanIntegerExpr := .add (1350123, 32000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (206, 5887) e29 e3
  let e31 : LowMeanIntegerExpr := .add (14540174101, 188384000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (576, 625)
  let e33 : LowMeanIntegerExpr := .pow (10000000000000000, 2883821021683985761) e21 8
  let e34 : LowMeanIntegerExpr := .mul (9216000000000000, 2883821021683985761) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-9216000000000000, 2883821021683985761) e34
  let e36 : LowMeanIntegerExpr := .add (6827775231426677283598603, 92282272693887544352000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (6828698054153616159042123, 92282272693887544352000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-6827775231426677283598603, 92282272693887544352000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0220 : LowMeanDirectSeedInput :=
  { record := 220, positions := [{ j := 6, mode := 0, left := 573, right := 0 }], target := { R := 8, expr := lowMeanSeedTargetExpr0220 } }

noncomputable def lowMeanSeedTargetExpr0221 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (26161, 500000)
  let e2 : LowMeanIntegerExpr := .atom (6403, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (9, 1)
  let e4 : LowMeanIntegerExpr := .atom (45, 4)
  let e5 : LowMeanIntegerExpr := .neg (-45, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-9, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-57627, 40000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (2035253, 40000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (7621, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (81, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (617301, 160000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-617301, 160000000) e11
  let e13 : LowMeanIntegerExpr := .add (7523711, 160000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (927, 23548) e29 e3
  let e31 : LowMeanIntegerExpr := .add (81372086657, 941920000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (576, 625)
  let e33 : LowMeanIntegerExpr := .pow (1000000000000000000, 585415667401849109483) e21 9
  let e34 : LowMeanIntegerExpr := .mul (921600000000000000, 585415667401849109483) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-921600000000000000, 585415667401849109483) e34
  let e36 : LowMeanIntegerExpr := .add (7944355519991295359077451413, 93666506784295857517280000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (7945292185059138317652624213, 93666506784295857517280000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-7944355519991295359077451413, 93666506784295857517280000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0221 : LowMeanDirectSeedInput :=
  { record := 221, positions := [{ j := 3, mode := 0, left := 574, right := 0 }], target := { R := 9, expr := lowMeanSeedTargetExpr0221 } }

noncomputable def lowMeanSeedTargetExpr0222 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (26161, 500000)
  let e2 : LowMeanIntegerExpr := .atom (6403, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (10, 1)
  let e4 : LowMeanIntegerExpr := .atom (45, 4)
  let e5 : LowMeanIntegerExpr := .neg (-45, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-5, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-6403, 8000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (412173, 8000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (7621, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (25, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (7621, 6400000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-7621, 6400000) e11
  let e13 : LowMeanIntegerExpr := .add (1610587, 32000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (515, 11774) e29 e3
  let e31 : LowMeanIntegerExpr := .add (17721525669, 188384000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (576, 625)
  let e33 : LowMeanIntegerExpr := .pow (100000000000000000000, 118839380482575369225049) e21 10
  let e34 : LowMeanIntegerExpr := .mul (92160000000000000000, 118839380482575369225049) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-92160000000000000000, 118839380482575369225049) e34
  let e36 : LowMeanIntegerExpr := .add (354790837824021914888543993763, 3802860175442411815201568000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (354828866425776339006696009443, 3802860175442411815201568000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-354790837824021914888543993763, 3802860175442411815201568000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0222 : LowMeanDirectSeedInput :=
  { record := 222, positions := [{ j := 7, mode := 0, left := 575, right := 0 }], target := { R := 10, expr := lowMeanSeedTargetExpr0222 } }

noncomputable def lowMeanSeedTargetExpr0223 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (26161, 500000)
  let e2 : LowMeanIntegerExpr := .atom (6403, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (11, 1)
  let e4 : LowMeanIntegerExpr := .atom (45, 4)
  let e5 : LowMeanIntegerExpr := .neg (-45, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-1, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-6403, 40000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (2086477, 40000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (7621, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (1, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (7621, 160000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-7621, 160000000) e11
  let e13 : LowMeanIntegerExpr := .add (8338287, 160000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (1133, 23548) e29 e3
  let e31 : LowMeanIntegerExpr := .add (94407495569, 941920000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (576, 625)
  let e33 : LowMeanIntegerExpr := .pow (10000000000000000000000, 24124394237962799952684947) e21 11
  let e34 : LowMeanIntegerExpr := .mul (9216000000000000000000, 24124394237962799952684947) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-9216000000000000000000, 24124394237962799952684947) e34
  let e36 : LowMeanIntegerExpr := .add (385398829183842732821460428665789, 3859903078074047992429591520000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (385437428214623473301384724580989, 3859903078074047992429591520000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-385398829183842732821460428665789, 3859903078074047992429591520000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0223 : LowMeanDirectSeedInput :=
  { record := 223, positions := [{ j := 7, mode := 0, left := 576, right := 0 }], target := { R := 11, expr := lowMeanSeedTargetExpr0223 } }

noncomputable def lowMeanSeedGroup0208 : List LowMeanDirectSeedInput := [lowMeanSeedRecord0208, lowMeanSeedRecord0209, lowMeanSeedRecord0210, lowMeanSeedRecord0211, lowMeanSeedRecord0212, lowMeanSeedRecord0213, lowMeanSeedRecord0214, lowMeanSeedRecord0215, lowMeanSeedRecord0216, lowMeanSeedRecord0217, lowMeanSeedRecord0218, lowMeanSeedRecord0219, lowMeanSeedRecord0220, lowMeanSeedRecord0221, lowMeanSeedRecord0222, lowMeanSeedRecord0223]

end Erdos993Lean.Analytic.V213
