module

public import Erdos993Lean.Analytic.V213.LowMeanCoreAll
public import Erdos993Lean.Analytic.V213.LowMeanData.Seed0160
public import Erdos993Lean.Analytic.V213.LowMeanFiberSeed
public import Erdos993Lean.Analytic.V213.LowMeanIntegerExpr
public import Erdos993Lean.Analytic.V213.LowMeanSeedGeometry
public import Erdos993Lean.Analytic.V213.LowMeanWidthData
public import Erdos993Lean.Ceiling.Prefix
public import Erdos993Lean.Ceiling.Statement

/-! Exact core/budget keys and equation-51 targets for the direct fibers. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanSeedTargetExpr0256 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (85209, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (-123, 50000)
  let e3 : LowMeanIntegerExpr := .atom (8, 1)
  let e4 : LowMeanIntegerExpr := .atom (33, 4)
  let e5 : LowMeanIntegerExpr := .neg (-33, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-1, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (123, 200000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (1341, 15625) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1511, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (1, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1511, 16000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1511, 16000000) e11
  let e13 : LowMeanIntegerExpr := .add (1371673, 16000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (385628, 5356125) e29 e3
  let e31 : LowMeanIntegerExpr := .add (108135200377, 685584000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (9441, 10000)
  let e33 : LowMeanIntegerExpr := .pow (10000000000000000, 3371031134626313601) e21 8
  let e34 : LowMeanIntegerExpr := .mul (1049000000000000, 374559014958479289) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1049000000000000, 374559014958479289) e34
  let e36 : LowMeanIntegerExpr := .add (928465927315617593204497, 5992944239335668624000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (928525856758010949890737, 5992944239335668624000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-928465927315617593204497, 5992944239335668624000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0256 : LowMeanDirectSeedInput :=
  { record := 256, positions := [], target := { R := 8, expr := lowMeanSeedTargetExpr0256 } }

noncomputable def lowMeanSeedTargetExpr0257 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (85209, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (-123, 50000)
  let e3 : LowMeanIntegerExpr := .atom (9, 1)
  let e4 : LowMeanIntegerExpr := .atom (33, 4)
  let e5 : LowMeanIntegerExpr := .neg (-33, 4) e4
  let e6 : LowMeanIntegerExpr := .add (3, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-369, 200000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (20841, 250000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1511, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (9, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (13599, 16000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-13599, 16000000) e11
  let e13 : LowMeanIntegerExpr := .add (52809, 640000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (96407, 1190250) e29 e3
  let e31 : LowMeanIntegerExpr := .add (498225569, 3047040000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (9441, 10000)
  let e33 : LowMeanIntegerExpr := .pow (1000000000000000000, 697803444867646915407) e21 9
  let e34 : LowMeanIntegerExpr := .mul (104900000000000000, 77533716096405212823) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-104900000000000000, 77533716096405212823) e34
  let e36 : LowMeanIntegerExpr := .add (8046554363120341527684367, 49621578301699336206720000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (40235252894516792605232171, 248107891508496681033600000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-8046554363120341527684367, 49621578301699336206720000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0257 : LowMeanDirectSeedInput :=
  { record := 257, positions := [{ j := 6, mode := 0, left := 612, right := 0 }], target := { R := 9, expr := lowMeanSeedTargetExpr0257 } }

noncomputable def lowMeanSeedTargetExpr0258 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (85209, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (-123, 50000)
  let e3 : LowMeanIntegerExpr := .atom (10, 1)
  let e4 : LowMeanIntegerExpr := .atom (33, 4)
  let e5 : LowMeanIntegerExpr := .neg (-33, 4) e4
  let e6 : LowMeanIntegerExpr := .add (7, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-861, 200000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (10113, 125000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1511, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (49, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (74039, 16000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-74039, 16000000) e11
  let e13 : LowMeanIntegerExpr := .add (48817, 640000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (96407, 1071225) e29 e3
  let e31 : LowMeanIntegerExpr := .add (4559778833, 27423360000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (9441, 10000)
  let e33 : LowMeanIntegerExpr := .pow (100000000000000000000, 144445313087602911489249) e21 10
  let e34 : LowMeanIntegerExpr := .mul (10490000000000000000, 16049479231955879054361) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-10490000000000000000, 16049479231955879054361) e34
  let e36 : LowMeanIntegerExpr := .add (1701192668117004235851089737, 10271666708451762594791040000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (8506476923920443767385188237, 51358333542258812973955200000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-1701192668117004235851089737, 10271666708451762594791040000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0258 : LowMeanDirectSeedInput :=
  { record := 258, positions := [{ j := 5, mode := 0, left := 613, right := 0 }, { j := 6, mode := 0, left := 614, right := 0 }], target := { R := 10, expr := lowMeanSeedTargetExpr0258 } }

noncomputable def lowMeanSeedTargetExpr0259 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (85209, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (-123, 50000)
  let e3 : LowMeanIntegerExpr := .atom (11, 1)
  let e4 : LowMeanIntegerExpr := .atom (33, 4)
  let e5 : LowMeanIntegerExpr := .neg (-33, 4) e4
  let e6 : LowMeanIntegerExpr := .add (11, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1353, 200000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (19611, 250000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1511, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (121, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (182831, 16000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-182831, 16000000) e11
  let e13 : LowMeanIntegerExpr := .add (1072273, 16000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (1060477, 10712250) e29 e3
  let e31 : LowMeanIntegerExpr := .add (113816353777, 685584000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (9441, 10000)
  let e33 : LowMeanIntegerExpr := .pow (10000000000000000000000, 29900179809133802678274543) e21 11
  let e34 : LowMeanIntegerExpr := .mul (1049000000000000000000, 3322242201014866964252727) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1049000000000000000000, 3322242201014866964252727) e34
  let e36 : LowMeanIntegerExpr := .add (8807820860873935140609544882471, 53155875216237871428043632000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (8808352419626097519323825318791, 53155875216237871428043632000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-8807820860873935140609544882471, 53155875216237871428043632000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0259 : LowMeanDirectSeedInput :=
  { record := 259, positions := [], target := { R := 11, expr := lowMeanSeedTargetExpr0259 } }

noncomputable def lowMeanSeedTargetExpr0260 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (867, 15625)
  let e2 : LowMeanIntegerExpr := .atom (771, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (0, 1)
  let e4 : LowMeanIntegerExpr := .atom (45, 4)
  let e5 : LowMeanIntegerExpr := .neg (-45, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-45, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-6939, 800000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (187257, 4000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (8851, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (2025, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (716931, 6400000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-716931, 6400000) e11
  let e13 : LowMeanIntegerExpr := .add (-2086599, 32000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (437, 25000)
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
  let e29 : LowMeanIntegerExpr := .mul (2033, 465750) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (0, 1) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-2086599, 32000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (909, 1000)
  let e33 : LowMeanIntegerExpr := .pow (1, 1) e21 0
  let e34 : LowMeanIntegerExpr := .mul (909, 1000) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-909, 1000) e34
  let e36 : LowMeanIntegerExpr := .add (-31174599, 32000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-31174279, 32000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (31174599, 32000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0260 : LowMeanDirectSeedInput :=
  { record := 260, positions := [], target := { R := 0, expr := lowMeanSeedTargetExpr0260 } }

noncomputable def lowMeanSeedTargetExpr0261 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (867, 15625)
  let e2 : LowMeanIntegerExpr := .atom (771, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (1, 1)
  let e4 : LowMeanIntegerExpr := .atom (45, 4)
  let e5 : LowMeanIntegerExpr := .neg (-45, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-41, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-31611, 4000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (190341, 4000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (8851, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (1681, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (14878531, 160000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-14878531, 160000000) e11
  let e13 : LowMeanIntegerExpr := .add (-7264891, 160000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (437, 25000)
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
  let e28 : LowMeanIntegerExpr := .mul (2033, 465750) e14 e27
  let e29 : LowMeanIntegerExpr := .mul (2033, 465750) e28 e3
  let e30 : LowMeanIntegerExpr := .add (-12233371933, 298080000000) e13 e29
  let e31 : LowMeanIntegerExpr := .atom (909, 1000)
  let e32 : LowMeanIntegerExpr := .pow (100, 207) e20 1
  let e33 : LowMeanIntegerExpr := .mul (101, 230) e31 e32
  let e34 : LowMeanIntegerExpr := .neg (-101, 230) e33
  let e35 : LowMeanIntegerExpr := .add (-6223016171, 12960000000) e30 e34
  let e36 : LowMeanIntegerExpr := .add (-6222886571, 12960000000) e0 e35
  let e37 : LowMeanIntegerExpr := .neg (6223016171, 12960000000) e35
  let e38 : LowMeanIntegerExpr := .add (1, 100000) e36 e37
  e38

noncomputable def lowMeanSeedRecord0261 : LowMeanDirectSeedInput :=
  { record := 261, positions := [], target := { R := 1, expr := lowMeanSeedTargetExpr0261 } }

noncomputable def lowMeanSeedTargetExpr0262 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (867, 15625)
  let e2 : LowMeanIntegerExpr := .atom (771, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (2, 1)
  let e4 : LowMeanIntegerExpr := .atom (45, 4)
  let e5 : LowMeanIntegerExpr := .neg (-45, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-37, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-28527, 4000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (7737, 160000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (8851, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (1369, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (12117019, 160000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-12117019, 160000000) e11
  let e13 : LowMeanIntegerExpr := .add (-4380019, 160000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (437, 25000)
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
  let e29 : LowMeanIntegerExpr := .mul (2033, 465750) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (2033, 232875) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-5557735397, 298080000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (909, 1000)
  let e33 : LowMeanIntegerExpr := .pow (10000, 42849) e21 2
  let e34 : LowMeanIntegerExpr := .mul (1010, 4761) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1010, 4761) e34
  let e36 : LowMeanIntegerExpr := .add (-1582227914131, 6855840000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-1582159355731, 6855840000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (1582227914131, 6855840000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0262 : LowMeanDirectSeedInput :=
  { record := 262, positions := [], target := { R := 2, expr := lowMeanSeedTargetExpr0262 } }

noncomputable def lowMeanSeedTargetExpr0263 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (867, 15625)
  let e2 : LowMeanIntegerExpr := .atom (771, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (3, 1)
  let e4 : LowMeanIntegerExpr := .atom (45, 4)
  let e5 : LowMeanIntegerExpr := .neg (-45, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-33, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-25443, 4000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (196509, 4000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (8851, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (1089, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (9638739, 160000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-9638739, 160000000) e11
  let e13 : LowMeanIntegerExpr := .add (-1778379, 160000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (437, 25000)
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
  let e29 : LowMeanIntegerExpr := .mul (2033, 465750) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (2033, 155250) e29 e3
  let e31 : LowMeanIntegerExpr := .add (196746641, 99360000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (909, 1000)
  let e33 : LowMeanIntegerExpr := .pow (1000000, 8869743) e21 3
  let e34 : LowMeanIntegerExpr := .mul (101000, 985527) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-101000, 985527) e34
  let e36 : LowMeanIntegerExpr := .add (-15847763080733, 157684320000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-15846186237533, 157684320000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (15847763080733, 157684320000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0263 : LowMeanDirectSeedInput :=
  { record := 263, positions := [], target := { R := 3, expr := lowMeanSeedTargetExpr0263 } }

noncomputable def lowMeanSeedTargetExpr0264 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (867, 15625)
  let e2 : LowMeanIntegerExpr := .atom (771, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (4, 1)
  let e4 : LowMeanIntegerExpr := .atom (45, 4)
  let e5 : LowMeanIntegerExpr := .neg (-45, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-29, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-22359, 4000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (199593, 4000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (8851, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (841, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (7443691, 160000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-7443691, 160000000) e11
  let e13 : LowMeanIntegerExpr := .add (540029, 160000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (437, 25000)
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
  let e29 : LowMeanIntegerExpr := .mul (2033, 465750) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (4066, 232875) e29 e3
  let e31 : LowMeanIntegerExpr := .add (6210554027, 298080000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (909, 1000)
  let e33 : LowMeanIntegerExpr := .pow (100000000, 1836036801) e21 4
  let e34 : LowMeanIntegerExpr := .mul (10100000, 204004089) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-10100000, 204004089) e34
  let e36 : LowMeanIntegerExpr := .add (-935925702381419, 32640654240000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-935599295839019, 32640654240000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (935925702381419, 32640654240000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0264 : LowMeanDirectSeedInput :=
  { record := 264, positions := [{ j := 0, mode := 0, left := 615, right := 0 }, { j := 4, mode := 0, left := 616, right := 0 }], target := { R := 4, expr := lowMeanSeedTargetExpr0264 } }

noncomputable def lowMeanSeedTargetExpr0265 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (867, 15625)
  let e2 : LowMeanIntegerExpr := .atom (771, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (5, 1)
  let e4 : LowMeanIntegerExpr := .atom (45, 4)
  let e5 : LowMeanIntegerExpr := .neg (-45, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-25, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-771, 160000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (202677, 4000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (8851, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (625, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (8851, 256000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-8851, 256000) e11
  let e13 : LowMeanIntegerExpr := .add (515041, 32000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (437, 25000)
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
  let e29 : LowMeanIntegerExpr := .mul (2033, 465750) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (2033, 93150) e29 e3
  let e31 : LowMeanIntegerExpr := .add (2260641383, 59616000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (909, 1000)
  let e33 : LowMeanIntegerExpr := .pow (10000000000, 380059617807) e21 5
  let e34 : LowMeanIntegerExpr := .mul (1010000000, 42228846423) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1010000000, 42228846423) e34
  let e36 : LowMeanIntegerExpr := .add (18922231766068343, 1351323085536000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (18935744996923703, 1351323085536000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-18922231766068343, 1351323085536000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0265 : LowMeanDirectSeedInput :=
  { record := 265, positions := [{ j := 1, mode := 0, left := 617, right := 0 }], target := { R := 5, expr := lowMeanSeedTargetExpr0265 } }

noncomputable def lowMeanSeedTargetExpr0266 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (867, 15625)
  let e2 : LowMeanIntegerExpr := .atom (771, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (6, 1)
  let e4 : LowMeanIntegerExpr := .atom (45, 4)
  let e5 : LowMeanIntegerExpr := .neg (-45, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-21, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-16191, 4000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (205761, 4000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (8851, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (441, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (3903291, 160000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-3903291, 160000000) e11
  let e13 : LowMeanIntegerExpr := .add (4327149, 160000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (437, 25000)
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
  let e29 : LowMeanIntegerExpr := .mul (2033, 465750) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (2033, 77625) e29 e3
  let e31 : LowMeanIntegerExpr := .add (5289399529, 99360000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (909, 1000)
  let e33 : LowMeanIntegerExpr := .pow (1000000000000, 78672340886049) e21 6
  let e34 : LowMeanIntegerExpr := .mul (101000000000, 8741371209561) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-101000000000, 8741371209561) e34
  let e36 : LowMeanIntegerExpr := .add (58295080126676511589, 1398619393529760000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (58309066320611809189, 1398619393529760000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-58295080126676511589, 1398619393529760000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0266 : LowMeanDirectSeedInput :=
  { record := 266, positions := [{ j := 1, mode := 0, left := 618, right := 0 }, { j := 5, mode := 0, left := 619, right := 0 }], target := { R := 6, expr := lowMeanSeedTargetExpr0266 } }

noncomputable def lowMeanSeedTargetExpr0267 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (867, 15625)
  let e2 : LowMeanIntegerExpr := .atom (771, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (7, 1)
  let e4 : LowMeanIntegerExpr := .atom (45, 4)
  let e5 : LowMeanIntegerExpr := .neg (-45, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-17, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-13107, 4000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (41769, 800000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (8851, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (289, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (2557939, 160000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-2557939, 160000000) e11
  let e13 : LowMeanIntegerExpr := .add (5795861, 160000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (437, 25000)
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
  let e29 : LowMeanIntegerExpr := .mul (2033, 465750) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (14231, 465750) e29 e3
  let e31 : LowMeanIntegerExpr := .add (19905529043, 298080000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (909, 1000)
  let e33 : LowMeanIntegerExpr := .pow (100000000000000, 16285174563412143) e21 7
  let e34 : LowMeanIntegerExpr := .mul (10100000000000, 1809463840379127) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-10100000000000, 1809463840379127) e34
  let e36 : LowMeanIntegerExpr := .add (17717513165284502753347, 289514214460660320000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (17720408307429109356547, 289514214460660320000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-17717513165284502753347, 289514214460660320000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0267 : LowMeanDirectSeedInput :=
  { record := 267, positions := [{ j := 2, mode := 0, left := 620, right := 0 }, { j := 6, mode := 0, left := 621, right := 0 }], target := { R := 7, expr := lowMeanSeedTargetExpr0267 } }

noncomputable def lowMeanSeedTargetExpr0268 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (867, 15625)
  let e2 : LowMeanIntegerExpr := .atom (771, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (8, 1)
  let e4 : LowMeanIntegerExpr := .atom (45, 4)
  let e5 : LowMeanIntegerExpr := .neg (-45, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-13, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-10023, 4000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (211929, 4000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (8851, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (169, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1495819, 160000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1495819, 160000000) e11
  let e13 : LowMeanIntegerExpr := .add (6981341, 160000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (437, 25000)
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
  let e29 : LowMeanIntegerExpr := .mul (2033, 465750) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (8132, 232875) e29 e3
  let e31 : LowMeanIntegerExpr := .add (23415198283, 298080000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (909, 1000)
  let e33 : LowMeanIntegerExpr := .pow (10000000000000000, 3371031134626313601) e21 8
  let e34 : LowMeanIntegerExpr := .mul (1010000000000000, 374559014958479289) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1010000000000000, 374559014958479289) e34
  let e36 : LowMeanIntegerExpr := .add (4546061623155102288826549, 59929442393356686240000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (4546660917579035855688949, 59929442393356686240000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-4546061623155102288826549, 59929442393356686240000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0268 : LowMeanDirectSeedInput :=
  { record := 268, positions := [{ j := 6, mode := 0, left := 622, right := 0 }], target := { R := 8, expr := lowMeanSeedTargetExpr0268 } }

noncomputable def lowMeanSeedTargetExpr0269 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (867, 15625)
  let e2 : LowMeanIntegerExpr := .atom (771, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (9, 1)
  let e4 : LowMeanIntegerExpr := .atom (45, 4)
  let e5 : LowMeanIntegerExpr := .neg (-45, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-9, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-6939, 4000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (215013, 4000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (8851, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (81, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (716931, 160000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-716931, 160000000) e11
  let e13 : LowMeanIntegerExpr := .add (7883589, 160000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (437, 25000)
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
  let e29 : LowMeanIntegerExpr := .mul (2033, 465750) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (2033, 51750) e29 e3
  let e31 : LowMeanIntegerExpr := .add (2933022923, 33120000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (909, 1000)
  let e33 : LowMeanIntegerExpr := .pow (1000000000000000000, 697803444867646915407) e21 9
  let e34 : LowMeanIntegerExpr := .mul (101000000000000000, 77533716096405212823) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-101000000000000000, 77533716096405212823) e34
  let e36 : LowMeanIntegerExpr := .add (1082430176889519647857741747, 12405394575424834051680000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (1082554230835273896198258547, 12405394575424834051680000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-1082430176889519647857741747, 12405394575424834051680000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0269 : LowMeanDirectSeedInput :=
  { record := 269, positions := [{ j := 3, mode := 0, left := 623, right := 0 }], target := { R := 9, expr := lowMeanSeedTargetExpr0269 } }

noncomputable def lowMeanSeedTargetExpr0270 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (867, 15625)
  let e2 : LowMeanIntegerExpr := .atom (771, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (10, 1)
  let e4 : LowMeanIntegerExpr := .atom (45, 4)
  let e5 : LowMeanIntegerExpr := .neg (-45, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-5, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-771, 800000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (218097, 4000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (8851, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (25, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (8851, 6400000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-8851, 6400000) e11
  let e13 : LowMeanIntegerExpr := .add (1700521, 32000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (437, 25000)
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
  let e29 : LowMeanIntegerExpr := .mul (2033, 465750) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (2033, 46575) e29 e3
  let e31 : LowMeanIntegerExpr := .add (5770310623, 59616000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (909, 1000)
  let e33 : LowMeanIntegerExpr := .pow (100000000000000000000, 144445313087602911489249) e21 10
  let e34 : LowMeanIntegerExpr := .mul (10100000000000000000, 16049479231955879054361) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-10100000000000000000, 16049479231955879054361) e34
  let e36 : LowMeanIntegerExpr := .add (49387202847972565740570302081, 513583335422588129739552000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (49392338681326791621867697601, 513583335422588129739552000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-49387202847972565740570302081, 513583335422588129739552000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0270 : LowMeanDirectSeedInput :=
  { record := 270, positions := [{ j := 7, mode := 0, left := 624, right := 0 }], target := { R := 10, expr := lowMeanSeedTargetExpr0270 } }

noncomputable def lowMeanSeedTargetExpr0271 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (867, 15625)
  let e2 : LowMeanIntegerExpr := .atom (771, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (11, 1)
  let e4 : LowMeanIntegerExpr := .atom (45, 4)
  let e5 : LowMeanIntegerExpr := .neg (-45, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-1, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-771, 4000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (221181, 4000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (8851, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (1, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (8851, 160000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-8851, 160000000) e11
  let e13 : LowMeanIntegerExpr := .add (8838389, 160000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (437, 25000)
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
  let e29 : LowMeanIntegerExpr := .mul (2033, 465750) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (22363, 465750) e29 e3
  let e31 : LowMeanIntegerExpr := .add (30778238707, 298080000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (909, 1000)
  let e33 : LowMeanIntegerExpr := .pow (10000000000000000000000, 29900179809133802678274543) e21 11
  let e34 : LowMeanIntegerExpr := .mul (1010000000000000000000, 3322242201014866964252727) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1010000000000000000000, 3322242201014866964252727) e34
  let e36 : LowMeanIntegerExpr := .add (54724478102686340891904920816803, 531558752162378714280436320000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (54729793690207964679047725180003, 531558752162378714280436320000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-54724478102686340891904920816803, 531558752162378714280436320000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0271 : LowMeanDirectSeedInput :=
  { record := 271, positions := [], target := { R := 11, expr := lowMeanSeedTargetExpr0271 } }

noncomputable def lowMeanSeedGroup0256 : List LowMeanDirectSeedInput := [lowMeanSeedRecord0256, lowMeanSeedRecord0257, lowMeanSeedRecord0258, lowMeanSeedRecord0259, lowMeanSeedRecord0260, lowMeanSeedRecord0261, lowMeanSeedRecord0262, lowMeanSeedRecord0263, lowMeanSeedRecord0264, lowMeanSeedRecord0265, lowMeanSeedRecord0266, lowMeanSeedRecord0267, lowMeanSeedRecord0268, lowMeanSeedRecord0269, lowMeanSeedRecord0270, lowMeanSeedRecord0271]

end Erdos993Lean.Analytic.V213
