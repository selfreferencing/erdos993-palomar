module

public import Erdos993Lean.Analytic.V213.LowMeanCoreAll
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0559
public import Erdos993Lean.Analytic.V213.LowMeanFiberSeed
public import Erdos993Lean.Analytic.V213.LowMeanIntegerExpr
public import Erdos993Lean.Analytic.V213.LowMeanSeedGeometry
public import Erdos993Lean.Analytic.V213.LowMeanWidthData
public import Erdos993Lean.Ceiling.Prefix
public import Erdos993Lean.Ceiling.Statement

/-! Exact core/budget keys and equation-51 targets for the direct fibers. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanSeedTargetExpr0000 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (9807, 125000)
  let e2 : LowMeanIntegerExpr := .atom (4183, 5000000)
  let e3 : LowMeanIntegerExpr := .atom (0, 1)
  let e4 : LowMeanIntegerExpr := .atom (121, 4)
  let e5 : LowMeanIntegerExpr := .neg (-121, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-121, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-506143, 20000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (1062977, 20000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (327, 6250000)
  let e10 : LowMeanIntegerExpr := .pow (14641, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (4787607, 100000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-4787607, 100000000) e11
  let e13 : LowMeanIntegerExpr := .add (263639, 50000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (5511, 1000000)
  let e15 : LowMeanIntegerExpr := .atom (1, 4)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (3, 8)
  let e18 : LowMeanIntegerExpr := .atom (1, 1)
  let e19 : LowMeanIntegerExpr := .neg (-1, 4) e15
  let e20 : LowMeanIntegerExpr := .add (3, 4) e18 e19
  let e21 : LowMeanIntegerExpr := .mul (3, 16) e15 e20
  let e22 : LowMeanIntegerExpr := .neg (-3, 8) e17
  let e23 : LowMeanIntegerExpr := .add (5, 8) e18 e22
  let e24 : LowMeanIntegerExpr := .mul (15, 64) e17 e23
  let e25 : LowMeanIntegerExpr := .maximum (15, 64) e21 e24
  let e26 : LowMeanIntegerExpr := .selectLE (15, 64) e16 e17 e15 e25
  let e27 : LowMeanIntegerExpr := .selectLE (15, 64) e15 e16 e26 e25
  let e28 : LowMeanIntegerExpr := .mul (16533, 12800000) e14 e27
  let e29 : LowMeanIntegerExpr := .mul (0, 1) e28 e3
  let e30 : LowMeanIntegerExpr := .add (263639, 50000000) e13 e29
  let e31 : LowMeanIntegerExpr := .atom (2461, 2500)
  let e32 : LowMeanIntegerExpr := .pow (1, 1) e20 0
  let e33 : LowMeanIntegerExpr := .mul (2461, 2500) e31 e32
  let e34 : LowMeanIntegerExpr := .neg (-2461, 2500) e33
  let e35 : LowMeanIntegerExpr := .add (-48956361, 50000000) e30 e34
  let e36 : LowMeanIntegerExpr := .add (-48955861, 50000000) e0 e35
  let e37 : LowMeanIntegerExpr := .neg (48956361, 50000000) e35
  let e38 : LowMeanIntegerExpr := .add (1, 100000) e36 e37
  e38

noncomputable def lowMeanSeedRecord0000 : LowMeanDirectSeedInput :=
  { record := 0, positions := [], target := { R := 0, expr := lowMeanSeedTargetExpr0000 } }

noncomputable def lowMeanSeedTargetExpr0001 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (9807, 125000)
  let e2 : LowMeanIntegerExpr := .atom (4183, 5000000)
  let e3 : LowMeanIntegerExpr := .atom (1, 1)
  let e4 : LowMeanIntegerExpr := .atom (121, 4)
  let e5 : LowMeanIntegerExpr := .neg (-121, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-117, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-489411, 20000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (1079709, 20000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (327, 6250000)
  let e10 : LowMeanIntegerExpr := .pow (13689, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (4476303, 100000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-4476303, 100000000) e11
  let e13 : LowMeanIntegerExpr := .add (461121, 50000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (5511, 1000000)
  let e15 : LowMeanIntegerExpr := .atom (1, 4)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (3, 8)
  let e18 : LowMeanIntegerExpr := .neg (-1, 4) e15
  let e19 : LowMeanIntegerExpr := .add (3, 4) e3 e18
  let e20 : LowMeanIntegerExpr := .mul (3, 16) e15 e19
  let e21 : LowMeanIntegerExpr := .neg (-3, 8) e17
  let e22 : LowMeanIntegerExpr := .add (5, 8) e3 e21
  let e23 : LowMeanIntegerExpr := .mul (15, 64) e17 e22
  let e24 : LowMeanIntegerExpr := .maximum (15, 64) e20 e23
  let e25 : LowMeanIntegerExpr := .selectLE (15, 64) e16 e17 e15 e24
  let e26 : LowMeanIntegerExpr := .selectLE (15, 64) e15 e16 e25 e24
  let e27 : LowMeanIntegerExpr := .mul (16533, 12800000) e14 e26
  let e28 : LowMeanIntegerExpr := .mul (16533, 12800000) e27 e3
  let e29 : LowMeanIntegerExpr := .add (16822497, 1600000000) e13 e28
  let e30 : LowMeanIntegerExpr := .atom (2461, 2500)
  let e31 : LowMeanIntegerExpr := .pow (3, 4) e19 1
  let e32 : LowMeanIntegerExpr := .mul (7383, 10000) e30 e31
  let e33 : LowMeanIntegerExpr := .neg (-7383, 10000) e32
  let e34 : LowMeanIntegerExpr := .add (-1164457503, 1600000000) e29 e33
  let e35 : LowMeanIntegerExpr := .add (-1164441503, 1600000000) e0 e34
  let e36 : LowMeanIntegerExpr := .neg (1164457503, 1600000000) e34
  let e37 : LowMeanIntegerExpr := .add (1, 100000) e35 e36
  e37

noncomputable def lowMeanSeedRecord0001 : LowMeanDirectSeedInput :=
  { record := 1, positions := [], target := { R := 1, expr := lowMeanSeedTargetExpr0001 } }

noncomputable def lowMeanSeedTargetExpr0002 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (9807, 125000)
  let e2 : LowMeanIntegerExpr := .atom (4183, 5000000)
  let e3 : LowMeanIntegerExpr := .atom (2, 1)
  let e4 : LowMeanIntegerExpr := .atom (121, 4)
  let e5 : LowMeanIntegerExpr := .neg (-121, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-113, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-472679, 20000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (1096441, 20000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (327, 6250000)
  let e10 : LowMeanIntegerExpr := .pow (12769, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (4175463, 100000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-4175463, 100000000) e11
  let e13 : LowMeanIntegerExpr := .add (653371, 50000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (5511, 1000000)
  let e15 : LowMeanIntegerExpr := .atom (1, 4)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (3, 8)
  let e18 : LowMeanIntegerExpr := .atom (1, 1)
  let e19 : LowMeanIntegerExpr := .neg (-1, 4) e15
  let e20 : LowMeanIntegerExpr := .add (3, 4) e18 e19
  let e21 : LowMeanIntegerExpr := .mul (3, 16) e15 e20
  let e22 : LowMeanIntegerExpr := .neg (-3, 8) e17
  let e23 : LowMeanIntegerExpr := .add (5, 8) e18 e22
  let e24 : LowMeanIntegerExpr := .mul (15, 64) e17 e23
  let e25 : LowMeanIntegerExpr := .maximum (15, 64) e21 e24
  let e26 : LowMeanIntegerExpr := .selectLE (15, 64) e16 e17 e15 e25
  let e27 : LowMeanIntegerExpr := .selectLE (15, 64) e15 e16 e26 e25
  let e28 : LowMeanIntegerExpr := .mul (16533, 12800000) e14 e27
  let e29 : LowMeanIntegerExpr := .mul (16533, 6400000) e28 e3
  let e30 : LowMeanIntegerExpr := .add (12520561, 800000000) e13 e29
  let e31 : LowMeanIntegerExpr := .atom (2461, 2500)
  let e32 : LowMeanIntegerExpr := .pow (9, 16) e20 2
  let e33 : LowMeanIntegerExpr := .mul (22149, 40000) e31 e32
  let e34 : LowMeanIntegerExpr := .neg (-22149, 40000) e33
  let e35 : LowMeanIntegerExpr := .add (-430459439, 800000000) e30 e34
  let e36 : LowMeanIntegerExpr := .add (-430451439, 800000000) e0 e35
  let e37 : LowMeanIntegerExpr := .neg (430459439, 800000000) e35
  let e38 : LowMeanIntegerExpr := .add (1, 100000) e36 e37
  e38

noncomputable def lowMeanSeedRecord0002 : LowMeanDirectSeedInput :=
  { record := 2, positions := [], target := { R := 2, expr := lowMeanSeedTargetExpr0002 } }

noncomputable def lowMeanSeedTargetExpr0003 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (9807, 125000)
  let e2 : LowMeanIntegerExpr := .atom (4183, 5000000)
  let e3 : LowMeanIntegerExpr := .atom (3, 1)
  let e4 : LowMeanIntegerExpr := .atom (121, 4)
  let e5 : LowMeanIntegerExpr := .neg (-121, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-109, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-455947, 20000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (1113173, 20000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (327, 6250000)
  let e10 : LowMeanIntegerExpr := .pow (11881, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (3885087, 100000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-3885087, 100000000) e11
  let e13 : LowMeanIntegerExpr := .add (840389, 50000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (5511, 1000000)
  let e15 : LowMeanIntegerExpr := .atom (1, 4)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (3, 8)
  let e18 : LowMeanIntegerExpr := .atom (1, 1)
  let e19 : LowMeanIntegerExpr := .neg (-1, 4) e15
  let e20 : LowMeanIntegerExpr := .add (3, 4) e18 e19
  let e21 : LowMeanIntegerExpr := .mul (3, 16) e15 e20
  let e22 : LowMeanIntegerExpr := .neg (-3, 8) e17
  let e23 : LowMeanIntegerExpr := .add (5, 8) e18 e22
  let e24 : LowMeanIntegerExpr := .mul (15, 64) e17 e23
  let e25 : LowMeanIntegerExpr := .maximum (15, 64) e21 e24
  let e26 : LowMeanIntegerExpr := .selectLE (15, 64) e16 e17 e15 e25
  let e27 : LowMeanIntegerExpr := .selectLE (15, 64) e15 e16 e26 e25
  let e28 : LowMeanIntegerExpr := .mul (16533, 12800000) e14 e27
  let e29 : LowMeanIntegerExpr := .mul (49599, 12800000) e28 e3
  let e30 : LowMeanIntegerExpr := .add (33092323, 1600000000) e13 e29
  let e31 : LowMeanIntegerExpr := .atom (2461, 2500)
  let e32 : LowMeanIntegerExpr := .pow (27, 64) e20 3
  let e33 : LowMeanIntegerExpr := .mul (66447, 160000) e31 e32
  let e34 : LowMeanIntegerExpr := .neg (-66447, 160000) e33
  let e35 : LowMeanIntegerExpr := .add (-631377677, 1600000000) e30 e34
  let e36 : LowMeanIntegerExpr := .add (-631361677, 1600000000) e0 e35
  let e37 : LowMeanIntegerExpr := .neg (631377677, 1600000000) e35
  let e38 : LowMeanIntegerExpr := .add (1, 100000) e36 e37
  e38

noncomputable def lowMeanSeedRecord0003 : LowMeanDirectSeedInput :=
  { record := 3, positions := [], target := { R := 3, expr := lowMeanSeedTargetExpr0003 } }

noncomputable def lowMeanSeedTargetExpr0004 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (9807, 125000)
  let e2 : LowMeanIntegerExpr := .atom (4183, 5000000)
  let e3 : LowMeanIntegerExpr := .atom (4, 1)
  let e4 : LowMeanIntegerExpr := .atom (121, 4)
  let e5 : LowMeanIntegerExpr := .neg (-121, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-105, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-87843, 4000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (225981, 4000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (327, 6250000)
  let e10 : LowMeanIntegerExpr := .pow (11025, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (144207, 4000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-144207, 4000000) e11
  let e13 : LowMeanIntegerExpr := .add (40887, 2000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (5511, 1000000)
  let e15 : LowMeanIntegerExpr := .atom (1, 4)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (3, 8)
  let e18 : LowMeanIntegerExpr := .atom (1, 1)
  let e19 : LowMeanIntegerExpr := .neg (-1, 4) e15
  let e20 : LowMeanIntegerExpr := .add (3, 4) e18 e19
  let e21 : LowMeanIntegerExpr := .mul (3, 16) e15 e20
  let e22 : LowMeanIntegerExpr := .neg (-3, 8) e17
  let e23 : LowMeanIntegerExpr := .add (5, 8) e18 e22
  let e24 : LowMeanIntegerExpr := .mul (15, 64) e17 e23
  let e25 : LowMeanIntegerExpr := .maximum (15, 64) e21 e24
  let e26 : LowMeanIntegerExpr := .selectLE (15, 64) e16 e17 e15 e25
  let e27 : LowMeanIntegerExpr := .selectLE (15, 64) e15 e16 e26 e25
  let e28 : LowMeanIntegerExpr := .mul (16533, 12800000) e14 e27
  let e29 : LowMeanIntegerExpr := .mul (16533, 3200000) e28 e3
  let e30 : LowMeanIntegerExpr := .add (409761, 16000000) e13 e29
  let e31 : LowMeanIntegerExpr := .atom (2461, 2500)
  let e32 : LowMeanIntegerExpr := .pow (81, 256) e20 4
  let e33 : LowMeanIntegerExpr := .mul (199341, 640000) e31 e32
  let e34 : LowMeanIntegerExpr := .neg (-199341, 640000) e33
  let e35 : LowMeanIntegerExpr := .add (-1143441, 4000000) e30 e34
  let e36 : LowMeanIntegerExpr := .add (-1143401, 4000000) e0 e35
  let e37 : LowMeanIntegerExpr := .neg (1143441, 4000000) e35
  let e38 : LowMeanIntegerExpr := .add (1, 100000) e36 e37
  e38

noncomputable def lowMeanSeedRecord0004 : LowMeanDirectSeedInput :=
  { record := 4, positions := [], target := { R := 4, expr := lowMeanSeedTargetExpr0004 } }

noncomputable def lowMeanSeedTargetExpr0005 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (9807, 125000)
  let e2 : LowMeanIntegerExpr := .atom (4183, 5000000)
  let e3 : LowMeanIntegerExpr := .atom (5, 1)
  let e4 : LowMeanIntegerExpr := .atom (121, 4)
  let e5 : LowMeanIntegerExpr := .neg (-121, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-101, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-422483, 20000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (1146637, 20000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (327, 6250000)
  let e10 : LowMeanIntegerExpr := .pow (10201, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (3335727, 100000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-3335727, 100000000) e11
  let e13 : LowMeanIntegerExpr := .add (1198729, 50000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (5511, 1000000)
  let e15 : LowMeanIntegerExpr := .atom (1, 4)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (3, 8)
  let e18 : LowMeanIntegerExpr := .atom (1, 1)
  let e19 : LowMeanIntegerExpr := .neg (-1, 4) e15
  let e20 : LowMeanIntegerExpr := .add (3, 4) e18 e19
  let e21 : LowMeanIntegerExpr := .mul (3, 16) e15 e20
  let e22 : LowMeanIntegerExpr := .neg (-3, 8) e17
  let e23 : LowMeanIntegerExpr := .add (5, 8) e18 e22
  let e24 : LowMeanIntegerExpr := .mul (15, 64) e17 e23
  let e25 : LowMeanIntegerExpr := .maximum (15, 64) e21 e24
  let e26 : LowMeanIntegerExpr := .selectLE (15, 64) e16 e17 e15 e25
  let e27 : LowMeanIntegerExpr := .selectLE (15, 64) e15 e16 e26 e25
  let e28 : LowMeanIntegerExpr := .mul (16533, 12800000) e14 e27
  let e29 : LowMeanIntegerExpr := .mul (16533, 2560000) e28 e3
  let e30 : LowMeanIntegerExpr := .add (48692453, 1600000000) e13 e29
  let e31 : LowMeanIntegerExpr := .atom (2461, 2500)
  let e32 : LowMeanIntegerExpr := .pow (243, 1024) e20 5
  let e33 : LowMeanIntegerExpr := .mul (598023, 2560000) e31 e32
  let e34 : LowMeanIntegerExpr := .neg (-598023, 2560000) e33
  let e35 : LowMeanIntegerExpr := .add (-162535961, 800000000) e30 e34
  let e36 : LowMeanIntegerExpr := .add (-162527961, 800000000) e0 e35
  let e37 : LowMeanIntegerExpr := .neg (162535961, 800000000) e35
  let e38 : LowMeanIntegerExpr := .add (1, 100000) e36 e37
  e38

noncomputable def lowMeanSeedRecord0005 : LowMeanDirectSeedInput :=
  { record := 5, positions := [], target := { R := 5, expr := lowMeanSeedTargetExpr0005 } }

noncomputable def lowMeanSeedTargetExpr0006 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (9807, 125000)
  let e2 : LowMeanIntegerExpr := .atom (4183, 5000000)
  let e3 : LowMeanIntegerExpr := .atom (6, 1)
  let e4 : LowMeanIntegerExpr := .atom (121, 4)
  let e5 : LowMeanIntegerExpr := .neg (-121, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-97, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-405751, 20000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (1163369, 20000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (327, 6250000)
  let e10 : LowMeanIntegerExpr := .pow (9409, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (3076743, 100000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-3076743, 100000000) e11
  let e13 : LowMeanIntegerExpr := .add (1370051, 50000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (5511, 1000000)
  let e15 : LowMeanIntegerExpr := .atom (1, 4)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (3, 8)
  let e18 : LowMeanIntegerExpr := .atom (1, 1)
  let e19 : LowMeanIntegerExpr := .neg (-1, 4) e15
  let e20 : LowMeanIntegerExpr := .add (3, 4) e18 e19
  let e21 : LowMeanIntegerExpr := .mul (3, 16) e15 e20
  let e22 : LowMeanIntegerExpr := .neg (-3, 8) e17
  let e23 : LowMeanIntegerExpr := .add (5, 8) e18 e22
  let e24 : LowMeanIntegerExpr := .mul (15, 64) e17 e23
  let e25 : LowMeanIntegerExpr := .maximum (15, 64) e21 e24
  let e26 : LowMeanIntegerExpr := .selectLE (15, 64) e16 e17 e15 e25
  let e27 : LowMeanIntegerExpr := .selectLE (15, 64) e15 e16 e26 e25
  let e28 : LowMeanIntegerExpr := .mul (16533, 12800000) e14 e27
  let e29 : LowMeanIntegerExpr := .mul (49599, 6400000) e28 e3
  let e30 : LowMeanIntegerExpr := .add (28120691, 800000000) e13 e29
  let e31 : LowMeanIntegerExpr := .atom (2461, 2500)
  let e32 : LowMeanIntegerExpr := .pow (729, 4096) e20 6
  let e33 : LowMeanIntegerExpr := .mul (1794069, 10240000) e31 e32
  let e34 : LowMeanIntegerExpr := .neg (-1794069, 10240000) e33
  let e35 : LowMeanIntegerExpr := .add (-896327597, 6400000000) e30 e34
  let e36 : LowMeanIntegerExpr := .add (-896263597, 6400000000) e0 e35
  let e37 : LowMeanIntegerExpr := .neg (896327597, 6400000000) e35
  let e38 : LowMeanIntegerExpr := .add (1, 100000) e36 e37
  e38

noncomputable def lowMeanSeedRecord0006 : LowMeanDirectSeedInput :=
  { record := 6, positions := [], target := { R := 6, expr := lowMeanSeedTargetExpr0006 } }

noncomputable def lowMeanSeedTargetExpr0007 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (9807, 125000)
  let e2 : LowMeanIntegerExpr := .atom (4183, 5000000)
  let e3 : LowMeanIntegerExpr := .atom (7, 1)
  let e4 : LowMeanIntegerExpr := .atom (121, 4)
  let e5 : LowMeanIntegerExpr := .neg (-121, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-93, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-389019, 20000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (1180101, 20000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (327, 6250000)
  let e10 : LowMeanIntegerExpr := .pow (8649, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (2828223, 100000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-2828223, 100000000) e11
  let e13 : LowMeanIntegerExpr := .add (1536141, 50000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (5511, 1000000)
  let e15 : LowMeanIntegerExpr := .atom (1, 4)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (3, 8)
  let e18 : LowMeanIntegerExpr := .atom (1, 1)
  let e19 : LowMeanIntegerExpr := .neg (-1, 4) e15
  let e20 : LowMeanIntegerExpr := .add (3, 4) e18 e19
  let e21 : LowMeanIntegerExpr := .mul (3, 16) e15 e20
  let e22 : LowMeanIntegerExpr := .neg (-3, 8) e17
  let e23 : LowMeanIntegerExpr := .add (5, 8) e18 e22
  let e24 : LowMeanIntegerExpr := .mul (15, 64) e17 e23
  let e25 : LowMeanIntegerExpr := .maximum (15, 64) e21 e24
  let e26 : LowMeanIntegerExpr := .selectLE (15, 64) e16 e17 e15 e25
  let e27 : LowMeanIntegerExpr := .selectLE (15, 64) e15 e16 e26 e25
  let e28 : LowMeanIntegerExpr := .mul (16533, 12800000) e14 e27
  let e29 : LowMeanIntegerExpr := .mul (115731, 12800000) e28 e3
  let e30 : LowMeanIntegerExpr := .add (63622887, 1600000000) e13 e29
  let e31 : LowMeanIntegerExpr := .atom (2461, 2500)
  let e32 : LowMeanIntegerExpr := .pow (2187, 16384) e20 7
  let e33 : LowMeanIntegerExpr := .mul (5382207, 40960000) e31 e32
  let e34 : LowMeanIntegerExpr := .neg (-5382207, 40960000) e33
  let e35 : LowMeanIntegerExpr := .add (-2345913183, 25600000000) e30 e34
  let e36 : LowMeanIntegerExpr := .add (-2345657183, 25600000000) e0 e35
  let e37 : LowMeanIntegerExpr := .neg (2345913183, 25600000000) e35
  let e38 : LowMeanIntegerExpr := .add (1, 100000) e36 e37
  e38

noncomputable def lowMeanSeedRecord0007 : LowMeanDirectSeedInput :=
  { record := 7, positions := [], target := { R := 7, expr := lowMeanSeedTargetExpr0007 } }

noncomputable def lowMeanSeedTargetExpr0008 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (9807, 125000)
  let e2 : LowMeanIntegerExpr := .atom (4183, 5000000)
  let e3 : LowMeanIntegerExpr := .atom (8, 1)
  let e4 : LowMeanIntegerExpr := .atom (121, 4)
  let e5 : LowMeanIntegerExpr := .neg (-121, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-89, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-372287, 20000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (1196833, 20000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (327, 6250000)
  let e10 : LowMeanIntegerExpr := .pow (7921, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (2590167, 100000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-2590167, 100000000) e11
  let e13 : LowMeanIntegerExpr := .add (1696999, 50000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (5511, 1000000)
  let e15 : LowMeanIntegerExpr := .atom (1, 4)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (3, 8)
  let e18 : LowMeanIntegerExpr := .atom (1, 1)
  let e19 : LowMeanIntegerExpr := .neg (-1, 4) e15
  let e20 : LowMeanIntegerExpr := .add (3, 4) e18 e19
  let e21 : LowMeanIntegerExpr := .mul (3, 16) e15 e20
  let e22 : LowMeanIntegerExpr := .neg (-3, 8) e17
  let e23 : LowMeanIntegerExpr := .add (5, 8) e18 e22
  let e24 : LowMeanIntegerExpr := .mul (15, 64) e17 e23
  let e25 : LowMeanIntegerExpr := .maximum (15, 64) e21 e24
  let e26 : LowMeanIntegerExpr := .selectLE (15, 64) e16 e17 e15 e25
  let e27 : LowMeanIntegerExpr := .selectLE (15, 64) e15 e16 e26 e25
  let e28 : LowMeanIntegerExpr := .mul (16533, 12800000) e14 e27
  let e29 : LowMeanIntegerExpr := .mul (16533, 1600000) e28 e3
  let e30 : LowMeanIntegerExpr := .add (8854621, 200000000) e13 e29
  let e31 : LowMeanIntegerExpr := .atom (2461, 2500)
  let e32 : LowMeanIntegerExpr := .pow (6561, 65536) e20 8
  let e33 : LowMeanIntegerExpr := .mul (16146621, 163840000) e31 e32
  let e34 : LowMeanIntegerExpr := .neg (-16146621, 163840000) e33
  let e35 : LowMeanIntegerExpr := .add (-5558072173, 102400000000) e30 e34
  let e36 : LowMeanIntegerExpr := .add (-5557048173, 102400000000) e0 e35
  let e37 : LowMeanIntegerExpr := .neg (5558072173, 102400000000) e35
  let e38 : LowMeanIntegerExpr := .add (1, 100000) e36 e37
  e38

noncomputable def lowMeanSeedRecord0008 : LowMeanDirectSeedInput :=
  { record := 8, positions := [{ j := -1, mode := 0, left := 0, right := 0 }, { j := 5, mode := 0, left := 1, right := 0 }], target := { R := 8, expr := lowMeanSeedTargetExpr0008 } }

noncomputable def lowMeanSeedTargetExpr0009 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (9807, 125000)
  let e2 : LowMeanIntegerExpr := .atom (4183, 5000000)
  let e3 : LowMeanIntegerExpr := .atom (9, 1)
  let e4 : LowMeanIntegerExpr := .atom (121, 4)
  let e5 : LowMeanIntegerExpr := .neg (-121, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-85, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-71111, 4000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (242713, 4000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (327, 6250000)
  let e10 : LowMeanIntegerExpr := .pow (7225, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (94503, 4000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-94503, 4000000) e11
  let e13 : LowMeanIntegerExpr := .add (14821, 400000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (5511, 1000000)
  let e15 : LowMeanIntegerExpr := .atom (1, 4)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (3, 8)
  let e18 : LowMeanIntegerExpr := .atom (1, 1)
  let e19 : LowMeanIntegerExpr := .neg (-1, 4) e15
  let e20 : LowMeanIntegerExpr := .add (3, 4) e18 e19
  let e21 : LowMeanIntegerExpr := .mul (3, 16) e15 e20
  let e22 : LowMeanIntegerExpr := .neg (-3, 8) e17
  let e23 : LowMeanIntegerExpr := .add (5, 8) e18 e22
  let e24 : LowMeanIntegerExpr := .mul (15, 64) e17 e23
  let e25 : LowMeanIntegerExpr := .maximum (15, 64) e21 e24
  let e26 : LowMeanIntegerExpr := .selectLE (15, 64) e16 e17 e15 e25
  let e27 : LowMeanIntegerExpr := .selectLE (15, 64) e15 e16 e26 e25
  let e28 : LowMeanIntegerExpr := .mul (16533, 12800000) e14 e27
  let e29 : LowMeanIntegerExpr := .mul (148797, 12800000) e28 e3
  let e30 : LowMeanIntegerExpr := .add (623069, 12800000) e13 e29
  let e31 : LowMeanIntegerExpr := .atom (2461, 2500)
  let e32 : LowMeanIntegerExpr := .pow (19683, 262144) e20 9
  let e33 : LowMeanIntegerExpr := .mul (48439863, 655360000) e31 e32
  let e34 : LowMeanIntegerExpr := .neg (-48439863, 655360000) e33
  let e35 : LowMeanIntegerExpr := .add (-82693651, 3276800000) e30 e34
  let e36 : LowMeanIntegerExpr := .add (-82660883, 3276800000) e0 e35
  let e37 : LowMeanIntegerExpr := .neg (82693651, 3276800000) e35
  let e38 : LowMeanIntegerExpr := .add (1, 100000) e36 e37
  e38

noncomputable def lowMeanSeedRecord0009 : LowMeanDirectSeedInput :=
  { record := 9, positions := [{ j := -1, mode := 0, left := 2, right := 0 }, { j := 0, mode := 0, left := 3, right := 0 }], target := { R := 9, expr := lowMeanSeedTargetExpr0009 } }

noncomputable def lowMeanSeedTargetExpr0010 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (9807, 125000)
  let e2 : LowMeanIntegerExpr := .atom (4183, 5000000)
  let e3 : LowMeanIntegerExpr := .atom (10, 1)
  let e4 : LowMeanIntegerExpr := .atom (121, 4)
  let e5 : LowMeanIntegerExpr := .neg (-121, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-81, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-338823, 20000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (1230297, 20000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (327, 6250000)
  let e10 : LowMeanIntegerExpr := .pow (6561, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (2145447, 100000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-2145447, 100000000) e11
  let e13 : LowMeanIntegerExpr := .add (2003019, 50000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (5511, 1000000)
  let e15 : LowMeanIntegerExpr := .atom (1, 4)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (3, 8)
  let e18 : LowMeanIntegerExpr := .atom (1, 1)
  let e19 : LowMeanIntegerExpr := .neg (-1, 4) e15
  let e20 : LowMeanIntegerExpr := .add (3, 4) e18 e19
  let e21 : LowMeanIntegerExpr := .mul (3, 16) e15 e20
  let e22 : LowMeanIntegerExpr := .neg (-3, 8) e17
  let e23 : LowMeanIntegerExpr := .add (5, 8) e18 e22
  let e24 : LowMeanIntegerExpr := .mul (15, 64) e17 e23
  let e25 : LowMeanIntegerExpr := .maximum (15, 64) e21 e24
  let e26 : LowMeanIntegerExpr := .selectLE (15, 64) e16 e17 e15 e25
  let e27 : LowMeanIntegerExpr := .selectLE (15, 64) e15 e16 e26 e25
  let e28 : LowMeanIntegerExpr := .mul (16533, 12800000) e14 e27
  let e29 : LowMeanIntegerExpr := .mul (16533, 1280000) e28 e3
  let e30 : LowMeanIntegerExpr := .add (42381429, 800000000) e13 e29
  let e31 : LowMeanIntegerExpr := .atom (2461, 2500)
  let e32 : LowMeanIntegerExpr := .pow (59049, 1048576) e20 10
  let e33 : LowMeanIntegerExpr := .mul (145319589, 2621440000) e31 e32
  let e34 : LowMeanIntegerExpr := .neg (-145319589, 2621440000) e33
  let e35 : LowMeanIntegerExpr := .add (-4027576533, 1638400000000) e30 e34
  let e36 : LowMeanIntegerExpr := .add (-4011192533, 1638400000000) e0 e35
  let e37 : LowMeanIntegerExpr := .neg (4027576533, 1638400000000) e35
  let e38 : LowMeanIntegerExpr := .add (1, 100000) e36 e37
  e38

noncomputable def lowMeanSeedRecord0010 : LowMeanDirectSeedInput :=
  { record := 10, positions := [{ j := -1, mode := 0, left := 4, right := 0 }, { j := 0, mode := 0, left := 5, right := 0 }, { j := 6, mode := 0, left := 6, right := 0 }], target := { R := 10, expr := lowMeanSeedTargetExpr0010 } }

noncomputable def lowMeanSeedTargetExpr0011 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (9807, 125000)
  let e2 : LowMeanIntegerExpr := .atom (4183, 5000000)
  let e3 : LowMeanIntegerExpr := .atom (11, 1)
  let e4 : LowMeanIntegerExpr := .atom (121, 4)
  let e5 : LowMeanIntegerExpr := .neg (-121, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-77, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-322091, 20000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (1247029, 20000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (327, 6250000)
  let e10 : LowMeanIntegerExpr := .pow (5929, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1938783, 100000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1938783, 100000000) e11
  let e13 : LowMeanIntegerExpr := .add (2148181, 50000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (5511, 1000000)
  let e15 : LowMeanIntegerExpr := .atom (1, 4)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (3, 8)
  let e18 : LowMeanIntegerExpr := .atom (1, 1)
  let e19 : LowMeanIntegerExpr := .neg (-1, 4) e15
  let e20 : LowMeanIntegerExpr := .add (3, 4) e18 e19
  let e21 : LowMeanIntegerExpr := .mul (3, 16) e15 e20
  let e22 : LowMeanIntegerExpr := .neg (-3, 8) e17
  let e23 : LowMeanIntegerExpr := .add (5, 8) e18 e22
  let e24 : LowMeanIntegerExpr := .mul (15, 64) e17 e23
  let e25 : LowMeanIntegerExpr := .maximum (15, 64) e21 e24
  let e26 : LowMeanIntegerExpr := .selectLE (15, 64) e16 e17 e15 e25
  let e27 : LowMeanIntegerExpr := .selectLE (15, 64) e15 e16 e26 e25
  let e28 : LowMeanIntegerExpr := .mul (16533, 12800000) e14 e27
  let e29 : LowMeanIntegerExpr := .mul (181863, 12800000) e28 e3
  let e30 : LowMeanIntegerExpr := .add (91474667, 1600000000) e13 e29
  let e31 : LowMeanIntegerExpr := .atom (2461, 2500)
  let e32 : LowMeanIntegerExpr := .pow (177147, 4194304) e20 11
  let e33 : LowMeanIntegerExpr := .mul (435958767, 10485760000) e31 e32
  let e34 : LowMeanIntegerExpr := .neg (-435958767, 10485760000) e33
  let e35 : LowMeanIntegerExpr := .add (102206006657, 6553600000000) e30 e34
  let e36 : LowMeanIntegerExpr := .add (102271542657, 6553600000000) e0 e35
  let e37 : LowMeanIntegerExpr := .neg (-102206006657, 6553600000000) e35
  let e38 : LowMeanIntegerExpr := .add (1, 100000) e36 e37
  e38

noncomputable def lowMeanSeedRecord0011 : LowMeanDirectSeedInput :=
  { record := 11, positions := [{ j := -1, mode := 0, left := 7, right := 0 }, { j := 0, mode := 0, left := 8, right := 0 }], target := { R := 11, expr := lowMeanSeedTargetExpr0011 } }

noncomputable def lowMeanSeedTargetExpr0012 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (9807, 125000)
  let e2 : LowMeanIntegerExpr := .atom (4183, 5000000)
  let e3 : LowMeanIntegerExpr := .atom (12, 1)
  let e4 : LowMeanIntegerExpr := .atom (121, 4)
  let e5 : LowMeanIntegerExpr := .neg (-121, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-73, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-305359, 20000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (1263761, 20000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (327, 6250000)
  let e10 : LowMeanIntegerExpr := .pow (5329, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1742583, 100000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1742583, 100000000) e11
  let e13 : LowMeanIntegerExpr := .add (2288111, 50000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (5511, 1000000)
  let e15 : LowMeanIntegerExpr := .atom (1, 4)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (3, 8)
  let e18 : LowMeanIntegerExpr := .atom (1, 1)
  let e19 : LowMeanIntegerExpr := .neg (-1, 4) e15
  let e20 : LowMeanIntegerExpr := .add (3, 4) e18 e19
  let e21 : LowMeanIntegerExpr := .mul (3, 16) e15 e20
  let e22 : LowMeanIntegerExpr := .neg (-3, 8) e17
  let e23 : LowMeanIntegerExpr := .add (5, 8) e18 e22
  let e24 : LowMeanIntegerExpr := .mul (15, 64) e17 e23
  let e25 : LowMeanIntegerExpr := .maximum (15, 64) e21 e24
  let e26 : LowMeanIntegerExpr := .selectLE (15, 64) e16 e17 e15 e25
  let e27 : LowMeanIntegerExpr := .selectLE (15, 64) e15 e16 e26 e25
  let e28 : LowMeanIntegerExpr := .mul (16533, 12800000) e14 e27
  let e29 : LowMeanIntegerExpr := .mul (49599, 3200000) e28 e3
  let e30 : LowMeanIntegerExpr := .add (24504763, 400000000) e13 e29
  let e31 : LowMeanIntegerExpr := .atom (2461, 2500)
  let e32 : LowMeanIntegerExpr := .pow (531441, 16777216) e20 12
  let e33 : LowMeanIntegerExpr := .mul (1307876301, 41943040000) e31 e32
  let e34 : LowMeanIntegerExpr := .neg (-1307876301, 41943040000) e33
  let e35 : LowMeanIntegerExpr := .add (788521459843, 26214400000000) e30 e34
  let e36 : LowMeanIntegerExpr := .add (788783603843, 26214400000000) e0 e35
  let e37 : LowMeanIntegerExpr := .neg (-788521459843, 26214400000000) e35
  let e38 : LowMeanIntegerExpr := .add (1, 100000) e36 e37
  e38

noncomputable def lowMeanSeedRecord0012 : LowMeanDirectSeedInput :=
  { record := 12, positions := [{ j := -1, mode := 0, left := 9, right := 0 }, { j := 0, mode := 1, left := 10, right := 11 }, { j := 1, mode := 0, left := 12, right := 0 }], target := { R := 12, expr := lowMeanSeedTargetExpr0012 } }

noncomputable def lowMeanSeedTargetExpr0013 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (9807, 125000)
  let e2 : LowMeanIntegerExpr := .atom (4183, 5000000)
  let e3 : LowMeanIntegerExpr := .atom (13, 1)
  let e4 : LowMeanIntegerExpr := .atom (121, 4)
  let e5 : LowMeanIntegerExpr := .neg (-121, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-69, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-288627, 20000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (1280493, 20000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (327, 6250000)
  let e10 : LowMeanIntegerExpr := .pow (4761, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1556847, 100000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1556847, 100000000) e11
  let e13 : LowMeanIntegerExpr := .add (2422809, 50000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (5511, 1000000)
  let e15 : LowMeanIntegerExpr := .atom (1, 4)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (3, 8)
  let e18 : LowMeanIntegerExpr := .atom (1, 1)
  let e19 : LowMeanIntegerExpr := .neg (-1, 4) e15
  let e20 : LowMeanIntegerExpr := .add (3, 4) e18 e19
  let e21 : LowMeanIntegerExpr := .mul (3, 16) e15 e20
  let e22 : LowMeanIntegerExpr := .neg (-3, 8) e17
  let e23 : LowMeanIntegerExpr := .add (5, 8) e18 e22
  let e24 : LowMeanIntegerExpr := .mul (15, 64) e17 e23
  let e25 : LowMeanIntegerExpr := .maximum (15, 64) e21 e24
  let e26 : LowMeanIntegerExpr := .selectLE (15, 64) e16 e17 e15 e25
  let e27 : LowMeanIntegerExpr := .selectLE (15, 64) e15 e16 e26 e25
  let e28 : LowMeanIntegerExpr := .mul (16533, 12800000) e14 e27
  let e29 : LowMeanIntegerExpr := .mul (214929, 12800000) e28 e3
  let e30 : LowMeanIntegerExpr := .add (104396013, 1600000000) e13 e29
  let e31 : LowMeanIntegerExpr := .atom (2461, 2500)
  let e32 : LowMeanIntegerExpr := .pow (1594323, 67108864) e20 13
  let e33 : LowMeanIntegerExpr := .mul (3923628903, 167772160000) e31 e32
  let e34 : LowMeanIntegerExpr := .neg (-3923628903, 167772160000) e33
  let e35 : LowMeanIntegerExpr := .add (4389429043593, 104857600000000) e30 e34
  let e36 : LowMeanIntegerExpr := .add (4390477619593, 104857600000000) e0 e35
  let e37 : LowMeanIntegerExpr := .neg (-4389429043593, 104857600000000) e35
  let e38 : LowMeanIntegerExpr := .add (1, 100000) e36 e37
  e38

noncomputable def lowMeanSeedRecord0013 : LowMeanDirectSeedInput :=
  { record := 13, positions := [{ j := -1, mode := 0, left := 13, right := 0 }, { j := 0, mode := 2, left := 14, right := 0 }, { j := 1, mode := 0, left := 15, right := 0 }], target := { R := 13, expr := lowMeanSeedTargetExpr0013 } }

noncomputable def lowMeanSeedTargetExpr0014 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (9807, 125000)
  let e2 : LowMeanIntegerExpr := .atom (4183, 5000000)
  let e3 : LowMeanIntegerExpr := .atom (14, 1)
  let e4 : LowMeanIntegerExpr := .atom (121, 4)
  let e5 : LowMeanIntegerExpr := .neg (-121, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-65, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-54379, 4000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (51889, 800000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (327, 6250000)
  let e10 : LowMeanIntegerExpr := .pow (4225, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (55263, 4000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-55263, 4000000) e11
  let e13 : LowMeanIntegerExpr := .add (102091, 2000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (5511, 1000000)
  let e15 : LowMeanIntegerExpr := .atom (1, 4)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (3, 8)
  let e18 : LowMeanIntegerExpr := .atom (1, 1)
  let e19 : LowMeanIntegerExpr := .neg (-1, 4) e15
  let e20 : LowMeanIntegerExpr := .add (3, 4) e18 e19
  let e21 : LowMeanIntegerExpr := .mul (3, 16) e15 e20
  let e22 : LowMeanIntegerExpr := .neg (-3, 8) e17
  let e23 : LowMeanIntegerExpr := .add (5, 8) e18 e22
  let e24 : LowMeanIntegerExpr := .mul (15, 64) e17 e23
  let e25 : LowMeanIntegerExpr := .maximum (15, 64) e21 e24
  let e26 : LowMeanIntegerExpr := .selectLE (15, 64) e16 e17 e15 e25
  let e27 : LowMeanIntegerExpr := .selectLE (15, 64) e15 e16 e26 e25
  let e28 : LowMeanIntegerExpr := .mul (16533, 12800000) e14 e27
  let e29 : LowMeanIntegerExpr := .mul (115731, 6400000) e28 e3
  let e30 : LowMeanIntegerExpr := .add (2212111, 32000000) e13 e29
  let e31 : LowMeanIntegerExpr := .atom (2461, 2500)
  let e32 : LowMeanIntegerExpr := .pow (4782969, 268435456) e20 14
  let e33 : LowMeanIntegerExpr := .mul (11770886709, 671088640000) e31 e32
  let e34 : LowMeanIntegerExpr := .neg (-11770886709, 671088640000) e33
  let e35 : LowMeanIntegerExpr := .add (865511084243, 16777216000000) e30 e34
  let e36 : LowMeanIntegerExpr := .add (865678856403, 16777216000000) e0 e35
  let e37 : LowMeanIntegerExpr := .neg (-865511084243, 16777216000000) e35
  let e38 : LowMeanIntegerExpr := .add (1, 100000) e36 e37
  e38

noncomputable def lowMeanSeedRecord0014 : LowMeanDirectSeedInput :=
  { record := 14, positions := [{ j := -1, mode := 0, left := 16, right := 0 }, { j := 0, mode := 0, left := 17, right := 0 }, { j := 1, mode := 0, left := 18, right := 0 }], target := { R := 14, expr := lowMeanSeedTargetExpr0014 } }

noncomputable def lowMeanSeedTargetExpr0015 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (9807, 125000)
  let e2 : LowMeanIntegerExpr := .atom (4183, 5000000)
  let e3 : LowMeanIntegerExpr := .atom (15, 1)
  let e4 : LowMeanIntegerExpr := .atom (121, 4)
  let e5 : LowMeanIntegerExpr := .neg (-121, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-61, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-255163, 20000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (1313957, 20000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (327, 6250000)
  let e10 : LowMeanIntegerExpr := .pow (3721, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1216767, 100000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1216767, 100000000) e11
  let e13 : LowMeanIntegerExpr := .add (2676509, 50000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (5511, 1000000)
  let e15 : LowMeanIntegerExpr := .atom (1, 4)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (3, 8)
  let e18 : LowMeanIntegerExpr := .atom (1, 1)
  let e19 : LowMeanIntegerExpr := .neg (-1, 4) e15
  let e20 : LowMeanIntegerExpr := .add (3, 4) e18 e19
  let e21 : LowMeanIntegerExpr := .mul (3, 16) e15 e20
  let e22 : LowMeanIntegerExpr := .neg (-3, 8) e17
  let e23 : LowMeanIntegerExpr := .add (5, 8) e18 e22
  let e24 : LowMeanIntegerExpr := .mul (15, 64) e17 e23
  let e25 : LowMeanIntegerExpr := .maximum (15, 64) e21 e24
  let e26 : LowMeanIntegerExpr := .selectLE (15, 64) e16 e17 e15 e25
  let e27 : LowMeanIntegerExpr := .selectLE (15, 64) e15 e16 e26 e25
  let e28 : LowMeanIntegerExpr := .mul (16533, 12800000) e14 e27
  let e29 : LowMeanIntegerExpr := .mul (49599, 2560000) e28 e3
  let e30 : LowMeanIntegerExpr := .add (116647663, 1600000000) e13 e29
  let e31 : LowMeanIntegerExpr := .atom (2461, 2500)
  let e32 : LowMeanIntegerExpr := .pow (14348907, 1073741824) e20 15
  let e33 : LowMeanIntegerExpr := .mul (35312660127, 2684354560000) e31 e32
  let e34 : LowMeanIntegerExpr := .neg (-35312660127, 2684354560000) e33
  let e35 : LowMeanIntegerExpr := .add (100243527298513, 1677721600000000) e30 e34
  let e36 : LowMeanIntegerExpr := .add (100260304514513, 1677721600000000) e0 e35
  let e37 : LowMeanIntegerExpr := .neg (-100243527298513, 1677721600000000) e35
  let e38 : LowMeanIntegerExpr := .add (1, 100000) e36 e37
  e38

noncomputable def lowMeanSeedRecord0015 : LowMeanDirectSeedInput :=
  { record := 15, positions := [{ j := -1, mode := 0, left := 19, right := 0 }, { j := 0, mode := 2, left := 20, right := 0 }, { j := 1, mode := 2, left := 21, right := 0 }, { j := 2, mode := 0, left := 22, right := 0 }, { j := 7, mode := 0, left := 23, right := 0 }], target := { R := 15, expr := lowMeanSeedTargetExpr0015 } }

noncomputable def lowMeanSeedGroup0000 : List LowMeanDirectSeedInput := [lowMeanSeedRecord0000, lowMeanSeedRecord0001, lowMeanSeedRecord0002, lowMeanSeedRecord0003, lowMeanSeedRecord0004, lowMeanSeedRecord0005, lowMeanSeedRecord0006, lowMeanSeedRecord0007, lowMeanSeedRecord0008, lowMeanSeedRecord0009, lowMeanSeedRecord0010, lowMeanSeedRecord0011, lowMeanSeedRecord0012, lowMeanSeedRecord0013, lowMeanSeedRecord0014, lowMeanSeedRecord0015]

end Erdos993Lean.Analytic.V213
