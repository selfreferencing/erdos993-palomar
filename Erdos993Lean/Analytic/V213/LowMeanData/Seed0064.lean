module

public import Erdos993Lean.Analytic.V213.LowMeanCoreAll
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0561
public import Erdos993Lean.Analytic.V213.LowMeanFiberSeed
public import Erdos993Lean.Analytic.V213.LowMeanIntegerExpr
public import Erdos993Lean.Analytic.V213.LowMeanSeedGeometry
public import Erdos993Lean.Analytic.V213.LowMeanWidthData
public import Erdos993Lean.Ceiling.Prefix
public import Erdos993Lean.Ceiling.Statement

/-! Exact core/budget keys and equation-51 targets for the direct fibers. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanSeedTargetExpr0064 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (14303, 100000)
  let e2 : LowMeanIntegerExpr := .atom (149, 20000)
  let e3 : LowMeanIntegerExpr := .atom (7, 1)
  let e4 : LowMeanIntegerExpr := .atom (22, 1)
  let e5 : LowMeanIntegerExpr := .neg (-22, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-15, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-447, 4000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (391, 12500) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1641, 2000000)
  let e10 : LowMeanIntegerExpr := .pow (225, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (14769, 80000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-14769, 80000) e11
  let e13 : LowMeanIntegerExpr := .add (-61333, 400000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (781, 50000)
  let e15 : LowMeanIntegerExpr := .atom (3, 8)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (39, 89)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-3, 8) e15
  let e21 : LowMeanIntegerExpr := .add (5, 8) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (15, 64) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-39, 89) e17
  let e24 : LowMeanIntegerExpr := .add (50, 89) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (1950, 7921) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (1950, 7921) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1950, 7921) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1950, 7921) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (30459, 7921000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (213213, 7921000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-400533493, 3168400000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1181, 125)
  let e33 : LowMeanIntegerExpr := .pow (78125, 2097152) e21 7
  let e34 : LowMeanIntegerExpr := .mul (738125, 2097152) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-738125, 2097152) e34
  let e36 : LowMeanIntegerExpr := .add (-24833241139937, 51911065600000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-24832722029281, 51911065600000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (24833241139937, 51911065600000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0064 : LowMeanDirectSeedInput :=
  { record := 64, positions := [], target := { R := 7, expr := lowMeanSeedTargetExpr0064 } }

noncomputable def lowMeanSeedTargetExpr0065 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (14303, 100000)
  let e2 : LowMeanIntegerExpr := .atom (149, 20000)
  let e3 : LowMeanIntegerExpr := .atom (8, 1)
  let e4 : LowMeanIntegerExpr := .atom (22, 1)
  let e5 : LowMeanIntegerExpr := .neg (-22, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-14, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1043, 10000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (3873, 100000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1641, 2000000)
  let e10 : LowMeanIntegerExpr := .pow (196, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (80409, 500000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-80409, 500000) e11
  let e13 : LowMeanIntegerExpr := .add (-15261, 125000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (781, 50000)
  let e15 : LowMeanIntegerExpr := .atom (3, 8)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (39, 89)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-3, 8) e15
  let e21 : LowMeanIntegerExpr := .add (5, 8) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (15, 64) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-39, 89) e17
  let e24 : LowMeanIntegerExpr := .add (50, 89) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (1950, 7921) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (1950, 7921) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1950, 7921) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1950, 7921) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (30459, 7921000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (30459, 990125) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-90423381, 990125000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1181, 125)
  let e33 : LowMeanIntegerExpr := .pow (390625, 16777216) e21 8
  let e34 : LowMeanIntegerExpr := .mul (3690625, 16777216) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-3690625, 16777216) e34
  let e36 : LowMeanIntegerExpr := .add (-646404084076537, 2076442624000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-646383319650297, 2076442624000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (646404084076537, 2076442624000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0065 : LowMeanDirectSeedInput :=
  { record := 65, positions := [], target := { R := 8, expr := lowMeanSeedTargetExpr0065 } }

noncomputable def lowMeanSeedTargetExpr0066 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (14303, 100000)
  let e2 : LowMeanIntegerExpr := .atom (149, 20000)
  let e3 : LowMeanIntegerExpr := .atom (9, 1)
  let e4 : LowMeanIntegerExpr := .atom (22, 1)
  let e5 : LowMeanIntegerExpr := .neg (-22, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-13, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1937, 20000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (2309, 50000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1641, 2000000)
  let e10 : LowMeanIntegerExpr := .pow (169, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (277329, 2000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-277329, 2000000) e11
  let e13 : LowMeanIntegerExpr := .add (-184969, 2000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (781, 50000)
  let e15 : LowMeanIntegerExpr := .atom (3, 8)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (39, 89)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-3, 8) e15
  let e21 : LowMeanIntegerExpr := .add (5, 8) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (15, 64) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-39, 89) e17
  let e24 : LowMeanIntegerExpr := .add (50, 89) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (1950, 7921) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (1950, 7921) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1950, 7921) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1950, 7921) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (30459, 7921000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (274131, 7921000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-916877449, 15842000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1181, 125)
  let e33 : LowMeanIntegerExpr := .pow (1953125, 134217728) e21 9
  let e34 : LowMeanIntegerExpr := .mul (18453125, 134217728) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-18453125, 134217728) e34
  let e36 : LowMeanIntegerExpr := .add (-3245278236790749, 16611540992000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-3245112121380829, 16611540992000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (3245278236790749, 16611540992000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0066 : LowMeanDirectSeedInput :=
  { record := 66, positions := [{ j := 6, mode := 0, left := 311, right := 0 }], target := { R := 9, expr := lowMeanSeedTargetExpr0066 } }

noncomputable def lowMeanSeedTargetExpr0067 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (14303, 100000)
  let e2 : LowMeanIntegerExpr := .atom (149, 20000)
  let e3 : LowMeanIntegerExpr := .atom (10, 1)
  let e4 : LowMeanIntegerExpr := .atom (22, 1)
  let e5 : LowMeanIntegerExpr := .neg (-22, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-12, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-447, 5000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (5363, 100000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1641, 2000000)
  let e10 : LowMeanIntegerExpr := .pow (144, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (14769, 125000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-14769, 125000) e11
  let e13 : LowMeanIntegerExpr := .add (-32261, 500000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (781, 50000)
  let e15 : LowMeanIntegerExpr := .atom (3, 8)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (39, 89)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-3, 8) e15
  let e21 : LowMeanIntegerExpr := .add (5, 8) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (15, 64) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-39, 89) e17
  let e24 : LowMeanIntegerExpr := .add (50, 89) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (1950, 7921) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (1950, 7921) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1950, 7921) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1950, 7921) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (30459, 7921000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (30459, 792100) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-103244381, 3960500000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1181, 125)
  let e33 : LowMeanIntegerExpr := .pow (9765625, 1073741824) e21 10
  let e34 : LowMeanIntegerExpr := .mul (92265625, 1073741824) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-92265625, 1073741824) e34
  let e36 : LowMeanIntegerExpr := .add (-14883619305787217, 132892327936000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-14882290382507857, 132892327936000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (14883619305787217, 132892327936000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0067 : LowMeanDirectSeedInput :=
  { record := 67, positions := [], target := { R := 10, expr := lowMeanSeedTargetExpr0067 } }

noncomputable def lowMeanSeedTargetExpr0068 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (14303, 100000)
  let e2 : LowMeanIntegerExpr := .atom (149, 20000)
  let e3 : LowMeanIntegerExpr := .atom (11, 1)
  let e4 : LowMeanIntegerExpr := .atom (22, 1)
  let e5 : LowMeanIntegerExpr := .neg (-22, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-11, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1639, 20000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (1527, 25000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1641, 2000000)
  let e10 : LowMeanIntegerExpr := .pow (121, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (198561, 2000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-198561, 2000000) e11
  let e13 : LowMeanIntegerExpr := .add (-76401, 2000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (781, 50000)
  let e15 : LowMeanIntegerExpr := .atom (3, 8)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (39, 89)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-3, 8) e15
  let e21 : LowMeanIntegerExpr := .add (5, 8) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (15, 64) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-39, 89) e17
  let e24 : LowMeanIntegerExpr := .add (50, 89) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (1950, 7921) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (1950, 7921) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1950, 7921) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1950, 7921) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (30459, 7921000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (335049, 7921000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (64925679, 15842000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1181, 125)
  let e33 : LowMeanIntegerExpr := .pow (48828125, 8589934592) e21 11
  let e34 : LowMeanIntegerExpr := .mul (461328125, 8589934592) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-461328125, 8589934592) e34
  let e36 : LowMeanIntegerExpr := .add (-52739475158584469, 1063138623488000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-52728843772349589, 1063138623488000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (52739475158584469, 1063138623488000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0068 : LowMeanDirectSeedInput :=
  { record := 68, positions := [{ j := 7, mode := 0, left := 312, right := 0 }], target := { R := 11, expr := lowMeanSeedTargetExpr0068 } }

noncomputable def lowMeanSeedTargetExpr0069 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (14303, 100000)
  let e2 : LowMeanIntegerExpr := .atom (149, 20000)
  let e3 : LowMeanIntegerExpr := .atom (12, 1)
  let e4 : LowMeanIntegerExpr := .atom (22, 1)
  let e5 : LowMeanIntegerExpr := .neg (-22, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-10, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-149, 2000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (6853, 100000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1641, 2000000)
  let e10 : LowMeanIntegerExpr := .pow (100, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1641, 20000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1641, 20000) e11
  let e13 : LowMeanIntegerExpr := .add (-169, 12500) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (781, 50000)
  let e15 : LowMeanIntegerExpr := .atom (3, 8)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (39, 89)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-3, 8) e15
  let e21 : LowMeanIntegerExpr := .add (5, 8) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (15, 64) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-39, 89) e17
  let e24 : LowMeanIntegerExpr := .add (50, 89) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (1950, 7921) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (1950, 7921) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1950, 7921) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1950, 7921) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (30459, 7921000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (91377, 1980250) e29 e3
  let e31 : LowMeanIntegerExpr := .add (3230201, 99012500) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1181, 125)
  let e33 : LowMeanIntegerExpr := .pow (244140625, 68719476736) e21 12
  let e34 : LowMeanIntegerExpr := .mul (2306640625, 68719476736) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-2306640625, 68719476736) e34
  let e36 : LowMeanIntegerExpr := .add (-1602133102677141, 1701021797580800000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-1585122884701333, 1701021797580800000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (1602133102677141, 1701021797580800000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0069 : LowMeanDirectSeedInput :=
  { record := 69, positions := [], target := { R := 12, expr := lowMeanSeedTargetExpr0069 } }

noncomputable def lowMeanSeedTargetExpr0070 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (14303, 100000)
  let e2 : LowMeanIntegerExpr := .atom (149, 20000)
  let e3 : LowMeanIntegerExpr := .atom (13, 1)
  let e4 : LowMeanIntegerExpr := .atom (22, 1)
  let e5 : LowMeanIntegerExpr := .neg (-22, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-9, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1341, 20000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (3799, 50000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1641, 2000000)
  let e10 : LowMeanIntegerExpr := .pow (81, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (132921, 2000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-132921, 2000000) e11
  let e13 : LowMeanIntegerExpr := .add (19039, 2000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (781, 50000)
  let e15 : LowMeanIntegerExpr := .atom (3, 8)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (39, 89)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-3, 8) e15
  let e21 : LowMeanIntegerExpr := .add (5, 8) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (15, 64) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-39, 89) e17
  let e24 : LowMeanIntegerExpr := .add (50, 89) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (1950, 7921) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (1950, 7921) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1950, 7921) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1950, 7921) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (30459, 7921000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (395967, 7921000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (942741919, 15842000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1181, 125)
  let e33 : LowMeanIntegerExpr := .pow (1220703125, 549755813888) e21 13
  let e34 : LowMeanIntegerExpr := .mul (11533203125, 549755813888) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-11533203125, 549755813888) e34
  let e36 : LowMeanIntegerExpr := .add (2621631617655702899, 68040871903232000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (2622312026374735219, 68040871903232000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-2621631617655702899, 68040871903232000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0070 : LowMeanDirectSeedInput :=
  { record := 70, positions := [{ j := 8, mode := 0, left := 313, right := 0 }], target := { R := 13, expr := lowMeanSeedTargetExpr0070 } }

noncomputable def lowMeanSeedTargetExpr0071 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (14303, 100000)
  let e2 : LowMeanIntegerExpr := .atom (149, 20000)
  let e3 : LowMeanIntegerExpr := .atom (14, 1)
  let e4 : LowMeanIntegerExpr := .atom (22, 1)
  let e5 : LowMeanIntegerExpr := .neg (-22, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-8, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-149, 2500) e2 e6
  let e8 : LowMeanIntegerExpr := .add (8343, 100000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1641, 2000000)
  let e10 : LowMeanIntegerExpr := .pow (64, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1641, 31250) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1641, 31250) e11
  let e13 : LowMeanIntegerExpr := .add (15459, 500000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (781, 50000)
  let e15 : LowMeanIntegerExpr := .atom (3, 8)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (39, 89)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-3, 8) e15
  let e21 : LowMeanIntegerExpr := .add (5, 8) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (15, 64) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-39, 89) e17
  let e24 : LowMeanIntegerExpr := .add (50, 89) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (1950, 7921) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (1950, 7921) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1950, 7921) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1950, 7921) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (30459, 7921000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (213213, 3960500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (335663739, 3960500000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1181, 125)
  let e33 : LowMeanIntegerExpr := .pow (6103515625, 4398046511104) e21 14
  let e34 : LowMeanIntegerExpr := .mul (57666015625, 4398046511104) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-57666015625, 4398046511104) e34
  let e36 : LowMeanIntegerExpr := .add (38996202541570661183, 544326975225856000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (39001645811322919743, 544326975225856000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-38996202541570661183, 544326975225856000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0071 : LowMeanDirectSeedInput :=
  { record := 71, positions := [{ j := 8, mode := 0, left := 314, right := 0 }], target := { R := 14, expr := lowMeanSeedTargetExpr0071 } }

noncomputable def lowMeanSeedTargetExpr0072 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (14303, 100000)
  let e2 : LowMeanIntegerExpr := .atom (149, 20000)
  let e3 : LowMeanIntegerExpr := .atom (15, 1)
  let e4 : LowMeanIntegerExpr := .atom (22, 1)
  let e5 : LowMeanIntegerExpr := .neg (-22, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-7, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1043, 20000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (284, 3125) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1641, 2000000)
  let e10 : LowMeanIntegerExpr := .pow (49, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (80409, 2000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-80409, 2000000) e11
  let e13 : LowMeanIntegerExpr := .add (101351, 2000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (781, 50000)
  let e15 : LowMeanIntegerExpr := .atom (3, 8)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (39, 89)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-3, 8) e15
  let e21 : LowMeanIntegerExpr := .add (5, 8) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (15, 64) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-39, 89) e17
  let e24 : LowMeanIntegerExpr := .add (50, 89) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (1950, 7921) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (1950, 7921) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1950, 7921) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1950, 7921) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (30459, 7921000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (91377, 1584200) e29 e3
  let e31 : LowMeanIntegerExpr := .add (1716571271, 15842000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1181, 125)
  let e33 : LowMeanIntegerExpr := .pow (30517578125, 35184372088832) e21 15
  let e34 : LowMeanIntegerExpr := .mul (288330078125, 35184372088832) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-288330078125, 35184372088832) e34
  let e36 : LowMeanIntegerExpr := .add (436162165767242352699, 4354615801806848000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (436205711925260421179, 4354615801806848000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-436162165767242352699, 4354615801806848000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0072 : LowMeanDirectSeedInput :=
  { record := 72, positions := [{ j := 2, mode := 0, left := 315, right := 0 }, { j := 9, mode := 0, left := 316, right := 0 }], target := { R := 15, expr := lowMeanSeedTargetExpr0072 } }

noncomputable def lowMeanSeedTargetExpr0073 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (14303, 100000)
  let e2 : LowMeanIntegerExpr := .atom (149, 20000)
  let e3 : LowMeanIntegerExpr := .atom (16, 1)
  let e4 : LowMeanIntegerExpr := .atom (22, 1)
  let e5 : LowMeanIntegerExpr := .neg (-22, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-6, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-447, 10000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (9833, 100000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1641, 2000000)
  let e10 : LowMeanIntegerExpr := .pow (36, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (14769, 500000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-14769, 500000) e11
  let e13 : LowMeanIntegerExpr := .add (8599, 125000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (781, 50000)
  let e15 : LowMeanIntegerExpr := .atom (3, 8)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (39, 89)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-3, 8) e15
  let e21 : LowMeanIntegerExpr := .add (5, 8) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (15, 64) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-39, 89) e17
  let e24 : LowMeanIntegerExpr := .add (50, 89) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (1950, 7921) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (1950, 7921) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1950, 7921) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1950, 7921) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (30459, 7921000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (60918, 990125) e29 e3
  let e31 : LowMeanIntegerExpr := .add (129030679, 990125000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1181, 125)
  let e33 : LowMeanIntegerExpr := .pow (152587890625, 281474976710656) e21 16
  let e34 : LowMeanIntegerExpr := .mul (1441650390625, 281474976710656) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1441650390625, 281474976710656) e34
  let e36 : LowMeanIntegerExpr := .add (4361436659183444011303, 34836926414454784000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (4361785028447588559143, 34836926414454784000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-4361436659183444011303, 34836926414454784000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0073 : LowMeanDirectSeedInput :=
  { record := 73, positions := [{ j := 2, mode := 0, left := 317, right := 0 }, { j := 9, mode := 0, left := 318, right := 0 }], target := { R := 16, expr := lowMeanSeedTargetExpr0073 } }

noncomputable def lowMeanSeedTargetExpr0074 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (14303, 100000)
  let e2 : LowMeanIntegerExpr := .atom (149, 20000)
  let e3 : LowMeanIntegerExpr := .atom (17, 1)
  let e4 : LowMeanIntegerExpr := .atom (22, 1)
  let e5 : LowMeanIntegerExpr := .neg (-22, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-5, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-149, 4000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (5289, 50000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1641, 2000000)
  let e10 : LowMeanIntegerExpr := .pow (25, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1641, 80000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1641, 80000) e11
  let e13 : LowMeanIntegerExpr := .add (34107, 400000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (781, 50000)
  let e15 : LowMeanIntegerExpr := .atom (3, 8)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (39, 89)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-3, 8) e15
  let e21 : LowMeanIntegerExpr := .add (5, 8) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (15, 64) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-39, 89) e17
  let e24 : LowMeanIntegerExpr := .add (50, 89) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (1950, 7921) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (1950, 7921) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1950, 7921) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1950, 7921) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (30459, 7921000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (517803, 7921000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (477282747, 3168400000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1181, 125)
  let e33 : LowMeanIntegerExpr := .pow (762939453125, 2251799813685248) e21 17
  let e34 : LowMeanIntegerExpr := .mul (7208251953125, 2251799813685248) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-7208251953125, 2251799813685248) e34
  let e36 : LowMeanIntegerExpr := .add (8218020119386735225127, 55739082263127654400000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (8218577510209366501671, 55739082263127654400000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-8218020119386735225127, 55739082263127654400000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0074 : LowMeanDirectSeedInput :=
  { record := 74, positions := [{ j := 2, mode := 0, left := 319, right := 0 }, { j := 3, mode := 0, left := 320, right := 0 }, { j := 10, mode := 0, left := 321, right := 0 }], target := { R := 17, expr := lowMeanSeedTargetExpr0074 } }

noncomputable def lowMeanSeedTargetExpr0075 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (14303, 100000)
  let e2 : LowMeanIntegerExpr := .atom (149, 20000)
  let e3 : LowMeanIntegerExpr := .atom (18, 1)
  let e4 : LowMeanIntegerExpr := .atom (22, 1)
  let e5 : LowMeanIntegerExpr := .neg (-22, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-4, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-149, 5000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (11323, 100000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1641, 2000000)
  let e10 : LowMeanIntegerExpr := .pow (16, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1641, 125000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1641, 125000) e11
  let e13 : LowMeanIntegerExpr := .add (50051, 500000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (781, 50000)
  let e15 : LowMeanIntegerExpr := .atom (3, 8)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (39, 89)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-3, 8) e15
  let e21 : LowMeanIntegerExpr := .add (5, 8) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (15, 64) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-39, 89) e17
  let e24 : LowMeanIntegerExpr := .add (50, 89) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (1950, 7921) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (1950, 7921) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1950, 7921) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1950, 7921) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (30459, 7921000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (274131, 3960500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (670584971, 3960500000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1181, 125)
  let e33 : LowMeanIntegerExpr := .pow (3814697265625, 18014398509481984) e21 18
  let e34 : LowMeanIntegerExpr := .mul (36041259765625, 18014398509481984) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-36041259765625, 18014398509481984) e34
  let e36 : LowMeanIntegerExpr := .add (373045109148801926661327, 2229563290525106176000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (373067404781707177723087, 2229563290525106176000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-373045109148801926661327, 2229563290525106176000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0075 : LowMeanDirectSeedInput :=
  { record := 75, positions := [{ j := 3, mode := 0, left := 322, right := 0 }, { j := 4, mode := 0, left := 323, right := 0 }, { j := 10, mode := 0, left := 324, right := 0 }], target := { R := 18, expr := lowMeanSeedTargetExpr0075 } }

noncomputable def lowMeanSeedTargetExpr0076 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (14303, 100000)
  let e2 : LowMeanIntegerExpr := .atom (149, 20000)
  let e3 : LowMeanIntegerExpr := .atom (21, 1)
  let e4 : LowMeanIntegerExpr := .atom (22, 1)
  let e5 : LowMeanIntegerExpr := .neg (-22, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-1, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-149, 20000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (6779, 50000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1641, 2000000)
  let e10 : LowMeanIntegerExpr := .pow (1, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1641, 2000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1641, 2000000) e11
  let e13 : LowMeanIntegerExpr := .add (269519, 2000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (781, 50000)
  let e15 : LowMeanIntegerExpr := .atom (3, 8)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (39, 89)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-3, 8) e15
  let e21 : LowMeanIntegerExpr := .add (5, 8) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (15, 64) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-39, 89) e17
  let e24 : LowMeanIntegerExpr := .add (50, 89) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (1950, 7921) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (1950, 7921) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1950, 7921) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1950, 7921) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (30459, 7921000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (639639, 7921000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (3414137999, 15842000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1181, 125)
  let e33 : LowMeanIntegerExpr := .pow (476837158203125, 9223372036854775808) e21 21
  let e34 : LowMeanIntegerExpr := .mul (4505157470703125, 9223372036854775808) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-4505157470703125, 9223372036854775808) e34
  let e36 : LowMeanIntegerExpr := .add (245456986291320622066161939, 1141536404748854362112000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (245468401655368110609783059, 1141536404748854362112000000) e0 e36
  let e38 : LowMeanIntegerExpr := .atom (19, 1)
  let e39 : LowMeanIntegerExpr := .add (-3, 1) e38 e5
  let e40 : LowMeanIntegerExpr := .mul (-447, 20000) e2 e39
  let e41 : LowMeanIntegerExpr := .add (3017, 25000) e1 e40
  let e42 : LowMeanIntegerExpr := .pow (9, 1) e39 2
  let e43 : LowMeanIntegerExpr := .mul (14769, 2000000) e9 e42
  let e44 : LowMeanIntegerExpr := .neg (-14769, 2000000) e43
  let e45 : LowMeanIntegerExpr := .add (226591, 2000000) e41 e44
  let e46 : LowMeanIntegerExpr := .mul (578721, 7921000) e29 e38
  let e47 : LowMeanIntegerExpr := .add (2952269311, 15842000000) e45 e46
  let e48 : LowMeanIntegerExpr := .pow (19073486328125, 144115188075855872) e21 19
  let e49 : LowMeanIntegerExpr := .mul (180206298828125, 144115188075855872) e32 e48
  let e50 : LowMeanIntegerExpr := .neg (-180206298828125, 144115188075855872) e49
  let e51 : LowMeanIntegerExpr := .add (3301656397025838083708939, 17836506324200849408000000) e47 e50
  let e52 : LowMeanIntegerExpr := .neg (-3301656397025838083708939, 17836506324200849408000000) e51
  let e53 : LowMeanIntegerExpr := .add (34162392245714473252410963, 1141536404748854362112000000) e37 e52
  e53

noncomputable def lowMeanSeedRecord0076 : LowMeanDirectSeedInput :=
  { record := 76, positions := [{ j := 3, mode := 0, left := 325, right := 0 }, { j := 4, mode := 0, left := 326, right := 0 }, { j := 10, mode := 0, left := 327, right := 0 }, { j := 11, mode := 0, left := 328, right := 0 }], target := { R := 21, expr := lowMeanSeedTargetExpr0076 } }

noncomputable def lowMeanSeedTargetExpr0077 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (14303, 100000)
  let e2 : LowMeanIntegerExpr := .atom (149, 20000)
  let e3 : LowMeanIntegerExpr := .atom (22, 1)
  let e4 : LowMeanIntegerExpr := .neg (-22, 1) e3
  let e5 : LowMeanIntegerExpr := .add (0, 1) e3 e4
  let e6 : LowMeanIntegerExpr := .mul (0, 1) e2 e5
  let e7 : LowMeanIntegerExpr := .add (14303, 100000) e1 e6
  let e8 : LowMeanIntegerExpr := .atom (1641, 2000000)
  let e9 : LowMeanIntegerExpr := .pow (0, 1) e5 2
  let e10 : LowMeanIntegerExpr := .mul (0, 1) e8 e9
  let e11 : LowMeanIntegerExpr := .neg (0, 1) e10
  let e12 : LowMeanIntegerExpr := .add (14303, 100000) e7 e11
  let e13 : LowMeanIntegerExpr := .atom (781, 50000)
  let e14 : LowMeanIntegerExpr := .atom (3, 8)
  let e15 : LowMeanIntegerExpr := .atom (1, 2)
  let e16 : LowMeanIntegerExpr := .atom (39, 89)
  let e17 : LowMeanIntegerExpr := .atom (1, 4)
  let e18 : LowMeanIntegerExpr := .atom (1, 1)
  let e19 : LowMeanIntegerExpr := .neg (-3, 8) e14
  let e20 : LowMeanIntegerExpr := .add (5, 8) e18 e19
  let e21 : LowMeanIntegerExpr := .mul (15, 64) e14 e20
  let e22 : LowMeanIntegerExpr := .neg (-39, 89) e16
  let e23 : LowMeanIntegerExpr := .add (50, 89) e18 e22
  let e24 : LowMeanIntegerExpr := .mul (1950, 7921) e16 e23
  let e25 : LowMeanIntegerExpr := .maximum (1950, 7921) e21 e24
  let e26 : LowMeanIntegerExpr := .selectLE (1950, 7921) e15 e16 e17 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1950, 7921) e14 e15 e26 e25
  let e28 : LowMeanIntegerExpr := .mul (30459, 7921000) e13 e27
  let e29 : LowMeanIntegerExpr := .mul (335049, 3960500) e28 e3
  let e30 : LowMeanIntegerExpr := .add (180303863, 792100000) e12 e29
  let e31 : LowMeanIntegerExpr := .atom (1181, 125)
  let e32 : LowMeanIntegerExpr := .pow (2384185791015625, 73786976294838206464) e20 22
  let e33 : LowMeanIntegerExpr := .mul (22525787353515625, 73786976294838206464) e31 e32
  let e34 : LowMeanIntegerExpr := .neg (-22525787353515625, 73786976294838206464) e33
  let e35 : LowMeanIntegerExpr := .add (415194818402688620590258451, 1826458247598166979379200000) e30 e34
  let e36 : LowMeanIntegerExpr := .add (415213082985164602260052243, 1826458247598166979379200000) e0 e35
  let e37 : LowMeanIntegerExpr := .neg (-415194818402688620590258451, 1826458247598166979379200000) e35
  let e38 : LowMeanIntegerExpr := .add (1, 100000) e36 e37
  e38

noncomputable def lowMeanSeedRecord0077 : LowMeanDirectSeedInput :=
  { record := 77, positions := [{ j := 4, mode := 0, left := 329, right := 0 }, { j := 5, mode := 0, left := 330, right := 0 }, { j := 6, mode := 0, left := 331, right := 0 }], target := { R := 22, expr := lowMeanSeedTargetExpr0077 } }

noncomputable def lowMeanSeedTargetExpr0078 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (14303, 100000)
  let e2 : LowMeanIntegerExpr := .atom (149, 20000)
  let e3 : LowMeanIntegerExpr := .atom (23, 1)
  let e4 : LowMeanIntegerExpr := .atom (22, 1)
  let e5 : LowMeanIntegerExpr := .neg (-22, 1) e4
  let e6 : LowMeanIntegerExpr := .add (1, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (149, 20000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (1881, 12500) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1641, 2000000)
  let e10 : LowMeanIntegerExpr := .pow (1, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1641, 2000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1641, 2000000) e11
  let e13 : LowMeanIntegerExpr := .add (299319, 2000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (781, 50000)
  let e15 : LowMeanIntegerExpr := .atom (3, 8)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (39, 89)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-3, 8) e15
  let e21 : LowMeanIntegerExpr := .add (5, 8) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (15, 64) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-39, 89) e17
  let e24 : LowMeanIntegerExpr := .add (50, 89) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (1950, 7921) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (1950, 7921) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1950, 7921) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1950, 7921) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (30459, 7921000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (700557, 7921000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (3772019799, 15842000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1181, 125)
  let e33 : LowMeanIntegerExpr := .pow (11920928955078125, 590295810358705651712) e21 23
  let e34 : LowMeanIntegerExpr := .mul (112628936767578125, 590295810358705651712) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-112628936767578125, 590295810358705651712) e34
  let e36 : LowMeanIntegerExpr := .add (17381431377527461231364158171, 73058329903926679175168000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (17382161960826500498155909851, 73058329903926679175168000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-17381431377527461231364158171, 73058329903926679175168000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0078 : LowMeanDirectSeedInput :=
  { record := 78, positions := [{ j := 4, mode := 0, left := 332, right := 0 }, { j := 5, mode := 0, left := 333, right := 0 }, { j := 6, mode := 0, left := 334, right := 0 }], target := { R := 23, expr := lowMeanSeedTargetExpr0078 } }

noncomputable def lowMeanSeedTargetExpr0079 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (14303, 100000)
  let e2 : LowMeanIntegerExpr := .atom (149, 20000)
  let e3 : LowMeanIntegerExpr := .atom (29, 1)
  let e4 : LowMeanIntegerExpr := .atom (22, 1)
  let e5 : LowMeanIntegerExpr := .neg (-22, 1) e4
  let e6 : LowMeanIntegerExpr := .add (7, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (1043, 20000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (9759, 50000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1641, 2000000)
  let e10 : LowMeanIntegerExpr := .pow (49, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (80409, 2000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-80409, 2000000) e11
  let e13 : LowMeanIntegerExpr := .add (309951, 2000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (781, 50000)
  let e15 : LowMeanIntegerExpr := .atom (3, 8)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (39, 89)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-3, 8) e15
  let e21 : LowMeanIntegerExpr := .add (5, 8) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (15, 64) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-39, 89) e17
  let e24 : LowMeanIntegerExpr := .add (50, 89) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (1950, 7921) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (1950, 7921) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1950, 7921) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1950, 7921) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (30459, 7921000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (883311, 7921000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (4221743871, 15842000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1181, 125)
  let e33 : LowMeanIntegerExpr := .pow (186264514923095703125, 154742504910672534362390528) e21 29
  let e34 : LowMeanIntegerExpr := .mul (1759827136993408203125, 154742504910672534362390528) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1759827136993408203125, 154742504910672534362390528) e34
  let e36 : LowMeanIntegerExpr := .add (5103557363346210350466446861269171, 19151802834334955385695240192000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (5103748881374553700020303813671091, 19151802834334955385695240192000000) e0 e36
  let e38 : LowMeanIntegerExpr := .atom (24, 1)
  let e39 : LowMeanIntegerExpr := .add (2, 1) e38 e5
  let e40 : LowMeanIntegerExpr := .mul (149, 10000) e2 e39
  let e41 : LowMeanIntegerExpr := .add (15793, 100000) e1 e40
  let e42 : LowMeanIntegerExpr := .pow (4, 1) e39 2
  let e43 : LowMeanIntegerExpr := .mul (1641, 500000) e9 e42
  let e44 : LowMeanIntegerExpr := .neg (-1641, 500000) e43
  let e45 : LowMeanIntegerExpr := .add (19331, 125000) e41 e44
  let e46 : LowMeanIntegerExpr := .mul (91377, 990125) e29 e38
  let e47 : LowMeanIntegerExpr := .add (244497851, 990125000) e45 e46
  let e48 : LowMeanIntegerExpr := .pow (59604644775390625, 4722366482869645213696) e21 24
  let e49 : LowMeanIntegerExpr := .mul (563144683837890625, 4722366482869645213696) e32 e48
  let e50 : LowMeanIntegerExpr := .neg (-563144683837890625, 4722366482869645213696) e49
  let e51 : LowMeanIntegerExpr := .add (144256359133246447053253705287, 584466639231413433401344000000) e47 e50
  let e52 : LowMeanIntegerExpr := .neg (-144256359133246447053253705287, 584466639231413433401344000000) e51
  let e53 : LowMeanIntegerExpr := .add (15070260211853364919171455953067, 766072113373398215427809607680000) e37 e52
  e53

noncomputable def lowMeanSeedRecord0079 : LowMeanDirectSeedInput :=
  { record := 79, positions := [{ j := 4, mode := 0, left := 335, right := 0 }, { j := 5, mode := 0, left := 336, right := 0 }, { j := 6, mode := 0, left := 337, right := 0 }, { j := 7, mode := 0, left := 338, right := 0 }, { j := 12, mode := 0, left := 339, right := 0 }, { j := 13, mode := 0, left := 340, right := 0 }], target := { R := 29, expr := lowMeanSeedTargetExpr0079 } }

noncomputable def lowMeanSeedGroup0064 : List LowMeanDirectSeedInput := [lowMeanSeedRecord0064, lowMeanSeedRecord0065, lowMeanSeedRecord0066, lowMeanSeedRecord0067, lowMeanSeedRecord0068, lowMeanSeedRecord0069, lowMeanSeedRecord0070, lowMeanSeedRecord0071, lowMeanSeedRecord0072, lowMeanSeedRecord0073, lowMeanSeedRecord0074, lowMeanSeedRecord0075, lowMeanSeedRecord0076, lowMeanSeedRecord0077, lowMeanSeedRecord0078, lowMeanSeedRecord0079]

end Erdos993Lean.Analytic.V213
