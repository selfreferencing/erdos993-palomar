module

public import Erdos993Lean.Analytic.V213.LowMeanCoreAll
public import Erdos993Lean.Analytic.V213.LowMeanData.Seed0352
public import Erdos993Lean.Analytic.V213.LowMeanFiberSeed
public import Erdos993Lean.Analytic.V213.LowMeanIntegerExpr
public import Erdos993Lean.Analytic.V213.LowMeanSeedGeometry
public import Erdos993Lean.Analytic.V213.LowMeanWidthData
public import Erdos993Lean.Ceiling.Prefix
public import Erdos993Lean.Ceiling.Statement

/-! Exact core/budget keys and equation-51 targets for the direct fibers. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanSeedTargetExpr0384 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (74161, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (1183, 500000)
  let e3 : LowMeanIntegerExpr := .atom (6, 1)
  let e4 : LowMeanIntegerExpr := .atom (14, 1)
  let e5 : LowMeanIntegerExpr := .neg (-14, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-8, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1183, 62500) e2 e6
  let e8 : LowMeanIntegerExpr := .add (55233, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1391, 2000000)
  let e10 : LowMeanIntegerExpr := .pow (64, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1391, 31250) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1391, 31250) e11
  let e13 : LowMeanIntegerExpr := .add (10721, 1000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (143, 10000)
  let e15 : LowMeanIntegerExpr := .atom (13, 23)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (8, 13)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-13, 23) e15
  let e21 : LowMeanIntegerExpr := .add (10, 23) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (130, 529) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-8, 13) e17
  let e24 : LowMeanIntegerExpr := .add (5, 13) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (40, 169) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (130, 529) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (130, 529) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (1859, 529000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (5577, 264500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (16825409, 529000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (573, 625)
  let e33 : LowMeanIntegerExpr := .pow (1000000, 148035889) e21 6
  let e34 : LowMeanIntegerExpr := .mul (916800, 148035889) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-916800, 148035889) e34
  let e36 : LowMeanIntegerExpr := .add (3791639279969, 148035889000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (3793119638859, 148035889000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-3791639279969, 148035889000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0384 : LowMeanDirectSeedInput :=
  { record := 384, positions := [{ j := 2, mode := 0, left := 827, right := 0 }], target := { R := 6, expr := lowMeanSeedTargetExpr0384 } }

noncomputable def lowMeanSeedTargetExpr0385 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (74161, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (1183, 500000)
  let e3 : LowMeanIntegerExpr := .atom (7, 1)
  let e4 : LowMeanIntegerExpr := .atom (14, 1)
  let e5 : LowMeanIntegerExpr := .neg (-14, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-7, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-8281, 500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (57599, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1391, 2000000)
  let e10 : LowMeanIntegerExpr := .pow (49, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (68159, 2000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-68159, 2000000) e11
  let e13 : LowMeanIntegerExpr := .add (47039, 2000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (143, 10000)
  let e15 : LowMeanIntegerExpr := .atom (13, 23)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (8, 13)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-13, 23) e15
  let e21 : LowMeanIntegerExpr := .add (10, 23) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (130, 529) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-8, 13) e17
  let e24 : LowMeanIntegerExpr := .add (5, 13) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (40, 169) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (130, 529) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (130, 529) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (1859, 529000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (13013, 529000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (50909631, 1058000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (573, 625)
  let e33 : LowMeanIntegerExpr := .pow (10000000, 3404825447) e21 7
  let e34 : LowMeanIntegerExpr := .mul (9168000, 3404825447) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-9168000, 3404825447) e34
  let e36 : LowMeanIntegerExpr := .add (309335847119433, 6809650894000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (309403943628373, 6809650894000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-309335847119433, 6809650894000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0385 : LowMeanDirectSeedInput :=
  { record := 385, positions := [], target := { R := 7, expr := lowMeanSeedTargetExpr0385 } }

noncomputable def lowMeanSeedTargetExpr0386 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (74161, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (1183, 500000)
  let e3 : LowMeanIntegerExpr := .atom (8, 1)
  let e4 : LowMeanIntegerExpr := .atom (14, 1)
  let e5 : LowMeanIntegerExpr := .neg (-14, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-6, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-3549, 250000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (11993, 200000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1391, 2000000)
  let e10 : LowMeanIntegerExpr := .pow (36, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (12519, 500000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-12519, 500000) e11
  let e13 : LowMeanIntegerExpr := .add (34927, 1000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (143, 10000)
  let e15 : LowMeanIntegerExpr := .atom (13, 23)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (8, 13)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-13, 23) e15
  let e21 : LowMeanIntegerExpr := .add (10, 23) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (130, 529) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-8, 13) e17
  let e24 : LowMeanIntegerExpr := .add (5, 13) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (40, 169) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (130, 529) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (130, 529) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (1859, 529000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (1859, 66125) e29 e3
  let e31 : LowMeanIntegerExpr := .add (33348383, 529000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (573, 625)
  let e33 : LowMeanIntegerExpr := .pow (100000000, 78310985281) e21 8
  let e34 : LowMeanIntegerExpr := .mul (91680000, 78310985281) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-91680000, 78310985281) e34
  let e36 : LowMeanIntegerExpr := .add (4845077524117487, 78310985281000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (4845860633970297, 78310985281000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-4845077524117487, 78310985281000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0386 : LowMeanDirectSeedInput :=
  { record := 386, positions := [{ j := 3, mode := 0, left := 828, right := 0 }], target := { R := 8, expr := lowMeanSeedTargetExpr0386 } }

noncomputable def lowMeanSeedTargetExpr0387 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (74161, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (1183, 500000)
  let e3 : LowMeanIntegerExpr := .atom (9, 1)
  let e4 : LowMeanIntegerExpr := .atom (14, 1)
  let e5 : LowMeanIntegerExpr := .neg (-14, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-5, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1183, 100000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (62331, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1391, 2000000)
  let e10 : LowMeanIntegerExpr := .pow (25, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1391, 80000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1391, 80000) e11
  let e13 : LowMeanIntegerExpr := .add (89887, 2000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (143, 10000)
  let e15 : LowMeanIntegerExpr := .atom (13, 23)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (8, 13)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-13, 23) e15
  let e21 : LowMeanIntegerExpr := .add (10, 23) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (130, 529) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-8, 13) e17
  let e24 : LowMeanIntegerExpr := .add (5, 13) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (40, 169) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (130, 529) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (130, 529) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (1859, 529000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (16731, 529000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (81012223, 1058000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (573, 625)
  let e33 : LowMeanIntegerExpr := .pow (1000000000, 1801152661463) e21 9
  let e34 : LowMeanIntegerExpr := .mul (916800000, 1801152661463) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-916800000, 1801152661463) e34
  let e36 : LowMeanIntegerExpr := .add (273998878388438681, 3602305322926000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (274034901441667941, 3602305322926000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-273998878388438681, 3602305322926000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0387 : LowMeanDirectSeedInput :=
  { record := 387, positions := [{ j := 8, mode := 0, left := 829, right := 0 }], target := { R := 9, expr := lowMeanSeedTargetExpr0387 } }

noncomputable def lowMeanSeedTargetExpr0388 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (74161, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (1183, 500000)
  let e3 : LowMeanIntegerExpr := .atom (10, 1)
  let e4 : LowMeanIntegerExpr := .atom (14, 1)
  let e5 : LowMeanIntegerExpr := .neg (-14, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-4, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1183, 125000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (64697, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1391, 2000000)
  let e10 : LowMeanIntegerExpr := .pow (16, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1391, 125000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1391, 125000) e11
  let e13 : LowMeanIntegerExpr := .add (53569, 1000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (143, 10000)
  let e15 : LowMeanIntegerExpr := .atom (13, 23)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (8, 13)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-13, 23) e15
  let e21 : LowMeanIntegerExpr := .add (10, 23) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (130, 529) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-8, 13) e17
  let e24 : LowMeanIntegerExpr := .add (5, 13) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (40, 169) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (130, 529) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (130, 529) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (1859, 529000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (1859, 52900) e29 e3
  let e31 : LowMeanIntegerExpr := .add (46928001, 529000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (573, 625)
  let e33 : LowMeanIntegerExpr := .pow (10000000000, 41426511213649) e21 10
  let e34 : LowMeanIntegerExpr := .mul (9168000000, 41426511213649) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-9168000000, 41426511213649) e34
  let e36 : LowMeanIntegerExpr := .add (3665809995577753281, 41426511213649000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (3666224260689889771, 41426511213649000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-3665809995577753281, 41426511213649000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0388 : LowMeanDirectSeedInput :=
  { record := 388, positions := [{ j := 9, mode := 0, left := 830, right := 0 }], target := { R := 10, expr := lowMeanSeedTargetExpr0388 } }

noncomputable def lowMeanSeedTargetExpr0389 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (74161, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (1183, 500000)
  let e3 : LowMeanIntegerExpr := .atom (11, 1)
  let e4 : LowMeanIntegerExpr := .atom (14, 1)
  let e5 : LowMeanIntegerExpr := .neg (-14, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-3, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-3549, 500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (67063, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1391, 2000000)
  let e10 : LowMeanIntegerExpr := .pow (9, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (12519, 2000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-12519, 2000000) e11
  let e13 : LowMeanIntegerExpr := .add (121607, 2000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (143, 10000)
  let e15 : LowMeanIntegerExpr := .atom (13, 23)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (8, 13)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-13, 23) e15
  let e21 : LowMeanIntegerExpr := .add (10, 23) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (130, 529) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-8, 13) e17
  let e24 : LowMeanIntegerExpr := .add (5, 13) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (40, 169) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (130, 529) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (130, 529) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (1859, 529000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (20449, 529000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (105228103, 1058000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (573, 625)
  let e33 : LowMeanIntegerExpr := .pow (100000000000, 952809757913927) e21 11
  let e34 : LowMeanIntegerExpr := .mul (91680000000, 952809757913927) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-91680000000, 952809757913927) e34
  let e36 : LowMeanIntegerExpr := .add (189348517779152694689, 1905619515827854000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (189367573974310973229, 1905619515827854000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-189348517779152694689, 1905619515827854000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0389 : LowMeanDirectSeedInput :=
  { record := 389, positions := [{ j := 9, mode := 0, left := 831, right := 0 }, { j := 10, mode := 0, left := 832, right := 0 }], target := { R := 11, expr := lowMeanSeedTargetExpr0389 } }

noncomputable def lowMeanSeedTargetExpr0390 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (74161, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (1183, 500000)
  let e3 : LowMeanIntegerExpr := .atom (12, 1)
  let e4 : LowMeanIntegerExpr := .atom (14, 1)
  let e5 : LowMeanIntegerExpr := .neg (-14, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-2, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1183, 250000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (69429, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1391, 2000000)
  let e10 : LowMeanIntegerExpr := .pow (4, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1391, 500000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1391, 500000) e11
  let e13 : LowMeanIntegerExpr := .add (66647, 1000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (143, 10000)
  let e15 : LowMeanIntegerExpr := .atom (13, 23)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (8, 13)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-13, 23) e15
  let e21 : LowMeanIntegerExpr := .add (10, 23) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (130, 529) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-8, 13) e17
  let e24 : LowMeanIntegerExpr := .add (5, 13) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (40, 169) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (130, 529) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (130, 529) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (1859, 529000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (5577, 132250) e29 e3
  let e31 : LowMeanIntegerExpr := .add (57564263, 529000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (573, 625)
  let e33 : LowMeanIntegerExpr := .pow (1000000000000, 21914624432020321) e21 12
  let e34 : LowMeanIntegerExpr := .mul (916800000000, 21914624432020321) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-916800000000, 21914624432020321) e34
  let e36 : LowMeanIntegerExpr := .add (2383769786674940225687, 21914624432020321000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (2383988932919260428897, 21914624432020321000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-2383769786674940225687, 21914624432020321000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0390 : LowMeanDirectSeedInput :=
  { record := 390, positions := [{ j := 10, mode := 0, left := 833, right := 0 }, { j := 11, mode := 0, left := 834, right := 0 }], target := { R := 12, expr := lowMeanSeedTargetExpr0390 } }

noncomputable def lowMeanSeedTargetExpr0391 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (74161, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (1183, 500000)
  let e3 : LowMeanIntegerExpr := .atom (13, 1)
  let e4 : LowMeanIntegerExpr := .atom (14, 1)
  let e5 : LowMeanIntegerExpr := .neg (-14, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-1, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1183, 500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (14359, 200000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1391, 2000000)
  let e10 : LowMeanIntegerExpr := .pow (1, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1391, 2000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1391, 2000000) e11
  let e13 : LowMeanIntegerExpr := .add (142199, 2000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (143, 10000)
  let e15 : LowMeanIntegerExpr := .atom (13, 23)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (8, 13)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-13, 23) e15
  let e21 : LowMeanIntegerExpr := .add (10, 23) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (130, 529) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-8, 13) e17
  let e24 : LowMeanIntegerExpr := .add (5, 13) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (40, 169) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (130, 529) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (130, 529) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (1859, 529000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (24167, 529000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (123557271, 1058000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (573, 625)
  let e33 : LowMeanIntegerExpr := .pow (10000000000000, 504036361936467383) e21 13
  let e34 : LowMeanIntegerExpr := .mul (9168000000000, 504036361936467383) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-9168000000000, 504036361936467383) e34
  let e36 : LowMeanIntegerExpr := .add (117708237470015473013217, 1008072723872934766000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (117718318197254202360877, 1008072723872934766000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-117708237470015473013217, 1008072723872934766000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0391 : LowMeanDirectSeedInput :=
  { record := 391, positions := [{ j := 10, mode := 0, left := 835, right := 0 }, { j := 11, mode := 0, left := 836, right := 0 }], target := { R := 13, expr := lowMeanSeedTargetExpr0391 } }

noncomputable def lowMeanSeedTargetExpr0392 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (74161, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (1183, 500000)
  let e3 : LowMeanIntegerExpr := .atom (14, 1)
  let e4 : LowMeanIntegerExpr := .neg (-14, 1) e3
  let e5 : LowMeanIntegerExpr := .add (0, 1) e3 e4
  let e6 : LowMeanIntegerExpr := .mul (0, 1) e2 e5
  let e7 : LowMeanIntegerExpr := .add (74161, 1000000) e1 e6
  let e8 : LowMeanIntegerExpr := .atom (1391, 2000000)
  let e9 : LowMeanIntegerExpr := .pow (0, 1) e5 2
  let e10 : LowMeanIntegerExpr := .mul (0, 1) e8 e9
  let e11 : LowMeanIntegerExpr := .neg (0, 1) e10
  let e12 : LowMeanIntegerExpr := .add (74161, 1000000) e7 e11
  let e13 : LowMeanIntegerExpr := .atom (143, 10000)
  let e14 : LowMeanIntegerExpr := .atom (13, 23)
  let e15 : LowMeanIntegerExpr := .atom (1, 2)
  let e16 : LowMeanIntegerExpr := .atom (8, 13)
  let e17 : LowMeanIntegerExpr := .atom (1, 4)
  let e18 : LowMeanIntegerExpr := .atom (1, 1)
  let e19 : LowMeanIntegerExpr := .neg (-13, 23) e14
  let e20 : LowMeanIntegerExpr := .add (10, 23) e18 e19
  let e21 : LowMeanIntegerExpr := .mul (130, 529) e14 e20
  let e22 : LowMeanIntegerExpr := .neg (-8, 13) e16
  let e23 : LowMeanIntegerExpr := .add (5, 13) e18 e22
  let e24 : LowMeanIntegerExpr := .mul (40, 169) e16 e23
  let e25 : LowMeanIntegerExpr := .maximum (130, 529) e21 e24
  let e26 : LowMeanIntegerExpr := .selectLE (1, 4) e15 e16 e17 e25
  let e27 : LowMeanIntegerExpr := .selectLE (130, 529) e14 e15 e26 e25
  let e28 : LowMeanIntegerExpr := .mul (1859, 529000) e13 e27
  let e29 : LowMeanIntegerExpr := .mul (13013, 264500) e28 e3
  let e30 : LowMeanIntegerExpr := .add (65257169, 529000000) e12 e29
  let e31 : LowMeanIntegerExpr := .atom (573, 625)
  let e32 : LowMeanIntegerExpr := .pow (100000000000000, 11592836324538749809) e20 14
  let e33 : LowMeanIntegerExpr := .mul (91680000000000, 11592836324538749809) e31 e32
  let e34 : LowMeanIntegerExpr := .neg (-91680000000000, 11592836324538749809) e33
  let e35 : LowMeanIntegerExpr := .add (1429994670131879098931249, 11592836324538749809000000) e30 e34
  let e36 : LowMeanIntegerExpr := .add (1430110598495124486429339, 11592836324538749809000000) e0 e35
  let e37 : LowMeanIntegerExpr := .neg (-1429994670131879098931249, 11592836324538749809000000) e35
  let e38 : LowMeanIntegerExpr := .add (1, 100000) e36 e37
  e38

noncomputable def lowMeanSeedRecord0392 : LowMeanDirectSeedInput :=
  { record := 392, positions := [{ j := 7, mode := 0, left := 837, right := 0 }, { j := 11, mode := 0, left := 838, right := 0 }, { j := 12, mode := 0, left := 839, right := 0 }], target := { R := 14, expr := lowMeanSeedTargetExpr0392 } }

noncomputable def lowMeanSeedTargetExpr0393 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (74161, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (1183, 500000)
  let e3 : LowMeanIntegerExpr := .atom (15, 1)
  let e4 : LowMeanIntegerExpr := .atom (14, 1)
  let e5 : LowMeanIntegerExpr := .neg (-14, 1) e4
  let e6 : LowMeanIntegerExpr := .add (1, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (1183, 500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (76527, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1391, 2000000)
  let e10 : LowMeanIntegerExpr := .pow (1, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1391, 2000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1391, 2000000) e11
  let e13 : LowMeanIntegerExpr := .add (151663, 2000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (143, 10000)
  let e15 : LowMeanIntegerExpr := .atom (13, 23)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (8, 13)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-13, 23) e15
  let e21 : LowMeanIntegerExpr := .add (10, 23) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (130, 529) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-8, 13) e17
  let e24 : LowMeanIntegerExpr := .add (5, 13) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (40, 169) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (130, 529) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (130, 529) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (1859, 529000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (5577, 105800) e29 e3
  let e31 : LowMeanIntegerExpr := .add (135999727, 1058000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (573, 625)
  let e33 : LowMeanIntegerExpr := .pow (1000000000000000, 266635235464391245607) e21 15
  let e34 : LowMeanIntegerExpr := .mul (916800000000000, 266635235464391245607) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-916800000000000, 266635235464391245607) e34
  let e36 : LowMeanIntegerExpr := .add (68546974021432755432404441, 533270470928782491214000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (68552306726142043257316581, 533270470928782491214000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-68546974021432755432404441, 533270470928782491214000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0393 : LowMeanDirectSeedInput :=
  { record := 393, positions := [{ j := 8, mode := 0, left := 840, right := 0 }, { j := 11, mode := 0, left := 841, right := 0 }, { j := 12, mode := 0, left := 842, right := 0 }], target := { R := 15, expr := lowMeanSeedTargetExpr0393 } }

noncomputable def lowMeanSeedTargetExpr0394 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (74161, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (1183, 500000)
  let e3 : LowMeanIntegerExpr := .atom (16, 1)
  let e4 : LowMeanIntegerExpr := .atom (14, 1)
  let e5 : LowMeanIntegerExpr := .neg (-14, 1) e4
  let e6 : LowMeanIntegerExpr := .add (2, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (1183, 250000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (78893, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1391, 2000000)
  let e10 : LowMeanIntegerExpr := .pow (4, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1391, 500000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1391, 500000) e11
  let e13 : LowMeanIntegerExpr := .add (76111, 1000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (143, 10000)
  let e15 : LowMeanIntegerExpr := .atom (13, 23)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (8, 13)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-13, 23) e15
  let e21 : LowMeanIntegerExpr := .add (10, 23) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (130, 529) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-8, 13) e17
  let e24 : LowMeanIntegerExpr := .add (5, 13) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (40, 169) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (130, 529) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (130, 529) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (1859, 529000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (3718, 66125) e29 e3
  let e31 : LowMeanIntegerExpr := .add (70006719, 529000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (573, 625)
  let e33 : LowMeanIntegerExpr := .pow (10000000000000000, 6132610415680998648961) e21 16
  let e34 : LowMeanIntegerExpr := .mul (9168000000000000, 6132610415680998648961) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-9168000000000000, 6132610415680998648961) e34
  let e36 : LowMeanIntegerExpr := .add (811567266984977062489966671, 6132610415680998648961000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (811628593089133872476456281, 6132610415680998648961000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-811567266984977062489966671, 6132610415680998648961000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0394 : LowMeanDirectSeedInput :=
  { record := 394, positions := [{ j := 8, mode := 0, left := 843, right := 0 }, { j := 9, mode := 0, left := 844, right := 0 }, { j := 11, mode := 0, left := 845, right := 0 }, { j := 12, mode := 0, left := 846, right := 0 }, { j := 13, mode := 0, left := 847, right := 0 }], target := { R := 16, expr := lowMeanSeedTargetExpr0394 } }

noncomputable def lowMeanSeedTargetExpr0395 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (74161, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (1183, 500000)
  let e3 : LowMeanIntegerExpr := .atom (17, 1)
  let e4 : LowMeanIntegerExpr := .atom (14, 1)
  let e5 : LowMeanIntegerExpr := .neg (-14, 1) e4
  let e6 : LowMeanIntegerExpr := .add (3, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (3549, 500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (81259, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1391, 2000000)
  let e10 : LowMeanIntegerExpr := .pow (9, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (12519, 2000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-12519, 2000000) e11
  let e13 : LowMeanIntegerExpr := .add (149999, 2000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (143, 10000)
  let e15 : LowMeanIntegerExpr := .atom (13, 23)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (8, 13)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-13, 23) e15
  let e21 : LowMeanIntegerExpr := .add (10, 23) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (130, 529) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-8, 13) e17
  let e24 : LowMeanIntegerExpr := .add (5, 13) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (40, 169) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (130, 529) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (130, 529) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (1859, 529000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (31603, 529000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (142555471, 1058000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (573, 625)
  let e33 : LowMeanIntegerExpr := .pow (100000000000000000, 141050039560662968926103) e21 17
  let e34 : LowMeanIntegerExpr := .mul (91680000000000000, 141050039560662968926103) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-91680000000000000, 141050039560662968926103) e34
  let e36 : LowMeanIntegerExpr := .add (38010128216822197745782565897, 282100079121325937852206000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (38012949217613411005161087957, 282100079121325937852206000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-38010128216822197745782565897, 282100079121325937852206000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0395 : LowMeanDirectSeedInput :=
  { record := 395, positions := [{ j := 9, mode := 0, left := 848, right := 0 }, { j := 12, mode := 0, left := 849, right := 0 }, { j := 13, mode := 0, left := 850, right := 0 }, { j := 14, mode := 0, left := 851, right := 0 }], target := { R := 17, expr := lowMeanSeedTargetExpr0395 } }

noncomputable def lowMeanSeedTargetExpr0396 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (74161, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (1183, 500000)
  let e3 : LowMeanIntegerExpr := .atom (18, 1)
  let e4 : LowMeanIntegerExpr := .atom (14, 1)
  let e5 : LowMeanIntegerExpr := .neg (-14, 1) e4
  let e6 : LowMeanIntegerExpr := .add (4, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (1183, 125000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (669, 8000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1391, 2000000)
  let e10 : LowMeanIntegerExpr := .pow (16, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1391, 125000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1391, 125000) e11
  let e13 : LowMeanIntegerExpr := .add (72497, 1000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (143, 10000)
  let e15 : LowMeanIntegerExpr := .atom (13, 23)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (8, 13)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-13, 23) e15
  let e21 : LowMeanIntegerExpr := .add (10, 23) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (130, 529) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-8, 13) e17
  let e24 : LowMeanIntegerExpr := .add (5, 13) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (40, 169) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (130, 529) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (130, 529) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (1859, 529000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (16731, 264500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (71812913, 529000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (573, 625)
  let e33 : LowMeanIntegerExpr := .pow (1000000000000000000, 3244150909895248285300369) e21 18
  let e34 : LowMeanIntegerExpr := .mul (916800000000000000, 3244150909895248285300369) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-916800000000000000, 3244150909895248285300369) e34
  let e36 : LowMeanIntegerExpr := .add (440399701444193391730953833393, 3244150909895248285300369000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (440432142953292344213806837083, 3244150909895248285300369000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-440399701444193391730953833393, 3244150909895248285300369000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0396 : LowMeanDirectSeedInput :=
  { record := 396, positions := [{ j := 10, mode := 0, left := 852, right := 0 }, { j := 12, mode := 0, left := 853, right := 0 }, { j := 13, mode := 0, left := 854, right := 0 }, { j := 14, mode := 0, left := 855, right := 0 }], target := { R := 18, expr := lowMeanSeedTargetExpr0396 } }

noncomputable def lowMeanSeedTargetExpr0397 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (10473, 250000)
  let e2 : LowMeanIntegerExpr := .atom (5227, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (0, 1)
  let e4 : LowMeanIntegerExpr := .atom (69, 2)
  let e5 : LowMeanIntegerExpr := .neg (-69, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-69, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-360663, 20000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (477177, 20000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (3471, 50000000)
  let e10 : LowMeanIntegerExpr := .pow (4761, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (16525431, 200000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-16525431, 200000000) e11
  let e13 : LowMeanIntegerExpr := .add (-11753661, 200000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (1567, 500000)
  let e15 : LowMeanIntegerExpr := .atom (13, 23)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (8, 13)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-13, 23) e15
  let e21 : LowMeanIntegerExpr := .add (10, 23) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (130, 529) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-8, 13) e17
  let e24 : LowMeanIntegerExpr := .add (5, 13) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (40, 169) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (130, 529) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (130, 529) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (20371, 26450000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (0, 1) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-11753661, 200000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1171, 50)
  let e33 : LowMeanIntegerExpr := .pow (1, 1) e21 0
  let e34 : LowMeanIntegerExpr := .mul (1171, 50) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1171, 50) e34
  let e36 : LowMeanIntegerExpr := .add (-4695753661, 200000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-4695751661, 200000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (4695753661, 200000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0397 : LowMeanDirectSeedInput :=
  { record := 397, positions := [], target := { R := 0, expr := lowMeanSeedTargetExpr0397 } }

noncomputable def lowMeanSeedTargetExpr0398 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (10473, 250000)
  let e2 : LowMeanIntegerExpr := .atom (5227, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (1, 1)
  let e4 : LowMeanIntegerExpr := .atom (69, 2)
  let e5 : LowMeanIntegerExpr := .neg (-69, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-67, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-350209, 20000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (487631, 20000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (3471, 50000000)
  let e10 : LowMeanIntegerExpr := .pow (4489, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (15581319, 200000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-15581319, 200000000) e11
  let e13 : LowMeanIntegerExpr := .add (-10705009, 200000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (1567, 500000)
  let e15 : LowMeanIntegerExpr := .atom (13, 23)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (8, 13)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .neg (-13, 23) e15
  let e20 : LowMeanIntegerExpr := .add (10, 23) e3 e19
  let e21 : LowMeanIntegerExpr := .mul (130, 529) e15 e20
  let e22 : LowMeanIntegerExpr := .neg (-8, 13) e17
  let e23 : LowMeanIntegerExpr := .add (5, 13) e3 e22
  let e24 : LowMeanIntegerExpr := .mul (40, 169) e17 e23
  let e25 : LowMeanIntegerExpr := .maximum (130, 529) e21 e24
  let e26 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e25
  let e27 : LowMeanIntegerExpr := .selectLE (130, 529) e15 e16 e26 e25
  let e28 : LowMeanIntegerExpr := .mul (20371, 26450000) e14 e27
  let e29 : LowMeanIntegerExpr := .mul (20371, 26450000) e28 e3
  let e30 : LowMeanIntegerExpr := .add (-5581465761, 105800000000) e13 e29
  let e31 : LowMeanIntegerExpr := .atom (1171, 50)
  let e32 : LowMeanIntegerExpr := .pow (10, 23) e20 1
  let e33 : LowMeanIntegerExpr := .mul (1171, 115) e31 e32
  let e34 : LowMeanIntegerExpr := .neg (-1171, 115) e33
  let e35 : LowMeanIntegerExpr := .add (-1082901465761, 105800000000) e30 e34
  let e36 : LowMeanIntegerExpr := .add (-1082900407761, 105800000000) e0 e35
  let e37 : LowMeanIntegerExpr := .neg (1082901465761, 105800000000) e35
  let e38 : LowMeanIntegerExpr := .add (1, 100000) e36 e37
  e38

noncomputable def lowMeanSeedRecord0398 : LowMeanDirectSeedInput :=
  { record := 398, positions := [], target := { R := 1, expr := lowMeanSeedTargetExpr0398 } }

noncomputable def lowMeanSeedTargetExpr0399 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (10473, 250000)
  let e2 : LowMeanIntegerExpr := .atom (5227, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (2, 1)
  let e4 : LowMeanIntegerExpr := .atom (69, 2)
  let e5 : LowMeanIntegerExpr := .neg (-69, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-65, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-67951, 4000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (99617, 4000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (3471, 50000000)
  let e10 : LowMeanIntegerExpr := .pow (4225, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (586599, 8000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-586599, 8000000) e11
  let e13 : LowMeanIntegerExpr := .add (-77473, 1600000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (1567, 500000)
  let e15 : LowMeanIntegerExpr := .atom (13, 23)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (8, 13)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-13, 23) e15
  let e21 : LowMeanIntegerExpr := .add (10, 23) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (130, 529) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-8, 13) e17
  let e24 : LowMeanIntegerExpr := .add (5, 13) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (40, 169) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (130, 529) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (130, 529) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (20371, 26450000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (20371, 13225000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-39679473, 846400000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1171, 50)
  let e33 : LowMeanIntegerExpr := .pow (100, 529) e21 2
  let e34 : LowMeanIntegerExpr := .mul (2342, 529) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-2342, 529) e34
  let e36 : LowMeanIntegerExpr := .add (-3786879473, 846400000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-3786871009, 846400000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (3786879473, 846400000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0399 : LowMeanDirectSeedInput :=
  { record := 399, positions := [], target := { R := 2, expr := lowMeanSeedTargetExpr0399 } }

noncomputable def lowMeanSeedGroup0384 : List LowMeanDirectSeedInput := [lowMeanSeedRecord0384, lowMeanSeedRecord0385, lowMeanSeedRecord0386, lowMeanSeedRecord0387, lowMeanSeedRecord0388, lowMeanSeedRecord0389, lowMeanSeedRecord0390, lowMeanSeedRecord0391, lowMeanSeedRecord0392, lowMeanSeedRecord0393, lowMeanSeedRecord0394, lowMeanSeedRecord0395, lowMeanSeedRecord0396, lowMeanSeedRecord0397, lowMeanSeedRecord0398, lowMeanSeedRecord0399]

end Erdos993Lean.Analytic.V213
