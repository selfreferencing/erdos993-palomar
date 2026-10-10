module

public import Erdos993Lean.Analytic.V213.LowMeanCoreAll
public import Erdos993Lean.Analytic.V213.LowMeanData.Seed0272
public import Erdos993Lean.Analytic.V213.LowMeanFiberSeed
public import Erdos993Lean.Analytic.V213.LowMeanIntegerExpr
public import Erdos993Lean.Analytic.V213.LowMeanSeedGeometry
public import Erdos993Lean.Analytic.V213.LowMeanWidthData
public import Erdos993Lean.Ceiling.Prefix
public import Erdos993Lean.Ceiling.Statement

/-! Exact core/budget keys and equation-51 targets for the direct fibers. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanSeedTargetExpr0368 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (3013, 25000)
  let e2 : LowMeanIntegerExpr := .atom (-24, 15625)
  let e3 : LowMeanIntegerExpr := .atom (2, 1)
  let e4 : LowMeanIntegerExpr := .atom (8, 1)
  let e5 : LowMeanIntegerExpr := .neg (-8, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-6, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (144, 15625) e2 e6
  let e8 : LowMeanIntegerExpr := .add (16217, 125000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1591, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (36, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (14319, 250000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-14319, 250000) e11
  let e13 : LowMeanIntegerExpr := .add (3623, 50000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (2473, 50000)
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
  let e29 : LowMeanIntegerExpr := .mul (32149, 2645000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (32149, 1322500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (2559547, 26450000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (8933, 10000)
  let e33 : LowMeanIntegerExpr := .pow (100, 529) e21 2
  let e34 : LowMeanIntegerExpr := .mul (8933, 52900) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-8933, 52900) e34
  let e36 : LowMeanIntegerExpr := .add (-82911, 1150000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-165799, 2300000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (82911, 1150000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0368 : LowMeanDirectSeedInput :=
  { record := 368, positions := [{ j := 0, mode := 0, left := 811, right := 0 }], target := { R := 2, expr := lowMeanSeedTargetExpr0368 } }

noncomputable def lowMeanSeedTargetExpr0369 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (3013, 25000)
  let e2 : LowMeanIntegerExpr := .atom (-24, 15625)
  let e3 : LowMeanIntegerExpr := .atom (3, 1)
  let e4 : LowMeanIntegerExpr := .atom (8, 1)
  let e5 : LowMeanIntegerExpr := .neg (-8, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-5, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (24, 3125) e2 e6
  let e8 : LowMeanIntegerExpr := .add (641, 5000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1591, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (25, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1591, 40000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1591, 40000) e11
  let e13 : LowMeanIntegerExpr := .add (3537, 40000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (2473, 50000)
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
  let e29 : LowMeanIntegerExpr := .mul (32149, 2645000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (96447, 2645000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (2642649, 21160000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (8933, 10000)
  let e33 : LowMeanIntegerExpr := .pow (1000, 12167) e21 3
  let e34 : LowMeanIntegerExpr := .mul (8933, 121670) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-8933, 121670) e34
  let e36 : LowMeanIntegerExpr := .add (25048927, 486680000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (125268969, 2433400000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-25048927, 486680000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0369 : LowMeanDirectSeedInput :=
  { record := 369, positions := [], target := { R := 3, expr := lowMeanSeedTargetExpr0369 } }

noncomputable def lowMeanSeedTargetExpr0370 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (3013, 25000)
  let e2 : LowMeanIntegerExpr := .atom (-24, 15625)
  let e3 : LowMeanIntegerExpr := .atom (4, 1)
  let e4 : LowMeanIntegerExpr := .atom (8, 1)
  let e5 : LowMeanIntegerExpr := .neg (-8, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-4, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (96, 15625) e2 e6
  let e8 : LowMeanIntegerExpr := .add (15833, 125000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1591, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (16, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1591, 62500) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1591, 62500) e11
  let e13 : LowMeanIntegerExpr := .add (12651, 125000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (2473, 50000)
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
  let e29 : LowMeanIntegerExpr := .mul (32149, 2645000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (32149, 661250) e29 e3
  let e31 : LowMeanIntegerExpr := .add (9907279, 66125000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (8933, 10000)
  let e33 : LowMeanIntegerExpr := .pow (10000, 279841) e21 4
  let e34 : LowMeanIntegerExpr := .mul (8933, 279841) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-8933, 279841) e34
  let e36 : LowMeanIntegerExpr := .add (4124325591, 34980125000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (16498701569, 139920500000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-4124325591, 34980125000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0370 : LowMeanDirectSeedInput :=
  { record := 370, positions := [{ j := 1, mode := 0, left := 812, right := 0 }], target := { R := 4, expr := lowMeanSeedTargetExpr0370 } }

noncomputable def lowMeanSeedTargetExpr0371 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (3013, 25000)
  let e2 : LowMeanIntegerExpr := .atom (-24, 15625)
  let e3 : LowMeanIntegerExpr := .atom (5, 1)
  let e4 : LowMeanIntegerExpr := .atom (8, 1)
  let e5 : LowMeanIntegerExpr := .neg (-8, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-3, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (72, 15625) e2 e6
  let e8 : LowMeanIntegerExpr := .add (15641, 125000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1591, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (9, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (14319, 1000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-14319, 1000000) e11
  let e13 : LowMeanIntegerExpr := .add (110809, 1000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (2473, 50000)
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
  let e29 : LowMeanIntegerExpr := .mul (32149, 2645000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (32149, 529000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (90766961, 529000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (8933, 10000)
  let e33 : LowMeanIntegerExpr := .pow (100000, 6436343) e21 5
  let e34 : LowMeanIntegerExpr := .mul (89330, 6436343) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-89330, 6436343) e34
  let e36 : LowMeanIntegerExpr := .add (1015031614487, 6436343000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (1015095977917, 6436343000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-1015031614487, 6436343000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0371 : LowMeanDirectSeedInput :=
  { record := 371, positions := [{ j := 5, mode := 0, left := 813, right := 0 }], target := { R := 5, expr := lowMeanSeedTargetExpr0371 } }

noncomputable def lowMeanSeedTargetExpr0372 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (3013, 25000)
  let e2 : LowMeanIntegerExpr := .atom (-24, 15625)
  let e3 : LowMeanIntegerExpr := .atom (6, 1)
  let e4 : LowMeanIntegerExpr := .atom (8, 1)
  let e5 : LowMeanIntegerExpr := .neg (-8, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-2, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (48, 15625) e2 e6
  let e8 : LowMeanIntegerExpr := .add (15449, 125000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1591, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (4, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1591, 250000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1591, 250000) e11
  let e13 : LowMeanIntegerExpr := .add (29307, 250000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (2473, 50000)
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
  let e29 : LowMeanIntegerExpr := .mul (32149, 2645000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (96447, 1322500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (25148103, 132250000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (8933, 10000)
  let e33 : LowMeanIntegerExpr := .pow (1000000, 148035889) e21 6
  let e34 : LowMeanIntegerExpr := .mul (893300, 148035889) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-893300, 148035889) e34
  let e36 : LowMeanIntegerExpr := .add (6814145291623, 37008972250000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (13629030762691, 74017944500000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-6814145291623, 37008972250000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0372 : LowMeanDirectSeedInput :=
  { record := 372, positions := [{ j := 6, mode := 0, left := 814, right := 0 }], target := { R := 6, expr := lowMeanSeedTargetExpr0372 } }

noncomputable def lowMeanSeedTargetExpr0373 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (3013, 25000)
  let e2 : LowMeanIntegerExpr := .atom (-24, 15625)
  let e3 : LowMeanIntegerExpr := .atom (7, 1)
  let e4 : LowMeanIntegerExpr := .atom (8, 1)
  let e5 : LowMeanIntegerExpr := .neg (-8, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-1, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (24, 15625) e2 e6
  let e8 : LowMeanIntegerExpr := .add (15257, 125000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1591, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (1, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1591, 1000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1591, 1000000) e11
  let e13 : LowMeanIntegerExpr := .add (24093, 200000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (2473, 50000)
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
  let e29 : LowMeanIntegerExpr := .mul (32149, 2645000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (225043, 2645000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (21746917, 105800000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (8933, 10000)
  let e33 : LowMeanIntegerExpr := .pow (10000000, 3404825447) e21 7
  let e34 : LowMeanIntegerExpr := .mul (8933000, 3404825447) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-8933000, 3404825447) e34
  let e36 : LowMeanIntegerExpr := .add (138184017004531, 680965089400000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (5527633066217, 27238603576000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-138184017004531, 680965089400000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0373 : LowMeanDirectSeedInput :=
  { record := 373, positions := [{ j := 6, mode := 0, left := 815, right := 0 }], target := { R := 7, expr := lowMeanSeedTargetExpr0373 } }

noncomputable def lowMeanSeedTargetExpr0374 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (3013, 25000)
  let e2 : LowMeanIntegerExpr := .atom (-24, 15625)
  let e3 : LowMeanIntegerExpr := .atom (8, 1)
  let e4 : LowMeanIntegerExpr := .neg (-8, 1) e3
  let e5 : LowMeanIntegerExpr := .add (0, 1) e3 e4
  let e6 : LowMeanIntegerExpr := .mul (0, 1) e2 e5
  let e7 : LowMeanIntegerExpr := .add (3013, 25000) e1 e6
  let e8 : LowMeanIntegerExpr := .atom (1591, 1000000)
  let e9 : LowMeanIntegerExpr := .pow (0, 1) e5 2
  let e10 : LowMeanIntegerExpr := .mul (0, 1) e8 e9
  let e11 : LowMeanIntegerExpr := .neg (0, 1) e10
  let e12 : LowMeanIntegerExpr := .add (3013, 25000) e7 e11
  let e13 : LowMeanIntegerExpr := .atom (2473, 50000)
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
  let e28 : LowMeanIntegerExpr := .mul (32149, 2645000) e13 e27
  let e29 : LowMeanIntegerExpr := .mul (32149, 330625) e28 e3
  let e30 : LowMeanIntegerExpr := .add (2879837, 13225000) e12 e29
  let e31 : LowMeanIntegerExpr := .atom (8933, 10000)
  let e32 : LowMeanIntegerExpr := .pow (100000000, 78310985281) e20 8
  let e33 : LowMeanIntegerExpr := .mul (89330000, 78310985281) e31 e32
  let e34 : LowMeanIntegerExpr := .neg (-89330000, 78310985281) e33
  let e35 : LowMeanIntegerExpr := .add (424085980470093, 1957774632025000) e30 e34
  let e36 : LowMeanIntegerExpr := .add (1696422232865653, 7831098528100000) e0 e35
  let e37 : LowMeanIntegerExpr := .neg (-424085980470093, 1957774632025000) e35
  let e38 : LowMeanIntegerExpr := .add (1, 100000) e36 e37
  e38

noncomputable def lowMeanSeedRecord0374 : LowMeanDirectSeedInput :=
  { record := 374, positions := [{ j := 4, mode := 0, left := 816, right := 0 }, { j := 7, mode := 0, left := 817, right := 0 }], target := { R := 8, expr := lowMeanSeedTargetExpr0374 } }

noncomputable def lowMeanSeedTargetExpr0375 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (3013, 25000)
  let e2 : LowMeanIntegerExpr := .atom (-24, 15625)
  let e3 : LowMeanIntegerExpr := .atom (9, 1)
  let e4 : LowMeanIntegerExpr := .atom (8, 1)
  let e5 : LowMeanIntegerExpr := .neg (-8, 1) e4
  let e6 : LowMeanIntegerExpr := .add (1, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-24, 15625) e2 e6
  let e8 : LowMeanIntegerExpr := .add (14873, 125000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1591, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (1, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1591, 1000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1591, 1000000) e11
  let e13 : LowMeanIntegerExpr := .add (117393, 1000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (2473, 50000)
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
  let e29 : LowMeanIntegerExpr := .mul (32149, 2645000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (289341, 2645000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (119969097, 529000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (8933, 10000)
  let e33 : LowMeanIntegerExpr := .pow (1000000000, 1801152661463) e21 9
  let e34 : LowMeanIntegerExpr := .mul (893300000, 1801152661463) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-893300000, 1801152661463) e34
  let e36 : LowMeanIntegerExpr := .add (407580534319211359, 1801152661463000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (407598545845825989, 1801152661463000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-407580534319211359, 1801152661463000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0375 : LowMeanDirectSeedInput :=
  { record := 375, positions := [{ j := 5, mode := 0, left := 818, right := 0 }, { j := 7, mode := 0, left := 819, right := 0 }], target := { R := 9, expr := lowMeanSeedTargetExpr0375 } }

noncomputable def lowMeanSeedTargetExpr0376 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (3013, 25000)
  let e2 : LowMeanIntegerExpr := .atom (-24, 15625)
  let e3 : LowMeanIntegerExpr := .atom (10, 1)
  let e4 : LowMeanIntegerExpr := .atom (8, 1)
  let e5 : LowMeanIntegerExpr := .neg (-8, 1) e4
  let e6 : LowMeanIntegerExpr := .add (2, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-48, 15625) e2 e6
  let e8 : LowMeanIntegerExpr := .add (14681, 125000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1591, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (4, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1591, 250000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1591, 250000) e11
  let e13 : LowMeanIntegerExpr := .add (27771, 250000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (2473, 50000)
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
  let e29 : LowMeanIntegerExpr := .mul (32149, 2645000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (32149, 264500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (30765359, 132250000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (8933, 10000)
  let e33 : LowMeanIntegerExpr := .pow (10000000000, 41426511213649) e21 10
  let e34 : LowMeanIntegerExpr := .mul (8933000000, 41426511213649) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-8933000000, 41426511213649) e34
  let e36 : LowMeanIntegerExpr := .add (2407032325813680879, 10356627803412250000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (4814271784183430003, 20713255606824500000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-2407032325813680879, 10356627803412250000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0376 : LowMeanDirectSeedInput :=
  { record := 376, positions := [{ j := 7, mode := 0, left := 820, right := 0 }, { j := 8, mode := 0, left := 821, right := 0 }], target := { R := 10, expr := lowMeanSeedTargetExpr0376 } }

noncomputable def lowMeanSeedTargetExpr0377 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (3013, 25000)
  let e2 : LowMeanIntegerExpr := .atom (-24, 15625)
  let e3 : LowMeanIntegerExpr := .atom (11, 1)
  let e4 : LowMeanIntegerExpr := .atom (8, 1)
  let e5 : LowMeanIntegerExpr := .neg (-8, 1) e4
  let e6 : LowMeanIntegerExpr := .add (3, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-72, 15625) e2 e6
  let e8 : LowMeanIntegerExpr := .add (14489, 125000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1591, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (9, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (14319, 1000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-14319, 1000000) e11
  let e13 : LowMeanIntegerExpr := .add (101593, 1000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (2473, 50000)
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
  let e29 : LowMeanIntegerExpr := .mul (32149, 2645000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (353639, 2645000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (124470497, 529000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (8933, 10000)
  let e33 : LowMeanIntegerExpr := .pow (100000000000, 952809757913927) e21 11
  let e34 : LowMeanIntegerExpr := .mul (89330000000, 952809757913927) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-89330000000, 952809757913927) e34
  let e36 : LowMeanIntegerExpr := .add (224101036945172357111, 952809757913927000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (224110565042751496381, 952809757913927000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-224101036945172357111, 952809757913927000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0377 : LowMeanDirectSeedInput :=
  { record := 377, positions := [{ j := 6, mode := 0, left := 822, right := 0 }, { j := 8, mode := 0, left := 823, right := 0 }], target := { R := 11, expr := lowMeanSeedTargetExpr0377 } }

noncomputable def lowMeanSeedTargetExpr0378 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (74161, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (1183, 500000)
  let e3 : LowMeanIntegerExpr := .atom (0, 1)
  let e4 : LowMeanIntegerExpr := .atom (14, 1)
  let e5 : LowMeanIntegerExpr := .neg (-14, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-14, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-8281, 250000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (41037, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1391, 2000000)
  let e10 : LowMeanIntegerExpr := .pow (196, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (68159, 500000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-68159, 500000) e11
  let e13 : LowMeanIntegerExpr := .add (-95281, 1000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (0, 1) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-95281, 1000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (573, 625)
  let e33 : LowMeanIntegerExpr := .pow (1, 1) e21 0
  let e34 : LowMeanIntegerExpr := .mul (573, 625) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-573, 625) e34
  let e36 : LowMeanIntegerExpr := .add (-1012081, 1000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-1012071, 1000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (1012081, 1000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0378 : LowMeanDirectSeedInput :=
  { record := 378, positions := [], target := { R := 0, expr := lowMeanSeedTargetExpr0378 } }

noncomputable def lowMeanSeedTargetExpr0379 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (74161, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (1183, 500000)
  let e3 : LowMeanIntegerExpr := .atom (1, 1)
  let e4 : LowMeanIntegerExpr := .atom (14, 1)
  let e5 : LowMeanIntegerExpr := .neg (-14, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-13, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-15379, 500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (43403, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1391, 2000000)
  let e10 : LowMeanIntegerExpr := .pow (169, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (235079, 2000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-235079, 2000000) e11
  let e13 : LowMeanIntegerExpr := .add (-148273, 2000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (143, 10000)
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
  let e28 : LowMeanIntegerExpr := .mul (1859, 529000) e14 e27
  let e29 : LowMeanIntegerExpr := .mul (1859, 529000) e28 e3
  let e30 : LowMeanIntegerExpr := .add (-74718417, 1058000000) e13 e29
  let e31 : LowMeanIntegerExpr := .atom (573, 625)
  let e32 : LowMeanIntegerExpr := .pow (10, 23) e20 1
  let e33 : LowMeanIntegerExpr := .mul (1146, 2875) e31 e32
  let e34 : LowMeanIntegerExpr := .neg (-1146, 2875) e33
  let e35 : LowMeanIntegerExpr := .add (-496446417, 1058000000) e30 e34
  let e36 : LowMeanIntegerExpr := .add (-496435837, 1058000000) e0 e35
  let e37 : LowMeanIntegerExpr := .neg (496446417, 1058000000) e35
  let e38 : LowMeanIntegerExpr := .add (1, 100000) e36 e37
  e38

noncomputable def lowMeanSeedRecord0379 : LowMeanDirectSeedInput :=
  { record := 379, positions := [], target := { R := 1, expr := lowMeanSeedTargetExpr0379 } }

noncomputable def lowMeanSeedTargetExpr0380 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (74161, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (1183, 500000)
  let e3 : LowMeanIntegerExpr := .atom (2, 1)
  let e4 : LowMeanIntegerExpr := .atom (14, 1)
  let e5 : LowMeanIntegerExpr := .neg (-14, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-12, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-3549, 125000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (45769, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1391, 2000000)
  let e10 : LowMeanIntegerExpr := .pow (144, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (12519, 125000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-12519, 125000) e11
  let e13 : LowMeanIntegerExpr := .add (-54383, 1000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (1859, 264500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-25050607, 529000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (573, 625)
  let e33 : LowMeanIntegerExpr := .pow (100, 529) e21 2
  let e34 : LowMeanIntegerExpr := .mul (2292, 13225) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-2292, 13225) e34
  let e36 : LowMeanIntegerExpr := .add (-116730607, 529000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-116725317, 529000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (116730607, 529000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0380 : LowMeanDirectSeedInput :=
  { record := 380, positions := [], target := { R := 2, expr := lowMeanSeedTargetExpr0380 } }

noncomputable def lowMeanSeedTargetExpr0381 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (74161, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (1183, 500000)
  let e3 : LowMeanIntegerExpr := .atom (3, 1)
  let e4 : LowMeanIntegerExpr := .atom (14, 1)
  let e5 : LowMeanIntegerExpr := .neg (-14, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-11, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-13013, 500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (9627, 200000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1391, 2000000)
  let e10 : LowMeanIntegerExpr := .pow (121, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (168311, 2000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-168311, 2000000) e11
  let e13 : LowMeanIntegerExpr := .add (-72041, 2000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (5577, 529000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-26955689, 1058000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (573, 625)
  let e33 : LowMeanIntegerExpr := .pow (1000, 12167) e21 3
  let e34 : LowMeanIntegerExpr := .mul (4584, 60835) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-4584, 60835) e34
  let e36 : LowMeanIntegerExpr := .add (-2453580847, 24334000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-2453337507, 24334000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (2453580847, 24334000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0381 : LowMeanDirectSeedInput :=
  { record := 381, positions := [{ j := 0, mode := 0, left := 824, right := 0 }], target := { R := 3, expr := lowMeanSeedTargetExpr0381 } }

noncomputable def lowMeanSeedTargetExpr0382 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (74161, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (1183, 500000)
  let e3 : LowMeanIntegerExpr := .atom (4, 1)
  let e4 : LowMeanIntegerExpr := .atom (14, 1)
  let e5 : LowMeanIntegerExpr := .neg (-14, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-10, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1183, 50000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (50501, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1391, 2000000)
  let e10 : LowMeanIntegerExpr := .pow (100, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1391, 20000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1391, 20000) e11
  let e13 : LowMeanIntegerExpr := .add (-19049, 1000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (1859, 132250) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-2640921, 529000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (573, 625)
  let e33 : LowMeanIntegerExpr := .pow (10000, 279841) e21 4
  let e34 : LowMeanIntegerExpr := .mul (9168, 279841) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-9168, 279841) e34
  let e36 : LowMeanIntegerExpr := .add (-10565047209, 279841000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-10562248799, 279841000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (10565047209, 279841000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0382 : LowMeanDirectSeedInput :=
  { record := 382, positions := [{ j := 1, mode := 0, left := 825, right := 0 }], target := { R := 4, expr := lowMeanSeedTargetExpr0382 } }

noncomputable def lowMeanSeedTargetExpr0383 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (74161, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (1183, 500000)
  let e3 : LowMeanIntegerExpr := .atom (5, 1)
  let e4 : LowMeanIntegerExpr := .atom (14, 1)
  let e5 : LowMeanIntegerExpr := .neg (-14, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-9, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-10647, 500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (52867, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1391, 2000000)
  let e10 : LowMeanIntegerExpr := .pow (81, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (112671, 2000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-112671, 2000000) e11
  let e13 : LowMeanIntegerExpr := .add (-6937, 2000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (1859, 105800) e29 e3
  let e31 : LowMeanIntegerExpr := .add (14920327, 1058000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (573, 625)
  let e33 : LowMeanIntegerExpr := .pow (100000, 6436343) e21 5
  let e34 : LowMeanIntegerExpr := .mul (91680, 6436343) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-91680, 6436343) e34
  let e36 : LowMeanIntegerExpr := .add (-1824381391, 12872686000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-1695654531, 12872686000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (1824381391, 12872686000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0383 : LowMeanDirectSeedInput :=
  { record := 383, positions := [{ j := 1, mode := 0, left := 826, right := 0 }], target := { R := 5, expr := lowMeanSeedTargetExpr0383 } }

noncomputable def lowMeanSeedGroup0368 : List LowMeanDirectSeedInput := [lowMeanSeedRecord0368, lowMeanSeedRecord0369, lowMeanSeedRecord0370, lowMeanSeedRecord0371, lowMeanSeedRecord0372, lowMeanSeedRecord0373, lowMeanSeedRecord0374, lowMeanSeedRecord0375, lowMeanSeedRecord0376, lowMeanSeedRecord0377, lowMeanSeedRecord0378, lowMeanSeedRecord0379, lowMeanSeedRecord0380, lowMeanSeedRecord0381, lowMeanSeedRecord0382, lowMeanSeedRecord0383]

end Erdos993Lean.Analytic.V213
