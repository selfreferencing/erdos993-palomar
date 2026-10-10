module

public import Erdos993Lean.Analytic.V213.LowMeanCoreAll
public import Erdos993Lean.Analytic.V213.LowMeanData.Seed0288
public import Erdos993Lean.Analytic.V213.LowMeanFiberSeed
public import Erdos993Lean.Analytic.V213.LowMeanIntegerExpr
public import Erdos993Lean.Analytic.V213.LowMeanSeedGeometry
public import Erdos993Lean.Analytic.V213.LowMeanWidthData
public import Erdos993Lean.Ceiling.Prefix
public import Erdos993Lean.Ceiling.Statement

/-! Exact core/budget keys and equation-51 targets for the direct fibers. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanSeedTargetExpr0400 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (10473, 250000)
  let e2 : LowMeanIntegerExpr := .atom (5227, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (3, 1)
  let e4 : LowMeanIntegerExpr := .atom (69, 2)
  let e5 : LowMeanIntegerExpr := .neg (-69, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-63, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-329301, 20000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (508539, 20000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (3471, 50000000)
  let e10 : LowMeanIntegerExpr := .pow (3969, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (13776399, 200000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-13776399, 200000000) e11
  let e13 : LowMeanIntegerExpr := .add (-8691009, 200000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (61113, 26450000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-4353091761, 105800000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1171, 50)
  let e33 : LowMeanIntegerExpr := .pow (1000, 12167) e21 3
  let e34 : LowMeanIntegerExpr := .mul (23420, 12167) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-23420, 12167) e34
  let e36 : LowMeanIntegerExpr := .add (-4784121110503, 2433400000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-4784096776503, 2433400000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (4784121110503, 2433400000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0400 : LowMeanDirectSeedInput :=
  { record := 400, positions := [], target := { R := 3, expr := lowMeanSeedTargetExpr0400 } }

noncomputable def lowMeanSeedTargetExpr0401 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (10473, 250000)
  let e2 : LowMeanIntegerExpr := .atom (5227, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (4, 1)
  let e4 : LowMeanIntegerExpr := .atom (69, 2)
  let e5 : LowMeanIntegerExpr := .neg (-69, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-61, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-318847, 20000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (518993, 20000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (3471, 50000000)
  let e10 : LowMeanIntegerExpr := .pow (3721, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (12915591, 200000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-12915591, 200000000) e11
  let e13 : LowMeanIntegerExpr := .add (-7725661, 200000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (20371, 6612500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-3760938669, 105800000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1171, 50)
  let e33 : LowMeanIntegerExpr := .pow (10000, 279841) e21 4
  let e34 : LowMeanIntegerExpr := .mul (234200, 279841) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-234200, 279841) e34
  let e36 : LowMeanIntegerExpr := .add (-48829536555901, 55968200000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-48828976873901, 55968200000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (48829536555901, 55968200000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0401 : LowMeanDirectSeedInput :=
  { record := 401, positions := [], target := { R := 4, expr := lowMeanSeedTargetExpr0401 } }

noncomputable def lowMeanSeedTargetExpr0402 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (10473, 250000)
  let e2 : LowMeanIntegerExpr := .atom (5227, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (5, 1)
  let e4 : LowMeanIntegerExpr := .atom (69, 2)
  let e5 : LowMeanIntegerExpr := .neg (-69, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-59, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-308393, 20000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (529447, 20000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (3471, 50000000)
  let e10 : LowMeanIntegerExpr := .pow (3481, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (12082551, 200000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-12082551, 200000000) e11
  let e13 : LowMeanIntegerExpr := .add (-6788081, 200000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (20371, 5290000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-3183474849, 105800000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1171, 50)
  let e33 : LowMeanIntegerExpr := .pow (100000, 6436343) e21 5
  let e34 : LowMeanIntegerExpr := .mul (2342000, 6436343) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-2342000, 6436343) e34
  let e36 : LowMeanIntegerExpr := .add (-507133338487783, 1287268600000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-507120465801783, 1287268600000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (507133338487783, 1287268600000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0402 : LowMeanDirectSeedInput :=
  { record := 402, positions := [], target := { R := 5, expr := lowMeanSeedTargetExpr0402 } }

noncomputable def lowMeanSeedTargetExpr0403 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (10473, 250000)
  let e2 : LowMeanIntegerExpr := .atom (5227, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (6, 1)
  let e4 : LowMeanIntegerExpr := .atom (69, 2)
  let e5 : LowMeanIntegerExpr := .neg (-69, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-57, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-297939, 20000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (539901, 20000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (3471, 50000000)
  let e10 : LowMeanIntegerExpr := .pow (3249, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (11277279, 200000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-11277279, 200000000) e11
  let e13 : LowMeanIntegerExpr := .add (-5878269, 200000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (61113, 13225000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-2620700301, 105800000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1171, 50)
  let e33 : LowMeanIntegerExpr := .pow (1000000, 148035889) e21 6
  let e34 : LowMeanIntegerExpr := .mul (23420000, 148035889) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-23420000, 148035889) e34
  let e36 : LowMeanIntegerExpr := .add (-5417379392932141, 29607177800000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-5417083321154141, 29607177800000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (5417379392932141, 29607177800000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0403 : LowMeanDirectSeedInput :=
  { record := 403, positions := [], target := { R := 6, expr := lowMeanSeedTargetExpr0403 } }

noncomputable def lowMeanSeedTargetExpr0404 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (10473, 250000)
  let e2 : LowMeanIntegerExpr := .atom (5227, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (7, 1)
  let e4 : LowMeanIntegerExpr := .atom (69, 2)
  let e5 : LowMeanIntegerExpr := .neg (-69, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-55, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-57497, 4000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (110071, 4000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (3471, 50000000)
  let e10 : LowMeanIntegerExpr := .pow (3025, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (419991, 8000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-419991, 8000000) e11
  let e13 : LowMeanIntegerExpr := .add (-199849, 8000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (142597, 26450000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-82904601, 4232000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1171, 50)
  let e33 : LowMeanIntegerExpr := .pow (10000000, 3404825447) e21 7
  let e34 : LowMeanIntegerExpr := .mul (234200000, 3404825447) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-234200000, 3404825447) e34
  let e36 : LowMeanIntegerExpr := .add (-2407202448314143, 27238603576000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-2406930062278383, 27238603576000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (2407202448314143, 27238603576000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0404 : LowMeanDirectSeedInput :=
  { record := 404, positions := [{ j := 2, mode := 0, left := 856, right := 0 }], target := { R := 7, expr := lowMeanSeedTargetExpr0404 } }

noncomputable def lowMeanSeedTargetExpr0405 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (10473, 250000)
  let e2 : LowMeanIntegerExpr := .atom (5227, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (8, 1)
  let e4 : LowMeanIntegerExpr := .atom (69, 2)
  let e5 : LowMeanIntegerExpr := .neg (-69, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-53, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-277031, 20000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (560809, 20000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (3471, 50000000)
  let e10 : LowMeanIntegerExpr := .pow (2809, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (9750039, 200000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-9750039, 200000000) e11
  let e13 : LowMeanIntegerExpr := .add (-4141949, 200000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (20371, 3306250) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-1539219021, 105800000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1171, 50)
  let e33 : LowMeanIntegerExpr := .pow (100000000, 78310985281) e21 8
  let e34 : LowMeanIntegerExpr := .mul (2342000000, 78310985281) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-2342000000, 78310985281) e34
  let e36 : LowMeanIntegerExpr := .add (-696259656139444669, 15662197056200000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-696103034168882669, 15662197056200000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (696259656139444669, 15662197056200000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0405 : LowMeanDirectSeedInput :=
  { record := 405, positions := [{ j := 3, mode := 0, left := 857, right := 0 }], target := { R := 8, expr := lowMeanSeedTargetExpr0405 } }

noncomputable def lowMeanSeedTargetExpr0406 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (10473, 250000)
  let e2 : LowMeanIntegerExpr := .atom (5227, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (9, 1)
  let e4 : LowMeanIntegerExpr := .atom (69, 2)
  let e5 : LowMeanIntegerExpr := .neg (-69, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-51, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-266577, 20000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (571263, 20000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (3471, 50000000)
  let e10 : LowMeanIntegerExpr := .pow (2601, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (9028071, 200000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-9028071, 200000000) e11
  let e13 : LowMeanIntegerExpr := .add (-3315441, 200000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (183339, 26450000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-1020512289, 105800000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1171, 50)
  let e33 : LowMeanIntegerExpr := .pow (1000000000, 1801152661463) e21 9
  let e34 : LowMeanIntegerExpr := .mul (23420000000, 1801152661463) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-23420000000, 1801152661463) e34
  let e36 : LowMeanIntegerExpr := .add (-8158666210563418183, 360230532292600000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-8155063905240492183, 360230532292600000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (8158666210563418183, 360230532292600000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0406 : LowMeanDirectSeedInput :=
  { record := 406, positions := [{ j := 3, mode := 0, left := 858, right := 0 }], target := { R := 9, expr := lowMeanSeedTargetExpr0406 } }

noncomputable def lowMeanSeedTargetExpr0407 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (10473, 250000)
  let e2 : LowMeanIntegerExpr := .atom (5227, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (10, 1)
  let e4 : LowMeanIntegerExpr := .atom (69, 2)
  let e5 : LowMeanIntegerExpr := .neg (-69, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-49, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-256123, 20000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (581717, 20000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (3471, 50000000)
  let e10 : LowMeanIntegerExpr := .pow (2401, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (8333871, 200000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-8333871, 200000000) e11
  let e13 : LowMeanIntegerExpr := .add (-2516701, 200000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (20371, 2645000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-516494829, 105800000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1171, 50)
  let e33 : LowMeanIntegerExpr := .pow (10000000000, 41426511213649) e21 10
  let e34 : LowMeanIntegerExpr := .mul (234200000000, 41426511213649) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-234200000000, 41426511213649) e34
  let e36 : LowMeanIntegerExpr := .add (-87287218951531611949, 8285302242729800000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-87204365929104313949, 8285302242729800000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (87287218951531611949, 8285302242729800000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0407 : LowMeanDirectSeedInput :=
  { record := 407, positions := [{ j := 4, mode := 0, left := 859, right := 0 }], target := { R := 10, expr := lowMeanSeedTargetExpr0407 } }

noncomputable def lowMeanSeedTargetExpr0408 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (10473, 250000)
  let e2 : LowMeanIntegerExpr := .atom (5227, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (11, 1)
  let e4 : LowMeanIntegerExpr := .atom (69, 2)
  let e5 : LowMeanIntegerExpr := .neg (-69, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-47, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-245669, 20000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (592171, 20000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (3471, 50000000)
  let e10 : LowMeanIntegerExpr := .pow (2209, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (7667439, 200000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-7667439, 200000000) e11
  let e13 : LowMeanIntegerExpr := .add (-1745729, 200000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (224081, 26450000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-27166641, 105800000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1171, 50)
  let e33 : LowMeanIntegerExpr := .pow (100000000000, 952809757913927) e21 11
  let e34 : LowMeanIntegerExpr := .mul (2342000000000, 952809757913927) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-2342000000000, 952809757913927) e34
  let e36 : LowMeanIntegerExpr := .add (-517331267740159855783, 190561951582785400000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-515425648224332001783, 190561951582785400000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (517331267740159855783, 190561951582785400000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0408 : LowMeanDirectSeedInput :=
  { record := 408, positions := [{ j := 4, mode := 0, left := 860, right := 0 }], target := { R := 11, expr := lowMeanSeedTargetExpr0408 } }

noncomputable def lowMeanSeedTargetExpr0409 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (10473, 250000)
  let e2 : LowMeanIntegerExpr := .atom (5227, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (12, 1)
  let e4 : LowMeanIntegerExpr := .atom (69, 2)
  let e5 : LowMeanIntegerExpr := .neg (-69, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-45, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-47043, 4000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (4821, 160000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (3471, 50000000)
  let e10 : LowMeanIntegerExpr := .pow (2025, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (281151, 8000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-281151, 8000000) e11
  let e13 : LowMeanIntegerExpr := .add (-40101, 8000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (61113, 6612500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (17898891, 4232000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1171, 50)
  let e33 : LowMeanIntegerExpr := .pow (1000000000000, 21914624432020321) e21 12
  let e34 : LowMeanIntegerExpr := .mul (23420000000000, 21914624432020321) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-23420000000000, 21914624432020321) e34
  let e36 : LowMeanIntegerExpr := .add (554128608723381163259, 175316995456162568000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (555881778677942788939, 175316995456162568000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-554128608723381163259, 175316995456162568000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0409 : LowMeanDirectSeedInput :=
  { record := 409, positions := [{ j := 5, mode := 0, left := 861, right := 0 }], target := { R := 12, expr := lowMeanSeedTargetExpr0409 } }

noncomputable def lowMeanSeedTargetExpr0410 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (10473, 250000)
  let e2 : LowMeanIntegerExpr := .atom (5227, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (13, 1)
  let e4 : LowMeanIntegerExpr := .atom (69, 2)
  let e5 : LowMeanIntegerExpr := .neg (-69, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-43, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-224761, 20000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (613079, 20000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (3471, 50000000)
  let e10 : LowMeanIntegerExpr := .pow (1849, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (6417879, 200000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-6417879, 200000000) e11
  let e13 : LowMeanIntegerExpr := .add (-287089, 200000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (264823, 26450000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (907421919, 105800000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1171, 50)
  let e33 : LowMeanIntegerExpr := .pow (10000000000000, 504036361936467383) e21 13
  let e34 : LowMeanIntegerExpr := .mul (234200000000000, 504036361936467383) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-234200000000000, 504036361936467383) e34
  let e36 : LowMeanIntegerExpr := .add (817760458968181075165913, 100807272387293476600000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (818768531692054009931913, 100807272387293476600000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-817760458968181075165913, 100807272387293476600000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0410 : LowMeanDirectSeedInput :=
  { record := 410, positions := [], target := { R := 13, expr := lowMeanSeedTargetExpr0410 } }

noncomputable def lowMeanSeedTargetExpr0411 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (10473, 250000)
  let e2 : LowMeanIntegerExpr := .atom (5227, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (14, 1)
  let e4 : LowMeanIntegerExpr := .atom (69, 2)
  let e5 : LowMeanIntegerExpr := .neg (-69, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-41, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-214307, 20000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (623533, 20000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (3471, 50000000)
  let e10 : LowMeanIntegerExpr := .pow (1681, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (5834751, 200000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-5834751, 200000000) e11
  let e13 : LowMeanIntegerExpr := .add (400579, 200000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (142597, 13225000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (1352682291, 105800000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1171, 50)
  let e33 : LowMeanIntegerExpr := .pow (100000000000000, 11592836324538749809) e21 14
  let e34 : LowMeanIntegerExpr := .mul (2342000000000000, 11592836324538749809) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-2342000000000000, 11592836324538749809) e34
  let e36 : LowMeanIntegerExpr := .add (29175124383109821568835411, 2318567264907749961800000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (29198310055758899068453411, 2318567264907749961800000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-29175124383109821568835411, 2318567264907749961800000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0411 : LowMeanDirectSeedInput :=
  { record := 411, positions := [], target := { R := 14, expr := lowMeanSeedTargetExpr0411 } }

noncomputable def lowMeanSeedTargetExpr0412 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (10473, 250000)
  let e2 : LowMeanIntegerExpr := .atom (5227, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (15, 1)
  let e4 : LowMeanIntegerExpr := .atom (69, 2)
  let e5 : LowMeanIntegerExpr := .neg (-69, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-39, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-203853, 20000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (633987, 20000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (3471, 50000000)
  let e10 : LowMeanIntegerExpr := .pow (1521, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (5279391, 200000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-5279391, 200000000) e11
  let e13 : LowMeanIntegerExpr := .add (1060479, 200000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (61113, 5290000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (1783253391, 105800000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1171, 50)
  let e33 : LowMeanIntegerExpr := .pow (1000000000000000, 266635235464391245607) e21 15
  let e34 : LowMeanIntegerExpr := .mul (23420000000000000, 266635235464391245607) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-23420000000000000, 266635235464391245607) e34
  let e36 : LowMeanIntegerExpr := .add (894140551610508787295645753, 53327047092878249121400000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (894673822081437569786859753, 53327047092878249121400000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-894140551610508787295645753, 53327047092878249121400000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0412 : LowMeanDirectSeedInput :=
  { record := 412, positions := [], target := { R := 15, expr := lowMeanSeedTargetExpr0412 } }

noncomputable def lowMeanSeedTargetExpr0413 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (10473, 250000)
  let e2 : LowMeanIntegerExpr := .atom (5227, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (16, 1)
  let e4 : LowMeanIntegerExpr := .atom (69, 2)
  let e5 : LowMeanIntegerExpr := .neg (-69, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-37, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-193399, 20000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (644441, 20000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (3471, 50000000)
  let e10 : LowMeanIntegerExpr := .pow (1369, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (4751799, 200000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-4751799, 200000000) e11
  let e13 : LowMeanIntegerExpr := .add (1692611, 200000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (20371, 1653125) e29 e3
  let e31 : LowMeanIntegerExpr := .add (2199135219, 105800000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1171, 50)
  let e33 : LowMeanIntegerExpr := .pow (10000000000000000, 6132610415680998648961) e21 16
  let e34 : LowMeanIntegerExpr := .mul (234200000000000000, 6132610415680998648961) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-234200000000000000, 6132610415680998648961) e34
  let e36 : LowMeanIntegerExpr := .add (25447374649395678635201423171, 1226522083136199729792200000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (25459639870227040632499345171, 1226522083136199729792200000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-25447374649395678635201423171, 1226522083136199729792200000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0413 : LowMeanDirectSeedInput :=
  { record := 413, positions := [], target := { R := 16, expr := lowMeanSeedTargetExpr0413 } }

noncomputable def lowMeanSeedTargetExpr0414 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (10473, 250000)
  let e2 : LowMeanIntegerExpr := .atom (5227, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (17, 1)
  let e4 : LowMeanIntegerExpr := .atom (69, 2)
  let e5 : LowMeanIntegerExpr := .neg (-69, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-35, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-36589, 4000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (130979, 4000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (3471, 50000000)
  let e10 : LowMeanIntegerExpr := .pow (1225, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (170079, 8000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-170079, 8000000) e11
  let e13 : LowMeanIntegerExpr := .add (91879, 8000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (346307, 26450000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (104013111, 4232000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1171, 50)
  let e33 : LowMeanIntegerExpr := .pow (100000000000000000, 141050039560662968926103) e21 17
  let e34 : LowMeanIntegerExpr := .mul (2342000000000000000, 141050039560662968926103) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-2342000000000000000, 141050039560662968926103) e34
  let e36 : LowMeanIntegerExpr := .add (27714824342868863176749153377, 1128400316485303751408824000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (27726108346033716214263241617, 1128400316485303751408824000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-27714824342868863176749153377, 1128400316485303751408824000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0414 : LowMeanDirectSeedInput :=
  { record := 414, positions := [], target := { R := 17, expr := lowMeanSeedTargetExpr0414 } }

noncomputable def lowMeanSeedTargetExpr0415 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (10473, 250000)
  let e2 : LowMeanIntegerExpr := .atom (5227, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (18, 1)
  let e4 : LowMeanIntegerExpr := .atom (69, 2)
  let e5 : LowMeanIntegerExpr := .neg (-69, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-33, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-172491, 20000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (665349, 20000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (3471, 50000000)
  let e10 : LowMeanIntegerExpr := .pow (1089, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (3779919, 200000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-3779919, 200000000) e11
  let e13 : LowMeanIntegerExpr := .add (2873571, 200000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (183339, 13225000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (2986831059, 105800000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1171, 50)
  let e33 : LowMeanIntegerExpr := .pow (1000000000000000000, 3244150909895248285300369) e21 18
  let e34 : LowMeanIntegerExpr := .mul (23420000000000000000, 3244150909895248285300369) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-23420000000000000000, 3244150909895248285300369) e34
  let e36 : LowMeanIntegerExpr := .add (18312387262302907400853752879699, 648830181979049657060073800000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (18318875564122697897424353617699, 648830181979049657060073800000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-18312387262302907400853752879699, 648830181979049657060073800000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0415 : LowMeanDirectSeedInput :=
  { record := 415, positions := [], target := { R := 18, expr := lowMeanSeedTargetExpr0415 } }

noncomputable def lowMeanSeedGroup0400 : List LowMeanDirectSeedInput := [lowMeanSeedRecord0400, lowMeanSeedRecord0401, lowMeanSeedRecord0402, lowMeanSeedRecord0403, lowMeanSeedRecord0404, lowMeanSeedRecord0405, lowMeanSeedRecord0406, lowMeanSeedRecord0407, lowMeanSeedRecord0408, lowMeanSeedRecord0409, lowMeanSeedRecord0410, lowMeanSeedRecord0411, lowMeanSeedRecord0412, lowMeanSeedRecord0413, lowMeanSeedRecord0414, lowMeanSeedRecord0415]

end Erdos993Lean.Analytic.V213
