module

public import Erdos993Lean.Analytic.V213.LowMeanCoreAll
public import Erdos993Lean.Analytic.V213.LowMeanData.Seed0192
public import Erdos993Lean.Analytic.V213.LowMeanFiberSeed
public import Erdos993Lean.Analytic.V213.LowMeanIntegerExpr
public import Erdos993Lean.Analytic.V213.LowMeanSeedGeometry
public import Erdos993Lean.Analytic.V213.LowMeanWidthData
public import Erdos993Lean.Ceiling.Prefix
public import Erdos993Lean.Ceiling.Statement

/-! Exact core/budget keys and equation-51 targets for the direct fibers. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanSeedTargetExpr0336 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (8933, 250000)
  let e2 : LowMeanIntegerExpr := .atom (8401, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (14, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-2, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-8401, 5000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (170259, 5000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (3593, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (4, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (3593, 2500000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-3593, 2500000) e11
  let e13 : LowMeanIntegerExpr := .add (163073, 5000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (247, 31250)
  let e15 : LowMeanIntegerExpr := .atom (11, 21)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (13, 23)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-11, 21) e15
  let e21 : LowMeanIntegerExpr := .add (10, 21) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (110, 441) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-13, 23) e17
  let e24 : LowMeanIntegerExpr := .add (10, 23) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (130, 529) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (110, 441) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (110, 441) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2717, 1378125) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (5434, 196875) e29 e3
  let e31 : LowMeanIntegerExpr := .add (18967999, 315000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1773, 1000)
  let e33 : LowMeanIntegerExpr := .pow (100000000000000, 3243919932521508681) e21 14
  let e34 : LowMeanIntegerExpr := .mul (19700000000000, 360435548057945409) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-19700000000000, 360435548057945409) e34
  let e36 : LowMeanIntegerExpr := .add (108421200240120007301057, 1802177740289727045000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (108439222017522904571507, 1802177740289727045000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-108421200240120007301057, 1802177740289727045000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0336 : LowMeanDirectSeedInput :=
  { record := 336, positions := [{ j := 5, mode := 0, left := 726, right := 0 }, { j := 6, mode := 0, left := 727, right := 0 }, { j := 10, mode := 0, left := 728, right := 0 }, { j := 11, mode := 0, left := 729, right := 0 }], target := { R := 14, expr := lowMeanSeedTargetExpr0336 } }

noncomputable def lowMeanSeedTargetExpr0337 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (8933, 250000)
  let e2 : LowMeanIntegerExpr := .atom (8401, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (15, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-1, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-8401, 10000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (348919, 10000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (3593, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (1, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (3593, 10000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-3593, 10000000) e11
  let e13 : LowMeanIntegerExpr := .add (172663, 5000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (247, 31250)
  let e15 : LowMeanIntegerExpr := .atom (11, 21)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (13, 23)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-11, 21) e15
  let e21 : LowMeanIntegerExpr := .add (10, 21) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (110, 441) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-13, 23) e17
  let e24 : LowMeanIntegerExpr := .add (10, 23) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (130, 529) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (110, 441) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (110, 441) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2717, 1378125) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (2717, 91875) e29 e3
  let e31 : LowMeanIntegerExpr := .add (47117461, 735000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1773, 1000)
  let e33 : LowMeanIntegerExpr := .pow (1000000000000000, 68122318582951682301) e21 15
  let e34 : LowMeanIntegerExpr := .mul (197000000000000, 7569146509216853589) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-197000000000000, 7569146509216853589) e34
  let e36 : LowMeanIntegerExpr := .add (2425130411233409792669507, 37845732546084267945000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (2425508868558870635348957, 37845732546084267945000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-2425130411233409792669507, 37845732546084267945000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0337 : LowMeanDirectSeedInput :=
  { record := 337, positions := [{ j := 6, mode := 0, left := 730, right := 0 }, { j := 7, mode := 0, left := 731, right := 0 }, { j := 10, mode := 0, left := 732, right := 0 }, { j := 11, mode := 0, left := 733, right := 0 }], target := { R := 15, expr := lowMeanSeedTargetExpr0337 } }

noncomputable def lowMeanSeedTargetExpr0338 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (8933, 250000)
  let e2 : LowMeanIntegerExpr := .atom (8401, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (16, 1)
  let e4 : LowMeanIntegerExpr := .neg (-16, 1) e3
  let e5 : LowMeanIntegerExpr := .add (0, 1) e3 e4
  let e6 : LowMeanIntegerExpr := .mul (0, 1) e2 e5
  let e7 : LowMeanIntegerExpr := .add (8933, 250000) e1 e6
  let e8 : LowMeanIntegerExpr := .atom (3593, 10000000)
  let e9 : LowMeanIntegerExpr := .pow (0, 1) e5 2
  let e10 : LowMeanIntegerExpr := .mul (0, 1) e8 e9
  let e11 : LowMeanIntegerExpr := .neg (0, 1) e10
  let e12 : LowMeanIntegerExpr := .add (8933, 250000) e7 e11
  let e13 : LowMeanIntegerExpr := .atom (247, 31250)
  let e14 : LowMeanIntegerExpr := .atom (11, 21)
  let e15 : LowMeanIntegerExpr := .atom (1, 2)
  let e16 : LowMeanIntegerExpr := .atom (13, 23)
  let e17 : LowMeanIntegerExpr := .atom (1, 4)
  let e18 : LowMeanIntegerExpr := .atom (1, 1)
  let e19 : LowMeanIntegerExpr := .neg (-11, 21) e14
  let e20 : LowMeanIntegerExpr := .add (10, 21) e18 e19
  let e21 : LowMeanIntegerExpr := .mul (110, 441) e14 e20
  let e22 : LowMeanIntegerExpr := .neg (-13, 23) e16
  let e23 : LowMeanIntegerExpr := .add (10, 23) e18 e22
  let e24 : LowMeanIntegerExpr := .mul (130, 529) e16 e23
  let e25 : LowMeanIntegerExpr := .maximum (110, 441) e21 e24
  let e26 : LowMeanIntegerExpr := .selectLE (1, 4) e15 e16 e17 e25
  let e27 : LowMeanIntegerExpr := .selectLE (110, 441) e14 e15 e26 e25
  let e28 : LowMeanIntegerExpr := .mul (2717, 1378125) e13 e27
  let e29 : LowMeanIntegerExpr := .mul (43472, 1378125) e28 e3
  let e30 : LowMeanIntegerExpr := .add (7417213, 110250000) e12 e29
  let e31 : LowMeanIntegerExpr := .atom (1773, 1000)
  let e32 : LowMeanIntegerExpr := .pow (10000000000000000, 1430568690241985328321) e20 16
  let e33 : LowMeanIntegerExpr := .mul (1970000000000000, 158952076693553925369) e31 e32
  let e34 : LowMeanIntegerExpr := .neg (-1970000000000000, 158952076693553925369) e33
  let e35 : LowMeanIntegerExpr := .add (2672934732717517440925117, 39738019173388481342250000) e30 e34
  let e36 : LowMeanIntegerExpr := .add (5346664225818502651477079, 79476038346776962684500000) e0 e35
  let e37 : LowMeanIntegerExpr := .neg (-2672934732717517440925117, 39738019173388481342250000) e35
  let e38 : LowMeanIntegerExpr := .add (1, 100000) e36 e37
  e38

noncomputable def lowMeanSeedRecord0338 : LowMeanDirectSeedInput :=
  { record := 338, positions := [{ j := 7, mode := 0, left := 734, right := 0 }, { j := 10, mode := 0, left := 735, right := 0 }, { j := 11, mode := 0, left := 736, right := 0 }, { j := 12, mode := 0, left := 737, right := 0 }], target := { R := 16, expr := lowMeanSeedTargetExpr0338 } }

noncomputable def lowMeanSeedTargetExpr0339 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (8933, 250000)
  let e2 : LowMeanIntegerExpr := .atom (8401, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (17, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (1, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (8401, 10000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (365721, 10000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (3593, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (1, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (3593, 10000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-3593, 10000000) e11
  let e13 : LowMeanIntegerExpr := .add (22633, 625000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (247, 31250)
  let e15 : LowMeanIntegerExpr := .atom (11, 21)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (13, 23)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-11, 21) e15
  let e21 : LowMeanIntegerExpr := .add (10, 21) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (110, 441) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-13, 23) e17
  let e24 : LowMeanIntegerExpr := .add (10, 23) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (130, 529) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (110, 441) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (110, 441) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2717, 1378125) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (46189, 1378125) e29 e3
  let e31 : LowMeanIntegerExpr := .add (19218953, 275625000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1773, 1000)
  let e33 : LowMeanIntegerExpr := .pow (100000000000000000, 30041942495081691894741) e21 17
  let e34 : LowMeanIntegerExpr := .mul (19700000000000000, 3337993610564632432749) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-19700000000000000, 3337993610564632432749) e34
  let e36 : LowMeanIntegerExpr := .add (145458758510752775934872317, 2086246006602895270468125000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (581918483883275219550307993, 8344984026411581081872500000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-145458758510752775934872317, 2086246006602895270468125000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0339 : LowMeanDirectSeedInput :=
  { record := 339, positions := [{ j := 7, mode := 0, left := 738, right := 0 }, { j := 8, mode := 0, left := 739, right := 0 }, { j := 11, mode := 0, left := 740, right := 0 }, { j := 12, mode := 0, left := 741, right := 0 }], target := { R := 17, expr := lowMeanSeedTargetExpr0339 } }

noncomputable def lowMeanSeedTargetExpr0340 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (8933, 250000)
  let e2 : LowMeanIntegerExpr := .atom (8401, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (18, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (2, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (8401, 5000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (187061, 5000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (3593, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (4, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (3593, 2500000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-3593, 2500000) e11
  let e13 : LowMeanIntegerExpr := .add (1439, 40000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (247, 31250)
  let e15 : LowMeanIntegerExpr := .atom (11, 21)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (13, 23)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-11, 21) e15
  let e21 : LowMeanIntegerExpr := .add (10, 21) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (110, 441) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-13, 23) e17
  let e24 : LowMeanIntegerExpr := .add (10, 23) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (130, 529) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (110, 441) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (110, 441) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2717, 1378125) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (5434, 153125) e29 e3
  let e31 : LowMeanIntegerExpr := .add (700331, 9800000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1773, 1000)
  let e33 : LowMeanIntegerExpr := .pow (1000000000000000000, 630880792396715529789561) e21 18
  let e34 : LowMeanIntegerExpr := .mul (197000000000000000, 70097865821857281087729) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-197000000000000000, 70097865821857281087729) e34
  let e36 : LowMeanIntegerExpr := .add (1001832201405859826968374251, 14019573164371456217545800000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (1001972397137503541530549709, 14019573164371456217545800000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-1001832201405859826968374251, 14019573164371456217545800000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0340 : LowMeanDirectSeedInput :=
  { record := 340, positions := [{ j := 8, mode := 0, left := 742, right := 0 }, { j := 9, mode := 0, left := 743, right := 0 }, { j := 11, mode := 0, left := 744, right := 0 }, { j := 12, mode := 0, left := 745, right := 0 }, { j := 13, mode := 0, left := 746, right := 0 }], target := { R := 18, expr := lowMeanSeedTargetExpr0340 } }

noncomputable def lowMeanSeedTargetExpr0341 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (8933, 250000)
  let e2 : LowMeanIntegerExpr := .atom (8401, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (20, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (4, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (8401, 2500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (97731, 2500000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (3593, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (16, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (3593, 625000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-3593, 625000) e11
  let e13 : LowMeanIntegerExpr := .add (83359, 2500000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (247, 31250)
  let e15 : LowMeanIntegerExpr := .atom (11, 21)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (13, 23)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-11, 21) e15
  let e21 : LowMeanIntegerExpr := .add (10, 21) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (110, 441) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-13, 23) e17
  let e24 : LowMeanIntegerExpr := .add (10, 23) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (130, 529) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (110, 441) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (110, 441) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2717, 1378125) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (10868, 275625) e29 e3
  let e31 : LowMeanIntegerExpr := .add (80233319, 1102500000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1773, 1000)
  let e33 : LowMeanIntegerExpr := .pow (100000000000000000000, 278218429446951548637196401) e21 20
  let e34 : LowMeanIntegerExpr := .mul (19700000000000000000, 30913158827439060959688489) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-19700000000000000000, 30913158827439060959688489) e34
  let e36 : LowMeanIntegerExpr := .add (5624135179704272405984427842551, 77282897068597652399221222500000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (703113501084369797813552506847, 9660362133574706549902652812500) e0 e36
  let e38 : LowMeanIntegerExpr := .atom (19, 1)
  let e39 : LowMeanIntegerExpr := .add (3, 1) e38 e5
  let e40 : LowMeanIntegerExpr := .mul (25203, 10000000) e2 e39
  let e41 : LowMeanIntegerExpr := .add (382523, 10000000) e1 e40
  let e42 : LowMeanIntegerExpr := .pow (9, 1) e39 2
  let e43 : LowMeanIntegerExpr := .mul (32337, 10000000) e9 e42
  let e44 : LowMeanIntegerExpr := .neg (-32337, 10000000) e43
  let e45 : LowMeanIntegerExpr := .add (175093, 5000000) e41 e44
  let e46 : LowMeanIntegerExpr := .mul (51623, 1378125) e29 e38
  let e47 : LowMeanIntegerExpr := .add (159812813, 2205000000) e45 e46
  let e48 : LowMeanIntegerExpr := .pow (10000000000000000000, 13248496640331026125580781) e21 19
  let e49 : LowMeanIntegerExpr := .mul (1970000000000000000, 1472055182259002902842309) e32 e48
  let e50 : LowMeanIntegerExpr := .neg (-1970000000000000000, 1472055182259002902842309) e49
  let e51 : LowMeanIntegerExpr := .add (533444298680360427388651012937, 7360275911295014514211545000000) e47 e50
  let e52 : LowMeanIntegerExpr := .neg (-533444298680360427388651012937, 7360275911295014514211545000000) e51
  let e53 : LowMeanIntegerExpr := .add (379885960498782318841350703, 1236526353097562438387539560000) e37 e52
  e53

noncomputable def lowMeanSeedRecord0341 : LowMeanDirectSeedInput :=
  { record := 341, positions := [{ j := 9, mode := 0, left := 747, right := 0 }, { j := 10, mode := 0, left := 748, right := 0 }, { j := 11, mode := 0, left := 749, right := 0 }, { j := 12, mode := 0, left := 750, right := 0 }, { j := 13, mode := 0, left := 751, right := 0 }], target := { R := 20, expr := lowMeanSeedTargetExpr0341 } }

noncomputable def lowMeanSeedTargetExpr0342 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (773, 40000)
  let e2 : LowMeanIntegerExpr := .atom (1543, 2500000)
  let e3 : LowMeanIntegerExpr := .atom (0, 1)
  let e4 : LowMeanIntegerExpr := .atom (23, 1)
  let e5 : LowMeanIntegerExpr := .neg (-23, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-23, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-35489, 2500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (25647, 5000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (81, 625000)
  let e10 : LowMeanIntegerExpr := .pow (529, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (42849, 625000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-42849, 625000) e11
  let e13 : LowMeanIntegerExpr := .add (-63429, 1000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (2959, 1000000)
  let e15 : LowMeanIntegerExpr := .atom (11, 21)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (13, 23)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-11, 21) e15
  let e21 : LowMeanIntegerExpr := .add (10, 21) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (110, 441) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-13, 23) e17
  let e24 : LowMeanIntegerExpr := .add (10, 23) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (130, 529) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (110, 441) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (110, 441) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (32549, 44100000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (0, 1) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-63429, 1000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1129, 125)
  let e33 : LowMeanIntegerExpr := .pow (1, 1) e21 0
  let e34 : LowMeanIntegerExpr := .mul (1129, 125) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1129, 125) e34
  let e36 : LowMeanIntegerExpr := .add (-9095429, 1000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-9095419, 1000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (9095429, 1000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0342 : LowMeanDirectSeedInput :=
  { record := 342, positions := [], target := { R := 0, expr := lowMeanSeedTargetExpr0342 } }

noncomputable def lowMeanSeedTargetExpr0343 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (773, 40000)
  let e2 : LowMeanIntegerExpr := .atom (1543, 2500000)
  let e3 : LowMeanIntegerExpr := .atom (1, 1)
  let e4 : LowMeanIntegerExpr := .atom (23, 1)
  let e5 : LowMeanIntegerExpr := .neg (-23, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-22, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-16973, 1250000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (28733, 5000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (81, 625000)
  let e10 : LowMeanIntegerExpr := .pow (484, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (9801, 156250) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-9801, 156250) e11
  let e13 : LowMeanIntegerExpr := .add (-284899, 5000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (2959, 1000000)
  let e15 : LowMeanIntegerExpr := .atom (11, 21)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (13, 23)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .neg (-11, 21) e15
  let e20 : LowMeanIntegerExpr := .add (10, 21) e3 e19
  let e21 : LowMeanIntegerExpr := .mul (110, 441) e15 e20
  let e22 : LowMeanIntegerExpr := .neg (-13, 23) e17
  let e23 : LowMeanIntegerExpr := .add (10, 23) e3 e22
  let e24 : LowMeanIntegerExpr := .mul (130, 529) e17 e23
  let e25 : LowMeanIntegerExpr := .maximum (110, 441) e21 e24
  let e26 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e25
  let e27 : LowMeanIntegerExpr := .selectLE (110, 441) e15 e16 e26 e25
  let e28 : LowMeanIntegerExpr := .mul (32549, 44100000) e14 e27
  let e29 : LowMeanIntegerExpr := .mul (32549, 44100000) e28 e3
  let e30 : LowMeanIntegerExpr := .add (-124013009, 2205000000) e13 e29
  let e31 : LowMeanIntegerExpr := .atom (1129, 125)
  let e32 : LowMeanIntegerExpr := .pow (10, 21) e20 1
  let e33 : LowMeanIntegerExpr := .mul (2258, 525) e31 e32
  let e34 : LowMeanIntegerExpr := .neg (-2258, 525) e33
  let e35 : LowMeanIntegerExpr := .add (-9607613009, 2205000000) e30 e34
  let e36 : LowMeanIntegerExpr := .add (-9607590959, 2205000000) e0 e35
  let e37 : LowMeanIntegerExpr := .neg (9607613009, 2205000000) e35
  let e38 : LowMeanIntegerExpr := .add (1, 100000) e36 e37
  e38

noncomputable def lowMeanSeedRecord0343 : LowMeanDirectSeedInput :=
  { record := 343, positions := [], target := { R := 1, expr := lowMeanSeedTargetExpr0343 } }

noncomputable def lowMeanSeedTargetExpr0344 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (773, 40000)
  let e2 : LowMeanIntegerExpr := .atom (1543, 2500000)
  let e3 : LowMeanIntegerExpr := .atom (2, 1)
  let e4 : LowMeanIntegerExpr := .atom (23, 1)
  let e5 : LowMeanIntegerExpr := .neg (-23, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-21, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-32403, 2500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (31819, 5000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (81, 625000)
  let e10 : LowMeanIntegerExpr := .pow (441, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (35721, 625000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-35721, 625000) e11
  let e13 : LowMeanIntegerExpr := .add (-253949, 5000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (2959, 1000000)
  let e15 : LowMeanIntegerExpr := .atom (11, 21)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (13, 23)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-11, 21) e15
  let e21 : LowMeanIntegerExpr := .add (10, 21) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (110, 441) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-13, 23) e17
  let e24 : LowMeanIntegerExpr := .add (10, 23) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (130, 529) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (110, 441) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (110, 441) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (32549, 44100000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (32549, 22050000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-108736609, 2205000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1129, 125)
  let e33 : LowMeanIntegerExpr := .pow (100, 441) e21 2
  let e34 : LowMeanIntegerExpr := .mul (4516, 2205) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-4516, 2205) e34
  let e36 : LowMeanIntegerExpr := .add (-4624736609, 2205000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-4624714559, 2205000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (4624736609, 2205000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0344 : LowMeanDirectSeedInput :=
  { record := 344, positions := [], target := { R := 2, expr := lowMeanSeedTargetExpr0344 } }

noncomputable def lowMeanSeedTargetExpr0345 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (773, 40000)
  let e2 : LowMeanIntegerExpr := .atom (1543, 2500000)
  let e3 : LowMeanIntegerExpr := .atom (3, 1)
  let e4 : LowMeanIntegerExpr := .atom (23, 1)
  let e5 : LowMeanIntegerExpr := .neg (-23, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-20, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1543, 125000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (6981, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (81, 625000)
  let e10 : LowMeanIntegerExpr := .pow (400, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (162, 3125) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-162, 3125) e11
  let e13 : LowMeanIntegerExpr := .add (-44859, 1000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (2959, 1000000)
  let e15 : LowMeanIntegerExpr := .atom (11, 21)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (13, 23)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-11, 21) e15
  let e21 : LowMeanIntegerExpr := .add (10, 21) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (110, 441) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-13, 23) e17
  let e24 : LowMeanIntegerExpr := .add (10, 23) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (130, 529) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (110, 441) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (110, 441) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (32549, 44100000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (32549, 14700000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-6268783, 147000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1129, 125)
  let e33 : LowMeanIntegerExpr := .pow (1000, 9261) e21 3
  let e34 : LowMeanIntegerExpr := .mul (9032, 9261) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-9032, 9261) e34
  let e36 : LowMeanIntegerExpr := .add (-9426933329, 9261000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-9426840719, 9261000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (9426933329, 9261000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0345 : LowMeanDirectSeedInput :=
  { record := 345, positions := [], target := { R := 3, expr := lowMeanSeedTargetExpr0345 } }

noncomputable def lowMeanSeedTargetExpr0346 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (773, 40000)
  let e2 : LowMeanIntegerExpr := .atom (1543, 2500000)
  let e3 : LowMeanIntegerExpr := .atom (4, 1)
  let e4 : LowMeanIntegerExpr := .atom (23, 1)
  let e5 : LowMeanIntegerExpr := .neg (-23, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-19, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-29317, 2500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (37991, 5000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (81, 625000)
  let e10 : LowMeanIntegerExpr := .pow (361, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (29241, 625000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-29241, 625000) e11
  let e13 : LowMeanIntegerExpr := .add (-195937, 5000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (2959, 1000000)
  let e15 : LowMeanIntegerExpr := .atom (11, 21)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (13, 23)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-11, 21) e15
  let e21 : LowMeanIntegerExpr := .add (10, 21) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (110, 441) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-13, 23) e17
  let e24 : LowMeanIntegerExpr := .add (10, 23) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (130, 529) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (110, 441) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (110, 441) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (32549, 44100000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (32549, 11025000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-79898417, 2205000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1129, 125)
  let e33 : LowMeanIntegerExpr := .pow (10000, 194481) e21 4
  let e34 : LowMeanIntegerExpr := .mul (90320, 194481) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-90320, 194481) e34
  let e36 : LowMeanIntegerExpr := .add (-486835201897, 972405000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-486825477847, 972405000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (486835201897, 972405000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0346 : LowMeanDirectSeedInput :=
  { record := 346, positions := [], target := { R := 4, expr := lowMeanSeedTargetExpr0346 } }

noncomputable def lowMeanSeedTargetExpr0347 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (773, 40000)
  let e2 : LowMeanIntegerExpr := .atom (1543, 2500000)
  let e3 : LowMeanIntegerExpr := .atom (5, 1)
  let e4 : LowMeanIntegerExpr := .atom (23, 1)
  let e5 : LowMeanIntegerExpr := .neg (-23, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-18, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-13887, 1250000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (41077, 5000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (81, 625000)
  let e10 : LowMeanIntegerExpr := .pow (324, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (6561, 156250) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-6561, 156250) e11
  let e13 : LowMeanIntegerExpr := .add (-1351, 40000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (2959, 1000000)
  let e15 : LowMeanIntegerExpr := .atom (11, 21)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (13, 23)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-11, 21) e15
  let e21 : LowMeanIntegerExpr := .add (10, 21) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (110, 441) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-13, 23) e17
  let e24 : LowMeanIntegerExpr := .add (10, 23) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (130, 529) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (110, 441) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (110, 441) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (32549, 44100000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (32549, 8820000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-530693, 17640000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1129, 125)
  let e33 : LowMeanIntegerExpr := .pow (100000, 4084101) e21 5
  let e34 : LowMeanIntegerExpr := .mul (903200, 4084101) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-903200, 4084101) e34
  let e36 : LowMeanIntegerExpr := .add (-41042747873, 163364040000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-205205571163, 816820200000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (41042747873, 163364040000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0347 : LowMeanDirectSeedInput :=
  { record := 347, positions := [], target := { R := 5, expr := lowMeanSeedTargetExpr0347 } }

noncomputable def lowMeanSeedTargetExpr0348 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (773, 40000)
  let e2 : LowMeanIntegerExpr := .atom (1543, 2500000)
  let e3 : LowMeanIntegerExpr := .atom (6, 1)
  let e4 : LowMeanIntegerExpr := .atom (23, 1)
  let e5 : LowMeanIntegerExpr := .neg (-23, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-17, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-26231, 2500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (44163, 5000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (81, 625000)
  let e10 : LowMeanIntegerExpr := .pow (289, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (23409, 625000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-23409, 625000) e11
  let e13 : LowMeanIntegerExpr := .add (-143109, 5000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (2959, 1000000)
  let e15 : LowMeanIntegerExpr := .atom (11, 21)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (13, 23)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-11, 21) e15
  let e21 : LowMeanIntegerExpr := .add (10, 21) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (110, 441) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-13, 23) e17
  let e24 : LowMeanIntegerExpr := .add (10, 23) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (130, 529) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (110, 441) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (110, 441) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (32549, 44100000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (32549, 7350000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-17782123, 735000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1129, 125)
  let e33 : LowMeanIntegerExpr := .pow (1000000, 85766121) e21 6
  let e34 : LowMeanIntegerExpr := .mul (9032000, 85766121) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-9032000, 85766121) e34
  let e36 : LowMeanIntegerExpr := .add (-55534855189489, 428830605000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-55530566883439, 428830605000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (55534855189489, 428830605000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0348 : LowMeanDirectSeedInput :=
  { record := 348, positions := [{ j := 1, mode := 0, left := 752, right := 0 }], target := { R := 6, expr := lowMeanSeedTargetExpr0348 } }

noncomputable def lowMeanSeedTargetExpr0349 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (773, 40000)
  let e2 : LowMeanIntegerExpr := .atom (1543, 2500000)
  let e3 : LowMeanIntegerExpr := .atom (7, 1)
  let e4 : LowMeanIntegerExpr := .atom (23, 1)
  let e5 : LowMeanIntegerExpr := .neg (-23, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-16, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1543, 156250) e2 e6
  let e8 : LowMeanIntegerExpr := .add (47249, 5000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (81, 625000)
  let e10 : LowMeanIntegerExpr := .pow (256, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (2592, 78125) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-2592, 78125) e11
  let e13 : LowMeanIntegerExpr := .add (-118639, 5000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (2959, 1000000)
  let e15 : LowMeanIntegerExpr := .atom (11, 21)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (13, 23)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-11, 21) e15
  let e21 : LowMeanIntegerExpr := .add (10, 21) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (110, 441) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-13, 23) e17
  let e24 : LowMeanIntegerExpr := .add (10, 23) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (130, 529) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (110, 441) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (110, 441) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (32549, 44100000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (32549, 6300000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-5846807, 315000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1129, 125)
  let e33 : LowMeanIntegerExpr := .pow (10000000, 1801088541) e21 7
  let e34 : LowMeanIntegerExpr := .mul (90320000, 1801088541) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-90320000, 1801088541) e34
  let e36 : LowMeanIntegerExpr := .add (-618752652208549, 9005442705000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-618662597781499, 9005442705000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (618752652208549, 9005442705000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0349 : LowMeanDirectSeedInput :=
  { record := 349, positions := [{ j := 1, mode := 0, left := 753, right := 0 }, { j := 2, mode := 0, left := 754, right := 0 }], target := { R := 7, expr := lowMeanSeedTargetExpr0349 } }

noncomputable def lowMeanSeedTargetExpr0350 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (773, 40000)
  let e2 : LowMeanIntegerExpr := .atom (1543, 2500000)
  let e3 : LowMeanIntegerExpr := .atom (8, 1)
  let e4 : LowMeanIntegerExpr := .atom (23, 1)
  let e5 : LowMeanIntegerExpr := .neg (-23, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-15, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-4629, 500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (10067, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (81, 625000)
  let e10 : LowMeanIntegerExpr := .pow (225, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (729, 25000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-729, 25000) e11
  let e13 : LowMeanIntegerExpr := .add (-19093, 1000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (2959, 1000000)
  let e15 : LowMeanIntegerExpr := .atom (11, 21)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (13, 23)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-11, 21) e15
  let e21 : LowMeanIntegerExpr := .add (10, 21) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (110, 441) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-13, 23) e17
  let e24 : LowMeanIntegerExpr := .add (10, 23) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (130, 529) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (110, 441) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (110, 441) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (32549, 44100000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (32549, 5512500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-5816093, 441000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1129, 125)
  let e33 : LowMeanIntegerExpr := .pow (100000000, 37822859361) e21 8
  let e34 : LowMeanIntegerExpr := .mul (903200000, 37822859361) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-903200000, 37822859361) e34
  let e36 : LowMeanIntegerExpr := .add (-1402023735985253, 37822859361000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-1401645507391643, 37822859361000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (1402023735985253, 37822859361000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0350 : LowMeanDirectSeedInput :=
  { record := 350, positions := [{ j := 2, mode := 0, left := 755, right := 0 }, { j := 7, mode := 0, left := 756, right := 0 }], target := { R := 8, expr := lowMeanSeedTargetExpr0350 } }

noncomputable def lowMeanSeedTargetExpr0351 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (773, 40000)
  let e2 : LowMeanIntegerExpr := .atom (1543, 2500000)
  let e3 : LowMeanIntegerExpr := .atom (9, 1)
  let e4 : LowMeanIntegerExpr := .atom (23, 1)
  let e5 : LowMeanIntegerExpr := .neg (-23, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-14, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-10801, 1250000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (53421, 5000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (81, 625000)
  let e10 : LowMeanIntegerExpr := .pow (196, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (3969, 156250) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-3969, 156250) e11
  let e13 : LowMeanIntegerExpr := .add (-73587, 5000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (2959, 1000000)
  let e15 : LowMeanIntegerExpr := .atom (11, 21)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (13, 23)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-11, 21) e15
  let e21 : LowMeanIntegerExpr := .add (10, 21) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (110, 441) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-13, 23) e17
  let e24 : LowMeanIntegerExpr := .add (10, 23) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (130, 529) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (110, 441) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (110, 441) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (32549, 44100000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (32549, 4900000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-1978313, 245000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1129, 125)
  let e33 : LowMeanIntegerExpr := .pow (1000000000, 794280046581) e21 9
  let e34 : LowMeanIntegerExpr := .mul (9032000000, 794280046581) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-9032000000, 794280046581) e34
  let e36 : LowMeanIntegerExpr := .add (-77228051873301997, 3971400232905000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-77188337870972947, 3971400232905000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (77228051873301997, 3971400232905000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0351 : LowMeanDirectSeedInput :=
  { record := 351, positions := [{ j := 2, mode := 0, left := 757, right := 0 }, { j := 3, mode := 0, left := 758, right := 0 }, { j := 8, mode := 0, left := 759, right := 0 }], target := { R := 9, expr := lowMeanSeedTargetExpr0351 } }

noncomputable def lowMeanSeedGroup0336 : List LowMeanDirectSeedInput := [lowMeanSeedRecord0336, lowMeanSeedRecord0337, lowMeanSeedRecord0338, lowMeanSeedRecord0339, lowMeanSeedRecord0340, lowMeanSeedRecord0341, lowMeanSeedRecord0342, lowMeanSeedRecord0343, lowMeanSeedRecord0344, lowMeanSeedRecord0345, lowMeanSeedRecord0346, lowMeanSeedRecord0347, lowMeanSeedRecord0348, lowMeanSeedRecord0349, lowMeanSeedRecord0350, lowMeanSeedRecord0351]

end Erdos993Lean.Analytic.V213
