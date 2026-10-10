module

public import Erdos993Lean.Analytic.V213.LowMeanCoreAll
public import Erdos993Lean.Analytic.V213.LowMeanData.Seed0080
public import Erdos993Lean.Analytic.V213.LowMeanFiberSeed
public import Erdos993Lean.Analytic.V213.LowMeanIntegerExpr
public import Erdos993Lean.Analytic.V213.LowMeanSeedGeometry
public import Erdos993Lean.Analytic.V213.LowMeanWidthData
public import Erdos993Lean.Ceiling.Prefix
public import Erdos993Lean.Ceiling.Statement

/-! Exact core/budget keys and equation-51 targets for the direct fibers. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanSeedTargetExpr0160 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (4227, 50000)
  let e2 : LowMeanIntegerExpr := .atom (-439, 250000)
  let e3 : LowMeanIntegerExpr := .atom (9, 1)
  let e4 : LowMeanIntegerExpr := .atom (35, 4)
  let e5 : LowMeanIntegerExpr := .neg (-35, 4) e4
  let e6 : LowMeanIntegerExpr := .add (1, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-439, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (84101, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (127, 100000)
  let e10 : LowMeanIntegerExpr := .pow (1, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (127, 1600000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-127, 1600000) e11
  let e13 : LowMeanIntegerExpr := .add (672173, 8000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (1719, 50000)
  let e15 : LowMeanIntegerExpr := .atom (23, 48)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (103, 203)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-23, 48) e15
  let e21 : LowMeanIntegerExpr := .add (25, 48) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (575, 2304) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-103, 203) e17
  let e24 : LowMeanIntegerExpr := .add (100, 203) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (10300, 41209) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (10300, 41209) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1, 4) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (1719, 200000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (15471, 200000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (1291013, 8000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (126, 125)
  let e33 : LowMeanIntegerExpr := .pow (3814697265625, 1352605460594688) e21 9
  let e34 : LowMeanIntegerExpr := .mul (213623046875, 75144747810816) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-213623046875, 75144747810816) e34
  let e36 : LowMeanIntegerExpr := .add (186140355332978509, 1174136684544000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (186152096699823949, 1174136684544000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-186140355332978509, 1174136684544000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0160 : LowMeanDirectSeedInput :=
  { record := 160, positions := [{ j := 3, mode := 0, left := 460, right := 0 }, { j := 5, mode := 0, left := 461, right := 0 }, { j := 6, mode := 0, left := 462, right := 0 }], target := { R := 9, expr := lowMeanSeedTargetExpr0160 } }

noncomputable def lowMeanSeedTargetExpr0161 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (4227, 50000)
  let e2 : LowMeanIntegerExpr := .atom (-439, 250000)
  let e3 : LowMeanIntegerExpr := .atom (10, 1)
  let e4 : LowMeanIntegerExpr := .atom (35, 4)
  let e5 : LowMeanIntegerExpr := .neg (-35, 4) e4
  let e6 : LowMeanIntegerExpr := .add (5, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-439, 200000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (16469, 200000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (127, 100000)
  let e10 : LowMeanIntegerExpr := .pow (25, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (127, 64000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-127, 64000) e11
  let e13 : LowMeanIntegerExpr := .add (128577, 1600000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (1719, 50000)
  let e15 : LowMeanIntegerExpr := .atom (23, 48)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (103, 203)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-23, 48) e15
  let e21 : LowMeanIntegerExpr := .add (25, 48) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (575, 2304) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-103, 203) e17
  let e24 : LowMeanIntegerExpr := .add (100, 203) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (10300, 41209) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (10300, 41209) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1, 4) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (1719, 200000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (1719, 20000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (266097, 1600000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (126, 125)
  let e33 : LowMeanIntegerExpr := .pow (95367431640625, 64925062108545024) e21 10
  let e34 : LowMeanIntegerExpr := .mul (5340576171875, 3606947894919168) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-5340576171875, 3606947894919168) e34
  let e36 : LowMeanIntegerExpr := .add (1857916195545519233, 11271712171622400000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (1858028912667235457, 11271712171622400000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-1857916195545519233, 11271712171622400000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0161 : LowMeanDirectSeedInput :=
  { record := 161, positions := [{ j := 4, mode := 0, left := 463, right := 0 }, { j := 5, mode := 0, left := 464, right := 0 }, { j := 6, mode := 0, left := 465, right := 0 }], target := { R := 10, expr := lowMeanSeedTargetExpr0161 } }

noncomputable def lowMeanSeedTargetExpr0162 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (4227, 50000)
  let e2 : LowMeanIntegerExpr := .atom (-439, 250000)
  let e3 : LowMeanIntegerExpr := .atom (11, 1)
  let e4 : LowMeanIntegerExpr := .atom (35, 4)
  let e5 : LowMeanIntegerExpr := .neg (-35, 4) e4
  let e6 : LowMeanIntegerExpr := .add (9, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-3951, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (80589, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (127, 100000)
  let e10 : LowMeanIntegerExpr := .pow (81, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (10287, 1600000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-10287, 1600000) e11
  let e13 : LowMeanIntegerExpr := .add (593277, 8000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (1719, 50000)
  let e15 : LowMeanIntegerExpr := .atom (23, 48)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (103, 203)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-23, 48) e15
  let e21 : LowMeanIntegerExpr := .add (25, 48) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (575, 2304) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-103, 203) e17
  let e24 : LowMeanIntegerExpr := .add (100, 203) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (10300, 41209) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (10300, 41209) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1, 4) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (1719, 200000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (18909, 200000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (1349637, 8000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (126, 125)
  let e33 : LowMeanIntegerExpr := .pow (2384185791015625, 3116402981210161152) e21 11
  let e34 : LowMeanIntegerExpr := .mul (133514404296875, 173133498956120064) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-133514404296875, 173133498956120064) e34
  let e36 : LowMeanIntegerExpr := .add (454295431438019560189, 2705210921189376000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (454322483547231453949, 2705210921189376000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-454295431438019560189, 2705210921189376000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0162 : LowMeanDirectSeedInput :=
  { record := 162, positions := [{ j := 4, mode := 0, left := 466, right := 0 }, { j := 5, mode := 0, left := 467, right := 0 }, { j := 6, mode := 0, left := 468, right := 0 }, { j := 7, mode := 0, left := 469, right := 0 }], target := { R := 11, expr := lowMeanSeedTargetExpr0162 } }

noncomputable def lowMeanSeedTargetExpr0163 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (4227, 50000)
  let e2 : LowMeanIntegerExpr := .atom (-439, 250000)
  let e3 : LowMeanIntegerExpr := .atom (12, 1)
  let e4 : LowMeanIntegerExpr := .atom (35, 4)
  let e5 : LowMeanIntegerExpr := .neg (-35, 4) e4
  let e6 : LowMeanIntegerExpr := .add (13, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-5707, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (78833, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (127, 100000)
  let e10 : LowMeanIntegerExpr := .pow (169, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (21463, 1600000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-21463, 1600000) e11
  let e13 : LowMeanIntegerExpr := .add (523349, 8000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (1719, 50000)
  let e15 : LowMeanIntegerExpr := .atom (23, 48)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (103, 203)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-23, 48) e15
  let e21 : LowMeanIntegerExpr := .add (25, 48) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (575, 2304) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-103, 203) e17
  let e24 : LowMeanIntegerExpr := .add (100, 203) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (10300, 41209) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (10300, 41209) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1, 4) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (1719, 200000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (5157, 50000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (1348469, 8000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (126, 125)
  let e33 : LowMeanIntegerExpr := .pow (59604644775390625, 149587343098087735296) e21 12
  let e34 : LowMeanIntegerExpr := .mul (3337860107421875, 8310407949893763072) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-3337860107421875, 8310407949893763072) e34
  let e36 : LowMeanIntegerExpr := .add (21835204329933433195189, 129850124217090048000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (21836502831175604095669, 129850124217090048000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-21835204329933433195189, 129850124217090048000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0163 : LowMeanDirectSeedInput :=
  { record := 163, positions := [{ j := 5, mode := 0, left := 470, right := 0 }, { j := 6, mode := 0, left := 471, right := 0 }, { j := 7, mode := 0, left := 472, right := 0 }], target := { R := 12, expr := lowMeanSeedTargetExpr0163 } }

noncomputable def lowMeanSeedTargetExpr0164 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (55569, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (237, 250000)
  let e3 : LowMeanIntegerExpr := .atom (0, 1)
  let e4 : LowMeanIntegerExpr := .atom (23, 2)
  let e5 : LowMeanIntegerExpr := .neg (-23, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-23, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-5451, 500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (44667, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (9853, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (529, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (5212237, 40000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-5212237, 40000000) e11
  let e13 : LowMeanIntegerExpr := .add (-3425557, 40000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (1743, 100000)
  let e15 : LowMeanIntegerExpr := .atom (23, 48)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (103, 203)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-23, 48) e15
  let e21 : LowMeanIntegerExpr := .add (25, 48) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (575, 2304) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-103, 203) e17
  let e24 : LowMeanIntegerExpr := .add (100, 203) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (10300, 41209) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (10300, 41209) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1, 4) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (1743, 400000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (0, 1) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-3425557, 40000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (8967, 10000)
  let e33 : LowMeanIntegerExpr := .pow (1, 1) e21 0
  let e34 : LowMeanIntegerExpr := .mul (8967, 10000) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-8967, 10000) e34
  let e36 : LowMeanIntegerExpr := .add (-39293557, 40000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-39293157, 40000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (39293557, 40000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0164 : LowMeanDirectSeedInput :=
  { record := 164, positions := [], target := { R := 0, expr := lowMeanSeedTargetExpr0164 } }

noncomputable def lowMeanSeedTargetExpr0165 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (55569, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (237, 250000)
  let e3 : LowMeanIntegerExpr := .atom (1, 1)
  let e4 : LowMeanIntegerExpr := .atom (23, 2)
  let e5 : LowMeanIntegerExpr := .neg (-23, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-21, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-4977, 500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (9123, 200000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (9853, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (441, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (4345173, 40000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-4345173, 40000000) e11
  let e13 : LowMeanIntegerExpr := .add (-2520573, 40000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (1743, 100000)
  let e15 : LowMeanIntegerExpr := .atom (23, 48)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (103, 203)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .neg (-23, 48) e15
  let e20 : LowMeanIntegerExpr := .add (25, 48) e3 e19
  let e21 : LowMeanIntegerExpr := .mul (575, 2304) e15 e20
  let e22 : LowMeanIntegerExpr := .neg (-103, 203) e17
  let e23 : LowMeanIntegerExpr := .add (100, 203) e3 e22
  let e24 : LowMeanIntegerExpr := .mul (10300, 41209) e17 e23
  let e25 : LowMeanIntegerExpr := .maximum (10300, 41209) e21 e24
  let e26 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e15 e16 e26 e25
  let e28 : LowMeanIntegerExpr := .mul (1743, 400000) e14 e27
  let e29 : LowMeanIntegerExpr := .mul (1743, 400000) e28 e3
  let e30 : LowMeanIntegerExpr := .add (-2346273, 40000000) e13 e29
  let e31 : LowMeanIntegerExpr := .atom (8967, 10000)
  let e32 : LowMeanIntegerExpr := .pow (25, 48) e20 1
  let e33 : LowMeanIntegerExpr := .mul (2989, 6400) e31 e32
  let e34 : LowMeanIntegerExpr := .neg (-2989, 6400) e33
  let e35 : LowMeanIntegerExpr := .add (-21027523, 40000000) e30 e34
  let e36 : LowMeanIntegerExpr := .add (-21027123, 40000000) e0 e35
  let e37 : LowMeanIntegerExpr := .neg (21027523, 40000000) e35
  let e38 : LowMeanIntegerExpr := .add (1, 100000) e36 e37
  e38

noncomputable def lowMeanSeedRecord0165 : LowMeanDirectSeedInput :=
  { record := 165, positions := [], target := { R := 1, expr := lowMeanSeedTargetExpr0165 } }

noncomputable def lowMeanSeedTargetExpr0166 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (55569, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (237, 250000)
  let e3 : LowMeanIntegerExpr := .atom (2, 1)
  let e4 : LowMeanIntegerExpr := .atom (23, 2)
  let e5 : LowMeanIntegerExpr := .neg (-23, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-19, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-4503, 500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (46563, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (9853, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (361, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (3556933, 40000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-3556933, 40000000) e11
  let e13 : LowMeanIntegerExpr := .add (-1694413, 40000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (1743, 100000)
  let e15 : LowMeanIntegerExpr := .atom (23, 48)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (103, 203)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-23, 48) e15
  let e21 : LowMeanIntegerExpr := .add (25, 48) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (575, 2304) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-103, 203) e17
  let e24 : LowMeanIntegerExpr := .add (100, 203) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (10300, 41209) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (10300, 41209) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1, 4) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (1743, 400000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (1743, 200000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-1345813, 40000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (8967, 10000)
  let e33 : LowMeanIntegerExpr := .pow (625, 2304) e21 2
  let e34 : LowMeanIntegerExpr := .mul (2989, 12288) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-2989, 12288) e34
  let e36 : LowMeanIntegerExpr := .add (-265815137, 960000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-265805537, 960000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (265815137, 960000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0166 : LowMeanDirectSeedInput :=
  { record := 166, positions := [], target := { R := 2, expr := lowMeanSeedTargetExpr0166 } }

noncomputable def lowMeanSeedTargetExpr0167 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (55569, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (237, 250000)
  let e3 : LowMeanIntegerExpr := .atom (3, 1)
  let e4 : LowMeanIntegerExpr := .atom (23, 2)
  let e5 : LowMeanIntegerExpr := .neg (-23, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-17, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-4029, 500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (47511, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (9853, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (289, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (2847517, 40000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-2847517, 40000000) e11
  let e13 : LowMeanIntegerExpr := .add (-947077, 40000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (1743, 100000)
  let e15 : LowMeanIntegerExpr := .atom (23, 48)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (103, 203)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-23, 48) e15
  let e21 : LowMeanIntegerExpr := .add (25, 48) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (575, 2304) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-103, 203) e17
  let e24 : LowMeanIntegerExpr := .add (100, 203) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (10300, 41209) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (10300, 41209) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1, 4) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (1743, 400000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (5229, 400000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-424177, 40000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (8967, 10000)
  let e33 : LowMeanIntegerExpr := .pow (15625, 110592) e21 3
  let e34 : LowMeanIntegerExpr := .mul (74725, 589824) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-74725, 589824) e34
  let e36 : LowMeanIntegerExpr := .add (-6326542529, 46080000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-6326081729, 46080000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (6326542529, 46080000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0167 : LowMeanDirectSeedInput :=
  { record := 167, positions := [], target := { R := 3, expr := lowMeanSeedTargetExpr0167 } }

noncomputable def lowMeanSeedTargetExpr0168 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (55569, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (237, 250000)
  let e3 : LowMeanIntegerExpr := .atom (4, 1)
  let e4 : LowMeanIntegerExpr := .atom (23, 2)
  let e5 : LowMeanIntegerExpr := .neg (-23, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-15, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-711, 100000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (48459, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (9853, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (225, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (88677, 1600000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-88677, 1600000) e11
  let e13 : LowMeanIntegerExpr := .add (-55713, 8000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (1743, 100000)
  let e15 : LowMeanIntegerExpr := .atom (23, 48)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (103, 203)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-23, 48) e15
  let e21 : LowMeanIntegerExpr := .add (25, 48) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (575, 2304) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-103, 203) e17
  let e24 : LowMeanIntegerExpr := .add (100, 203) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (10300, 41209) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (10300, 41209) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1, 4) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (1743, 400000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (1743, 100000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (83727, 8000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (8967, 10000)
  let e33 : LowMeanIntegerExpr := .pow (390625, 5308416) e21 4
  let e34 : LowMeanIntegerExpr := .mul (1868125, 28311552) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1868125, 28311552) e34
  let e36 : LowMeanIntegerExpr := .add (-24559684933, 442368000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-24555261253, 442368000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (24559684933, 442368000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0168 : LowMeanDirectSeedInput :=
  { record := 168, positions := [{ j := 0, mode := 0, left := 473, right := 0 }, { j := 4, mode := 0, left := 474, right := 0 }], target := { R := 4, expr := lowMeanSeedTargetExpr0168 } }

noncomputable def lowMeanSeedTargetExpr0169 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (55569, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (237, 250000)
  let e3 : LowMeanIntegerExpr := .atom (5, 1)
  let e4 : LowMeanIntegerExpr := .atom (23, 2)
  let e5 : LowMeanIntegerExpr := .neg (-23, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-13, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-3081, 500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (49407, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (9853, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (169, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1665157, 40000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1665157, 40000000) e11
  let e13 : LowMeanIntegerExpr := .add (311123, 40000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (1743, 100000)
  let e15 : LowMeanIntegerExpr := .atom (23, 48)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (103, 203)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-23, 48) e15
  let e21 : LowMeanIntegerExpr := .add (25, 48) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (575, 2304) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-103, 203) e17
  let e24 : LowMeanIntegerExpr := .add (100, 203) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (10300, 41209) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (10300, 41209) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1, 4) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (1743, 400000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (1743, 80000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (1182623, 40000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (8967, 10000)
  let e33 : LowMeanIntegerExpr := .pow (9765625, 254803968) e21 5
  let e34 : LowMeanIntegerExpr := .mul (46703125, 1358954496) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-46703125, 1358954496) e34
  let e36 : LowMeanIntegerExpr := .add (-509754213041, 106168320000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-508692529841, 106168320000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (509754213041, 106168320000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0169 : LowMeanDirectSeedInput :=
  { record := 169, positions := [{ j := 0, mode := 0, left := 475, right := 0 }, { j := 4, mode := 0, left := 476, right := 0 }], target := { R := 5, expr := lowMeanSeedTargetExpr0169 } }

noncomputable def lowMeanSeedTargetExpr0170 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (55569, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (237, 250000)
  let e3 : LowMeanIntegerExpr := .atom (6, 1)
  let e4 : LowMeanIntegerExpr := .atom (23, 2)
  let e5 : LowMeanIntegerExpr := .neg (-23, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-11, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-2607, 500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (10071, 200000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (9853, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (121, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1192213, 40000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1192213, 40000000) e11
  let e13 : LowMeanIntegerExpr := .add (821987, 40000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (1743, 100000)
  let e15 : LowMeanIntegerExpr := .atom (23, 48)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (103, 203)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-23, 48) e15
  let e21 : LowMeanIntegerExpr := .add (25, 48) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (575, 2304) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-103, 203) e17
  let e24 : LowMeanIntegerExpr := .add (100, 203) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (10300, 41209) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (10300, 41209) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1, 4) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (1743, 400000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (5229, 200000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (1867787, 40000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (8967, 10000)
  let e33 : LowMeanIntegerExpr := .pow (244140625, 12230590464) e21 6
  let e34 : LowMeanIntegerExpr := .mul (1167578125, 65229815808) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1167578125, 65229815808) e34
  let e36 : LowMeanIntegerExpr := .add (146742728473783, 5096079360000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (146793689267383, 5096079360000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-146742728473783, 5096079360000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0170 : LowMeanDirectSeedInput :=
  { record := 170, positions := [{ j := 1, mode := 0, left := 477, right := 0 }, { j := 5, mode := 0, left := 478, right := 0 }], target := { R := 6, expr := lowMeanSeedTargetExpr0170 } }

noncomputable def lowMeanSeedTargetExpr0171 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (55569, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (237, 250000)
  let e3 : LowMeanIntegerExpr := .atom (7, 1)
  let e4 : LowMeanIntegerExpr := .atom (23, 2)
  let e5 : LowMeanIntegerExpr := .neg (-23, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-9, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-2133, 500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (51303, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (9853, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (81, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (798093, 40000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-798093, 40000000) e11
  let e13 : LowMeanIntegerExpr := .add (1254027, 40000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (1743, 100000)
  let e15 : LowMeanIntegerExpr := .atom (23, 48)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (103, 203)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-23, 48) e15
  let e21 : LowMeanIntegerExpr := .add (25, 48) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (575, 2304) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-103, 203) e17
  let e24 : LowMeanIntegerExpr := .add (100, 203) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (10300, 41209) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (10300, 41209) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1, 4) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (1743, 400000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (12201, 400000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (2474127, 40000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (8967, 10000)
  let e33 : LowMeanIntegerExpr := .pow (6103515625, 587068342272) e21 7
  let e34 : LowMeanIntegerExpr := .mul (29189453125, 3131031158784) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-29189453125, 3131031158784) e34
  let e36 : LowMeanIntegerExpr := .add (12849591021071839, 244611809280000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (12852037139164639, 244611809280000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-12849591021071839, 244611809280000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0171 : LowMeanDirectSeedInput :=
  { record := 171, positions := [{ j := 1, mode := 0, left := 479, right := 0 }, { j := 2, mode := 0, left := 480, right := 0 }, { j := 5, mode := 0, left := 481, right := 0 }, { j := 6, mode := 0, left := 482, right := 0 }], target := { R := 7, expr := lowMeanSeedTargetExpr0171 } }

noncomputable def lowMeanSeedTargetExpr0172 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (55569, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (237, 250000)
  let e3 : LowMeanIntegerExpr := .atom (8, 1)
  let e4 : LowMeanIntegerExpr := .atom (23, 2)
  let e5 : LowMeanIntegerExpr := .neg (-23, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-7, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1659, 500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (52251, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (9853, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (49, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (482797, 40000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-482797, 40000000) e11
  let e13 : LowMeanIntegerExpr := .add (1607243, 40000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (1743, 100000)
  let e15 : LowMeanIntegerExpr := .atom (23, 48)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (103, 203)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-23, 48) e15
  let e21 : LowMeanIntegerExpr := .add (25, 48) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (575, 2304) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-103, 203) e17
  let e24 : LowMeanIntegerExpr := .add (100, 203) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (10300, 41209) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (10300, 41209) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1, 4) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (1743, 400000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (1743, 50000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (3001643, 40000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (8967, 10000)
  let e33 : LowMeanIntegerExpr := .pow (152587890625, 28179280429056) e21 8
  let e34 : LowMeanIntegerExpr := .mul (729736328125, 150289495621632) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-729736328125, 150289495621632) e34
  let e36 : LowMeanIntegerExpr := .add (824074139416410823, 11741366845440000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (824191553084865223, 11741366845440000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-824074139416410823, 11741366845440000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0172 : LowMeanDirectSeedInput :=
  { record := 172, positions := [{ j := 2, mode := 0, left := 483, right := 0 }, { j := 6, mode := 0, left := 484, right := 0 }], target := { R := 8, expr := lowMeanSeedTargetExpr0172 } }

noncomputable def lowMeanSeedTargetExpr0173 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (55569, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (237, 250000)
  let e3 : LowMeanIntegerExpr := .atom (9, 1)
  let e4 : LowMeanIntegerExpr := .atom (23, 2)
  let e5 : LowMeanIntegerExpr := .neg (-23, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-5, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-237, 100000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (53199, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (9853, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (25, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (9853, 1600000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-9853, 1600000) e11
  let e13 : LowMeanIntegerExpr := .add (376327, 8000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (1743, 100000)
  let e15 : LowMeanIntegerExpr := .atom (23, 48)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (103, 203)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-23, 48) e15
  let e21 : LowMeanIntegerExpr := .add (25, 48) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (575, 2304) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-103, 203) e17
  let e24 : LowMeanIntegerExpr := .add (100, 203) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (10300, 41209) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (10300, 41209) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1, 4) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (1743, 400000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (15687, 400000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (690067, 8000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (8967, 10000)
  let e33 : LowMeanIntegerExpr := .pow (3814697265625, 1352605460594688) e21 9
  let e34 : LowMeanIntegerExpr := .mul (18243408203125, 7213895789838336) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-18243408203125, 7213895789838336) e34
  let e36 : LowMeanIntegerExpr := .add (9437742500744865251, 112717121716224000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (9438869671962027491, 112717121716224000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-9437742500744865251, 112717121716224000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0173 : LowMeanDirectSeedInput :=
  { record := 173, positions := [{ j := 2, mode := 0, left := 485, right := 0 }, { j := 3, mode := 0, left := 486, right := 0 }, { j := 6, mode := 0, left := 487, right := 0 }], target := { R := 9, expr := lowMeanSeedTargetExpr0173 } }

noncomputable def lowMeanSeedTargetExpr0174 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (55569, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (237, 250000)
  let e3 : LowMeanIntegerExpr := .atom (10, 1)
  let e4 : LowMeanIntegerExpr := .atom (23, 2)
  let e5 : LowMeanIntegerExpr := .neg (-23, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-3, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-711, 500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (54147, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (9853, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (9, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (88677, 40000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-88677, 40000000) e11
  let e13 : LowMeanIntegerExpr := .add (2077203, 40000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (1743, 100000)
  let e15 : LowMeanIntegerExpr := .atom (23, 48)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (103, 203)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-23, 48) e15
  let e21 : LowMeanIntegerExpr := .add (25, 48) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (575, 2304) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-103, 203) e17
  let e24 : LowMeanIntegerExpr := .add (100, 203) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (10300, 41209) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (10300, 41209) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1, 4) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (1743, 400000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (1743, 40000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (3820203, 40000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (8967, 10000)
  let e33 : LowMeanIntegerExpr := .pow (95367431640625, 64925062108545024) e21 10
  let e34 : LowMeanIntegerExpr := .mul (456085205078125, 346266997912240128) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-456085205078125, 346266997912240128) e34
  let e36 : LowMeanIntegerExpr := .add (2547982062543375925207, 27052109211893760000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (2548252583635494862807, 27052109211893760000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-2547982062543375925207, 27052109211893760000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0174 : LowMeanDirectSeedInput :=
  { record := 174, positions := [{ j := 3, mode := 0, left := 488, right := 0 }, { j := 6, mode := 0, left := 489, right := 0 }, { j := 7, mode := 0, left := 490, right := 0 }], target := { R := 10, expr := lowMeanSeedTargetExpr0174 } }

noncomputable def lowMeanSeedTargetExpr0175 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (55569, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (237, 250000)
  let e3 : LowMeanIntegerExpr := .atom (11, 1)
  let e4 : LowMeanIntegerExpr := .atom (23, 2)
  let e5 : LowMeanIntegerExpr := .neg (-23, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-1, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-237, 500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (11019, 200000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (9853, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (1, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (9853, 40000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-9853, 40000000) e11
  let e13 : LowMeanIntegerExpr := .add (2193947, 40000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (1743, 100000)
  let e15 : LowMeanIntegerExpr := .atom (23, 48)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (103, 203)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-23, 48) e15
  let e21 : LowMeanIntegerExpr := .add (25, 48) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (575, 2304) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-103, 203) e17
  let e24 : LowMeanIntegerExpr := .add (100, 203) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (10300, 41209) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (10300, 41209) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1, 4) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (1743, 400000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (19173, 400000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (4111247, 40000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (8967, 10000)
  let e33 : LowMeanIntegerExpr := .pow (2384185791015625, 3116402981210161152) e21 11
  let e34 : LowMeanIntegerExpr := .mul (11402130126953125, 16620815899787526144) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-11402130126953125, 16620815899787526144) e34
  let e36 : LowMeanIntegerExpr := .add (132570691993116489251839, 1298501242170900480000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (132583677005538198256639, 1298501242170900480000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-132570691993116489251839, 1298501242170900480000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0175 : LowMeanDirectSeedInput :=
  { record := 175, positions := [{ j := 3, mode := 0, left := 491, right := 0 }, { j := 4, mode := 0, left := 492, right := 0 }, { j := 7, mode := 0, left := 493, right := 0 }], target := { R := 11, expr := lowMeanSeedTargetExpr0175 } }

noncomputable def lowMeanSeedGroup0160 : List LowMeanDirectSeedInput := [lowMeanSeedRecord0160, lowMeanSeedRecord0161, lowMeanSeedRecord0162, lowMeanSeedRecord0163, lowMeanSeedRecord0164, lowMeanSeedRecord0165, lowMeanSeedRecord0166, lowMeanSeedRecord0167, lowMeanSeedRecord0168, lowMeanSeedRecord0169, lowMeanSeedRecord0170, lowMeanSeedRecord0171, lowMeanSeedRecord0172, lowMeanSeedRecord0173, lowMeanSeedRecord0174, lowMeanSeedRecord0175]

end Erdos993Lean.Analytic.V213
