module

public import Erdos993Lean.Analytic.V213.LowMeanCoreAll
public import Erdos993Lean.Analytic.V213.LowMeanData.Seed0240
public import Erdos993Lean.Analytic.V213.LowMeanFiberSeed
public import Erdos993Lean.Analytic.V213.LowMeanIntegerExpr
public import Erdos993Lean.Analytic.V213.LowMeanSeedGeometry
public import Erdos993Lean.Analytic.V213.LowMeanWidthData
public import Erdos993Lean.Ceiling.Prefix
public import Erdos993Lean.Ceiling.Statement

/-! Exact core/budget keys and equation-51 targets for the direct fibers. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanSeedTargetExpr0288 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (15941, 500000)
  let e2 : LowMeanIntegerExpr := .atom (277, 250000)
  let e3 : LowMeanIntegerExpr := .atom (13, 1)
  let e4 : LowMeanIntegerExpr := .atom (65, 4)
  let e5 : LowMeanIntegerExpr := .neg (-65, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-13, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-3601, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (28281, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1707, 5000000)
  let e10 : LowMeanIntegerExpr := .pow (169, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (288483, 80000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-288483, 80000000) e11
  let e13 : LowMeanIntegerExpr := .add (1973997, 80000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (3671, 500000)
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
  let e29 : LowMeanIntegerExpr := .mul (392797, 214245000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (5106361, 214245000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (166285573453, 3427920000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1679, 1000)
  let e33 : LowMeanIntegerExpr := .pow (100000000000000000000000000, 1281192804641574310961385893007) e21 13
  let e34 : LowMeanIntegerExpr := .mul (7300000000000000000000000, 55704034984416274389625473609) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-7300000000000000000000000, 55704034984416274389625473609) e34
  let e36 : LowMeanIntegerExpr := .add (215588545474331585459279549883761173, 4456322798753301951170037888720000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (215633108702319118478791250262648373, 4456322798753301951170037888720000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-215588545474331585459279549883761173, 4456322798753301951170037888720000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0288 : LowMeanDirectSeedInput :=
  { record := 288, positions := [], target := { R := 13, expr := lowMeanSeedTargetExpr0288 } }

noncomputable def lowMeanSeedTargetExpr0289 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (15941, 500000)
  let e2 : LowMeanIntegerExpr := .atom (277, 250000)
  let e3 : LowMeanIntegerExpr := .atom (14, 1)
  let e4 : LowMeanIntegerExpr := .atom (65, 4)
  let e5 : LowMeanIntegerExpr := .neg (-65, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-9, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-2493, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (29389, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1707, 5000000)
  let e10 : LowMeanIntegerExpr := .pow (81, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (138267, 80000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-138267, 80000000) e11
  let e13 : LowMeanIntegerExpr := .add (2212853, 80000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (3671, 500000)
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
  let e29 : LowMeanIntegerExpr := .mul (392797, 214245000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (2749579, 107122500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (182805066197, 3427920000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1679, 1000)
  let e33 : LowMeanIntegerExpr := .pow (10000000000000000000000000000, 265206910560805882369006879852449) e21 14
  let e34 : LowMeanIntegerExpr := .mul (730000000000000000000000000, 11530735241774168798652473037063) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-730000000000000000000000000, 11530735241774168798652473037063) e34
  let e36 : LowMeanIntegerExpr := .add (49134739143798168614490823541694306739, 922458819341933503892197842965040000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (49143963731991587949529745520123957139, 922458819341933503892197842965040000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-49134739143798168614490823541694306739, 922458819341933503892197842965040000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0289 : LowMeanDirectSeedInput :=
  { record := 289, positions := [], target := { R := 14, expr := lowMeanSeedTargetExpr0289 } }

noncomputable def lowMeanSeedTargetExpr0290 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (15941, 500000)
  let e2 : LowMeanIntegerExpr := .atom (277, 250000)
  let e3 : LowMeanIntegerExpr := .atom (15, 1)
  let e4 : LowMeanIntegerExpr := .atom (65, 4)
  let e5 : LowMeanIntegerExpr := .neg (-65, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-5, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-277, 200000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (30497, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1707, 5000000)
  let e10 : LowMeanIntegerExpr := .pow (25, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1707, 3200000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1707, 3200000) e11
  let e13 : LowMeanIntegerExpr := .add (479417, 16000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (3671, 500000)
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
  let e29 : LowMeanIntegerExpr := .mul (392797, 214245000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (392797, 14283000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (13132265011, 228528000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1679, 1000)
  let e33 : LowMeanIntegerExpr := .pow (1000000000000000000000000000000, 54897830486086817650384424129456943) e21 15
  let e34 : LowMeanIntegerExpr := .mul (73000000000000000000000000000, 2386862195047252941321061918672041) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-73000000000000000000000000000, 2386862195047252941321061918672041) e34
  let e36 : LowMeanIntegerExpr := .add (2193392448792109311277561965409323784097, 38189795120756047061136990698752656000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (2193774346743316871748173335316311310657, 38189795120756047061136990698752656000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-2193392448792109311277561965409323784097, 38189795120756047061136990698752656000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0290 : LowMeanDirectSeedInput :=
  { record := 290, positions := [{ j := 6, mode := 0, left := 636, right := 0 }, { j := 10, mode := 0, left := 637, right := 0 }], target := { R := 15, expr := lowMeanSeedTargetExpr0290 } }

noncomputable def lowMeanSeedTargetExpr0291 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (15941, 500000)
  let e2 : LowMeanIntegerExpr := .atom (277, 250000)
  let e3 : LowMeanIntegerExpr := .atom (16, 1)
  let e4 : LowMeanIntegerExpr := .atom (65, 4)
  let e5 : LowMeanIntegerExpr := .neg (-65, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-1, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-277, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (6321, 200000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1707, 5000000)
  let e10 : LowMeanIntegerExpr := .pow (1, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1707, 80000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1707, 80000000) e11
  let e13 : LowMeanIntegerExpr := .add (2526693, 80000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (3671, 500000)
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
  let e29 : LowMeanIntegerExpr := .mul (392797, 214245000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (785594, 26780625) e29 e3
  let e31 : LowMeanIntegerExpr := .add (208822300357, 3427920000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1679, 1000)
  let e33 : LowMeanIntegerExpr := .pow (100000000000000000000000000000000, 11363850910619971253629575794797587201) e21 16
  let e34 : LowMeanIntegerExpr := .mul (7300000000000000000000000000000, 494080474374781358853459817165112487) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-7300000000000000000000000000000, 494080474374781358853459817165112487) e34
  let e36 : LowMeanIntegerExpr := .add (2407290657994810490436224581406413779131491, 39526437949982508708276785373208998960000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (2407685922374310315523307349260145869121091, 39526437949982508708276785373208998960000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-2407290657994810490436224581406413779131491, 39526437949982508708276785373208998960000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0291 : LowMeanDirectSeedInput :=
  { record := 291, positions := [{ j := 10, mode := 0, left := 638, right := 0 }], target := { R := 16, expr := lowMeanSeedTargetExpr0291 } }

noncomputable def lowMeanSeedTargetExpr0292 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (15941, 500000)
  let e2 : LowMeanIntegerExpr := .atom (277, 250000)
  let e3 : LowMeanIntegerExpr := .atom (17, 1)
  let e4 : LowMeanIntegerExpr := .atom (65, 4)
  let e5 : LowMeanIntegerExpr := .neg (-65, 4) e4
  let e6 : LowMeanIntegerExpr := .add (3, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (831, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (32713, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1707, 5000000)
  let e10 : LowMeanIntegerExpr := .pow (9, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (15363, 80000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-15363, 80000000) e11
  let e13 : LowMeanIntegerExpr := .add (2601677, 80000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (3671, 500000)
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
  let e29 : LowMeanIntegerExpr := .mul (392797, 214245000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (6677549, 214245000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (218320041773, 3427920000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1679, 1000)
  let e33 : LowMeanIntegerExpr := .pow (10000000000000000000000000000000000, 2352317138498334049501322189523100550607) e21 17
  let e34 : LowMeanIntegerExpr := .mul (730000000000000000000000000000000, 102274658195579741282666182153178284809) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-730000000000000000000000000000000, 102274658195579741282666182153178284809) e34
  let e36 : LowMeanIntegerExpr := .add (521041454129110735858111355889199519807168693, 8181972655646379302613294572254262784720000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (521123273855667199651137488834922062435015893, 8181972655646379302613294572254262784720000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-521041454129110735858111355889199519807168693, 8181972655646379302613294572254262784720000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0292 : LowMeanDirectSeedInput :=
  { record := 292, positions := [{ j := 7, mode := 0, left := 639, right := 0 }, { j := 11, mode := 0, left := 640, right := 0 }], target := { R := 17, expr := lowMeanSeedTargetExpr0292 } }

noncomputable def lowMeanSeedTargetExpr0293 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (15941, 500000)
  let e2 : LowMeanIntegerExpr := .atom (277, 250000)
  let e3 : LowMeanIntegerExpr := .atom (18, 1)
  let e4 : LowMeanIntegerExpr := .atom (65, 4)
  let e5 : LowMeanIntegerExpr := .neg (-65, 4) e4
  let e6 : LowMeanIntegerExpr := .add (7, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (1939, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (33821, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1707, 5000000)
  let e10 : LowMeanIntegerExpr := .pow (49, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (83643, 80000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-83643, 80000000) e11
  let e13 : LowMeanIntegerExpr := .add (2622037, 80000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (3671, 500000)
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
  let e29 : LowMeanIntegerExpr := .mul (392797, 214245000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (392797, 11902500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (25053022157, 380880000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1679, 1000)
  let e33 : LowMeanIntegerExpr := .pow (1000000000000000000000000000000000000, 486929647669155148246773693231281813975649) e21 18
  let e34 : LowMeanIntegerExpr := .mul (73000000000000000000000000000000000, 21170854246485006445511899705707904955463) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-73000000000000000000000000000000000, 21170854246485006445511899705707904955463) e34
  let e36 : LowMeanIntegerExpr := .add (111398041646672212948476672239920588577875370131, 1693668339718800515640951976456632396437040000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (111414978330069400953633081759685154901839740531, 1693668339718800515640951976456632396437040000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-111398041646672212948476672239920588577875370131, 1693668339718800515640951976456632396437040000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0293 : LowMeanDirectSeedInput :=
  { record := 293, positions := [{ j := 8, mode := 0, left := 641, right := 0 }, { j := 11, mode := 0, left := 642, right := 0 }], target := { R := 18, expr := lowMeanSeedTargetExpr0293 } }

noncomputable def lowMeanSeedTargetExpr0294 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (15941, 500000)
  let e2 : LowMeanIntegerExpr := .atom (277, 250000)
  let e3 : LowMeanIntegerExpr := .atom (19, 1)
  let e4 : LowMeanIntegerExpr := .atom (65, 4)
  let e5 : LowMeanIntegerExpr := .neg (-65, 4) e4
  let e6 : LowMeanIntegerExpr := .add (11, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (3047, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (34929, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1707, 5000000)
  let e10 : LowMeanIntegerExpr := .pow (121, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (206547, 80000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-206547, 80000000) e11
  let e13 : LowMeanIntegerExpr := .add (2587773, 80000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (3671, 500000)
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
  let e29 : LowMeanIntegerExpr := .mul (392797, 214245000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (7463143, 214245000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (230293773277, 3427920000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1679, 1000)
  let e33 : LowMeanIntegerExpr := .pow (100000000000000000000000000000000000000, 100794437067515115687082154498875335492959343) e21 19
  let e34 : LowMeanIntegerExpr := .mul (7300000000000000000000000000000000000, 4382366829022396334220963239081536325780841) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-7300000000000000000000000000000000000, 4382366829022396334220963239081536325780841) e34
  let e36 : LowMeanIntegerExpr := .add (23552632946475510862524642922859223606763579249093, 350589346321791706737677059126522906062467280000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (23556138839938728779592019693450488835824203921893, 350589346321791706737677059126522906062467280000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-23552632946475510862524642922859223606763579249093, 350589346321791706737677059126522906062467280000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0294 : LowMeanDirectSeedInput :=
  { record := 294, positions := [{ j := 9, mode := 0, left := 643, right := 0 }, { j := 11, mode := 0, left := 644, right := 0 }], target := { R := 19, expr := lowMeanSeedTargetExpr0294 } }

noncomputable def lowMeanSeedTargetExpr0295 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (15941, 500000)
  let e2 : LowMeanIntegerExpr := .atom (277, 250000)
  let e3 : LowMeanIntegerExpr := .atom (20, 1)
  let e4 : LowMeanIntegerExpr := .atom (65, 4)
  let e5 : LowMeanIntegerExpr := .neg (-65, 4) e4
  let e6 : LowMeanIntegerExpr := .add (15, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (831, 200000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (36037, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1707, 5000000)
  let e10 : LowMeanIntegerExpr := .pow (225, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (15363, 3200000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-15363, 3200000) e11
  let e13 : LowMeanIntegerExpr := .add (499777, 16000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (3671, 500000)
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
  let e29 : LowMeanIntegerExpr := .mul (392797, 214245000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (392797, 10712250) e29 e3
  let e31 : LowMeanIntegerExpr := .add (46553952673, 685584000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1679, 1000)
  let e33 : LowMeanIntegerExpr := .pow (10000000000000000000000000000000000000000, 20864448472975628947226005981267194447042584001) e21 20
  let e34 : LowMeanIntegerExpr := .mul (730000000000000000000000000000000000000, 907149933607636041183739390489878019436634087) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-730000000000000000000000000000000000000, 907149933607636041183739390489878019436634087) e34
  let e36 : LowMeanIntegerExpr := .add (985575266637844066668460932157848435258606674802599, 14514398937722176658939830247838048310986145392000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (985720410627221288435050330460326815741716536256519, 14514398937722176658939830247838048310986145392000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-985575266637844066668460932157848435258606674802599, 14514398937722176658939830247838048310986145392000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0295 : LowMeanDirectSeedInput :=
  { record := 295, positions := [{ j := 9, mode := 0, left := 645, right := 0 }, { j := 12, mode := 0, left := 646, right := 0 }], target := { R := 20, expr := lowMeanSeedTargetExpr0295 } }

noncomputable def lowMeanSeedTargetExpr0296 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (15941, 500000)
  let e2 : LowMeanIntegerExpr := .atom (277, 250000)
  let e3 : LowMeanIntegerExpr := .atom (21, 1)
  let e4 : LowMeanIntegerExpr := .atom (65, 4)
  let e5 : LowMeanIntegerExpr := .neg (-65, 4) e4
  let e6 : LowMeanIntegerExpr := .add (19, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (5263, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (7429, 200000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1707, 5000000)
  let e10 : LowMeanIntegerExpr := .pow (361, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (616227, 80000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-616227, 80000000) e11
  let e13 : LowMeanIntegerExpr := .add (2355373, 80000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (3671, 500000)
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
  let e29 : LowMeanIntegerExpr := .mul (392797, 214245000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (2749579, 71415000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (77635056559, 1142640000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1679, 1000)
  let e33 : LowMeanIntegerExpr := .pow (1000000000000000000000000000000000000000000, 4318940833905955192075783238122309250537814888207) e21 21
  let e34 : LowMeanIntegerExpr := .mul (73000000000000000000000000000000000000000, 187780036256780660525034053831404750023383256009) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-73000000000000000000000000000000000000000, 187780036256780660525034053831404750023383256009) e34
  let e36 : LowMeanIntegerExpr := .add (1020670049900317666254876244808664735593825922620758357, 15022402900542452842002724306512380001870660480720000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (1020820273929323090783296272051729859393844629225565557, 15022402900542452842002724306512380001870660480720000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-1020670049900317666254876244808664735593825922620758357, 15022402900542452842002724306512380001870660480720000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0296 : LowMeanDirectSeedInput :=
  { record := 296, positions := [{ j := 10, mode := 0, left := 647, right := 0 }, { j := 12, mode := 0, left := 648, right := 0 }], target := { R := 21, expr := lowMeanSeedTargetExpr0296 } }

noncomputable def lowMeanSeedTargetExpr0297 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (89731, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (-467, 125000)
  let e3 : LowMeanIntegerExpr := .atom (0, 1)
  let e4 : LowMeanIntegerExpr := .atom (8, 1)
  let e5 : LowMeanIntegerExpr := .neg (-8, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-8, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (467, 15625) e2 e6
  let e8 : LowMeanIntegerExpr := .add (119619, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (289, 200000)
  let e10 : LowMeanIntegerExpr := .pow (64, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (289, 3125) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-289, 3125) e11
  let e13 : LowMeanIntegerExpr := .add (27139, 1000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (3873, 100000)
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
  let e29 : LowMeanIntegerExpr := .mul (14201, 1470000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (0, 1) e29 e3
  let e31 : LowMeanIntegerExpr := .add (27139, 1000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (4759, 5000)
  let e33 : LowMeanIntegerExpr := .pow (1, 1) e21 0
  let e34 : LowMeanIntegerExpr := .mul (4759, 5000) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-4759, 5000) e34
  let e36 : LowMeanIntegerExpr := .add (-924661, 1000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-924651, 1000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (924661, 1000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0297 : LowMeanDirectSeedInput :=
  { record := 297, positions := [], target := { R := 0, expr := lowMeanSeedTargetExpr0297 } }

noncomputable def lowMeanSeedTargetExpr0298 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (89731, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (-467, 125000)
  let e3 : LowMeanIntegerExpr := .atom (1, 1)
  let e4 : LowMeanIntegerExpr := .atom (8, 1)
  let e5 : LowMeanIntegerExpr := .neg (-8, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-7, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (3269, 125000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (115883, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (289, 200000)
  let e10 : LowMeanIntegerExpr := .pow (49, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (14161, 200000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-14161, 200000) e11
  let e13 : LowMeanIntegerExpr := .add (22539, 500000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (3873, 100000)
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
  let e28 : LowMeanIntegerExpr := .mul (14201, 1470000) e14 e27
  let e29 : LowMeanIntegerExpr := .mul (14201, 1470000) e28 e3
  let e30 : LowMeanIntegerExpr := .add (4023283, 73500000) e13 e29
  let e31 : LowMeanIntegerExpr := .atom (4759, 5000)
  let e32 : LowMeanIntegerExpr := .pow (10, 21) e20 1
  let e33 : LowMeanIntegerExpr := .mul (4759, 10500) e31 e32
  let e34 : LowMeanIntegerExpr := .neg (-4759, 10500) e33
  let e35 : LowMeanIntegerExpr := .add (-9763239, 24500000) e30 e34
  let e36 : LowMeanIntegerExpr := .add (-4881497, 12250000) e0 e35
  let e37 : LowMeanIntegerExpr := .neg (9763239, 24500000) e35
  let e38 : LowMeanIntegerExpr := .add (1, 100000) e36 e37
  e38

noncomputable def lowMeanSeedRecord0298 : LowMeanDirectSeedInput :=
  { record := 298, positions := [], target := { R := 1, expr := lowMeanSeedTargetExpr0298 } }

noncomputable def lowMeanSeedTargetExpr0299 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (89731, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (-467, 125000)
  let e3 : LowMeanIntegerExpr := .atom (2, 1)
  let e4 : LowMeanIntegerExpr := .atom (8, 1)
  let e5 : LowMeanIntegerExpr := .neg (-8, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-6, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (1401, 62500) e2 e6
  let e8 : LowMeanIntegerExpr := .add (112147, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (289, 200000)
  let e10 : LowMeanIntegerExpr := .pow (36, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (2601, 50000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-2601, 50000) e11
  let e13 : LowMeanIntegerExpr := .add (60127, 1000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (3873, 100000)
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
  let e29 : LowMeanIntegerExpr := .mul (14201, 1470000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (14201, 735000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (11678869, 147000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (4759, 5000)
  let e33 : LowMeanIntegerExpr := .pow (100, 441) e21 2
  let e34 : LowMeanIntegerExpr := .mul (4759, 22050) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-4759, 22050) e34
  let e36 : LowMeanIntegerExpr := .add (-60143393, 441000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-60138983, 441000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (60143393, 441000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0299 : LowMeanDirectSeedInput :=
  { record := 299, positions := [], target := { R := 2, expr := lowMeanSeedTargetExpr0299 } }

noncomputable def lowMeanSeedTargetExpr0300 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (89731, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (-467, 125000)
  let e3 : LowMeanIntegerExpr := .atom (3, 1)
  let e4 : LowMeanIntegerExpr := .atom (8, 1)
  let e5 : LowMeanIntegerExpr := .neg (-8, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-5, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (467, 25000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (108411, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (289, 200000)
  let e10 : LowMeanIntegerExpr := .pow (25, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (289, 8000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-289, 8000) e11
  let e13 : LowMeanIntegerExpr := .add (36143, 500000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (3873, 100000)
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
  let e29 : LowMeanIntegerExpr := .mul (14201, 1470000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (14201, 490000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (2481057, 24500000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (4759, 5000)
  let e33 : LowMeanIntegerExpr := .pow (1000, 9261) e21 3
  let e34 : LowMeanIntegerExpr := .mul (4759, 46305) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-4759, 46305) e34
  let e36 : LowMeanIntegerExpr := .add (-6980227, 4630500000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-3466961, 2315250000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (6980227, 4630500000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0300 : LowMeanDirectSeedInput :=
  { record := 300, positions := [{ j := 0, mode := 0, left := 649, right := 0 }], target := { R := 3, expr := lowMeanSeedTargetExpr0300 } }

noncomputable def lowMeanSeedTargetExpr0301 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (89731, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (-467, 125000)
  let e3 : LowMeanIntegerExpr := .atom (4, 1)
  let e4 : LowMeanIntegerExpr := .atom (8, 1)
  let e5 : LowMeanIntegerExpr := .neg (-8, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-4, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (467, 31250) e2 e6
  let e8 : LowMeanIntegerExpr := .add (4187, 40000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (289, 200000)
  let e10 : LowMeanIntegerExpr := .pow (16, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (289, 12500) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-289, 12500) e11
  let e13 : LowMeanIntegerExpr := .add (16311, 200000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (3873, 100000)
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
  let e29 : LowMeanIntegerExpr := .mul (14201, 1470000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (14201, 367500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (3533797, 29400000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (4759, 5000)
  let e33 : LowMeanIntegerExpr := .pow (10000, 194481) e21 4
  let e34 : LowMeanIntegerExpr := .mul (9518, 194481) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-9518, 194481) e34
  let e36 : LowMeanIntegerExpr := .add (2771613431, 38896200000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (2772002393, 38896200000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-2771613431, 38896200000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0301 : LowMeanDirectSeedInput :=
  { record := 301, positions := [{ j := 1, mode := 0, left := 650, right := 0 }, { j := 4, mode := 0, left := 651, right := 0 }], target := { R := 4, expr := lowMeanSeedTargetExpr0301 } }

noncomputable def lowMeanSeedTargetExpr0302 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (89731, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (-467, 125000)
  let e3 : LowMeanIntegerExpr := .atom (5, 1)
  let e4 : LowMeanIntegerExpr := .atom (8, 1)
  let e5 : LowMeanIntegerExpr := .neg (-8, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-3, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (1401, 125000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (100939, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (289, 200000)
  let e10 : LowMeanIntegerExpr := .pow (9, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (2601, 200000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-2601, 200000) e11
  let e13 : LowMeanIntegerExpr := .add (43967, 500000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (3873, 100000)
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
  let e29 : LowMeanIntegerExpr := .mul (14201, 1470000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (14201, 294000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (10013399, 73500000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (4759, 5000)
  let e33 : LowMeanIntegerExpr := .pow (100000, 4084101) e21 5
  let e34 : LowMeanIntegerExpr := .mul (95180, 4084101) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-95180, 4084101) e34
  let e36 : LowMeanIntegerExpr := .add (230612264417, 2042050500000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (115316342461, 1021025250000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-230612264417, 2042050500000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0302 : LowMeanDirectSeedInput :=
  { record := 302, positions := [{ j := 1, mode := 0, left := 652, right := 0 }, { j := 5, mode := 0, left := 653, right := 0 }], target := { R := 5, expr := lowMeanSeedTargetExpr0302 } }

noncomputable def lowMeanSeedTargetExpr0303 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (89731, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (-467, 125000)
  let e3 : LowMeanIntegerExpr := .atom (6, 1)
  let e4 : LowMeanIntegerExpr := .atom (8, 1)
  let e5 : LowMeanIntegerExpr := .neg (-8, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-2, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (467, 62500) e2 e6
  let e8 : LowMeanIntegerExpr := .add (97203, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (289, 200000)
  let e10 : LowMeanIntegerExpr := .pow (4, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (289, 50000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-289, 50000) e11
  let e13 : LowMeanIntegerExpr := .add (91423, 1000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (3873, 100000)
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
  let e29 : LowMeanIntegerExpr := .mul (14201, 1470000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (14201, 245000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (7319927, 49000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (4759, 5000)
  let e33 : LowMeanIntegerExpr := .pow (1000000, 85766121) e21 6
  let e34 : LowMeanIntegerExpr := .mul (951800, 85766121) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-951800, 85766121) e34
  let e36 : LowMeanIntegerExpr := .add (11860480505983, 85766121000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (11861338167193, 85766121000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-11860480505983, 85766121000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0303 : LowMeanDirectSeedInput :=
  { record := 303, positions := [{ j := 2, mode := 0, left := 654, right := 0 }, { j := 5, mode := 0, left := 655, right := 0 }], target := { R := 6, expr := lowMeanSeedTargetExpr0303 } }

noncomputable def lowMeanSeedGroup0288 : List LowMeanDirectSeedInput := [lowMeanSeedRecord0288, lowMeanSeedRecord0289, lowMeanSeedRecord0290, lowMeanSeedRecord0291, lowMeanSeedRecord0292, lowMeanSeedRecord0293, lowMeanSeedRecord0294, lowMeanSeedRecord0295, lowMeanSeedRecord0296, lowMeanSeedRecord0297, lowMeanSeedRecord0298, lowMeanSeedRecord0299, lowMeanSeedRecord0300, lowMeanSeedRecord0301, lowMeanSeedRecord0302, lowMeanSeedRecord0303]

end Erdos993Lean.Analytic.V213
