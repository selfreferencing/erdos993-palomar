module

public import Erdos993Lean.Analytic.V213.LowMeanCoreAll
public import Erdos993Lean.Analytic.V213.LowMeanData.Seed0176
public import Erdos993Lean.Analytic.V213.LowMeanFiberSeed
public import Erdos993Lean.Analytic.V213.LowMeanIntegerExpr
public import Erdos993Lean.Analytic.V213.LowMeanSeedGeometry
public import Erdos993Lean.Analytic.V213.LowMeanWidthData
public import Erdos993Lean.Ceiling.Prefix
public import Erdos993Lean.Ceiling.Statement

/-! Exact core/budget keys and equation-51 targets for the direct fibers. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanSeedTargetExpr0272 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (867, 15625)
  let e2 : LowMeanIntegerExpr := .atom (771, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (12, 1)
  let e4 : LowMeanIntegerExpr := .atom (45, 4)
  let e5 : LowMeanIntegerExpr := .neg (-45, 4) e4
  let e6 : LowMeanIntegerExpr := .add (3, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (2313, 4000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (44853, 800000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (8851, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (9, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (79659, 160000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-79659, 160000000) e11
  let e13 : LowMeanIntegerExpr := .add (8890941, 160000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (4066, 77625) e29 e3
  let e31 : LowMeanIntegerExpr := .add (10725754361, 99360000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (909, 1000)
  let e33 : LowMeanIntegerExpr := .pow (1000000000000000000000000, 6189337220490697154402830401) e21 12
  let e34 : LowMeanIntegerExpr := .mul (101000000000000000000000, 687704135610077461600314489) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-101000000000000000000000, 687704135610077461600314489) e34
  let e36 : LowMeanIntegerExpr := .add (11861691258611149322556172575464149, 110032661697612393856050318240000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (11862791585228125446494733078646549, 110032661697612393856050318240000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-11861691258611149322556172575464149, 110032661697612393856050318240000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0272 : LowMeanDirectSeedInput :=
  { record := 272, positions := [{ j := 5, mode := 0, left := 625, right := 0 }, { j := 8, mode := 0, left := 626, right := 0 }], target := { R := 12, expr := lowMeanSeedTargetExpr0272 } }

noncomputable def lowMeanSeedTargetExpr0273 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (867, 15625)
  let e2 : LowMeanIntegerExpr := .atom (771, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (13, 1)
  let e4 : LowMeanIntegerExpr := .atom (45, 4)
  let e5 : LowMeanIntegerExpr := .neg (-45, 4) e4
  let e6 : LowMeanIntegerExpr := .add (7, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (5397, 4000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (227349, 4000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (8851, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (49, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (433699, 160000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-433699, 160000000) e11
  let e13 : LowMeanIntegerExpr := .add (8660261, 160000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (26429, 465750) e29 e3
  let e31 : LowMeanIntegerExpr := .add (33048626243, 298080000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (909, 1000)
  let e33 : LowMeanIntegerExpr := .pow (100000000000000000000000000, 1281192804641574310961385893007) e21 13
  let e34 : LowMeanIntegerExpr := .mul (10100000000000000000000000, 142354756071286034551265099223) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-10100000000000000000000000, 142354756071286034551265099223) e34
  let e36 : LowMeanIntegerExpr := .add (2523681438171426312522997577579837203, 22776760971405765528202415875680000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (2523909205781140370178279601738594003, 22776760971405765528202415875680000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-2523681438171426312522997577579837203, 22776760971405765528202415875680000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0273 : LowMeanDirectSeedInput :=
  { record := 273, positions := [{ j := 6, mode := 0, left := 627, right := 0 }, { j := 8, mode := 0, left := 628, right := 0 }], target := { R := 13, expr := lowMeanSeedTargetExpr0273 } }

noncomputable def lowMeanSeedTargetExpr0274 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (867, 15625)
  let e2 : LowMeanIntegerExpr := .atom (771, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (14, 1)
  let e4 : LowMeanIntegerExpr := .atom (45, 4)
  let e5 : LowMeanIntegerExpr := .neg (-45, 4) e4
  let e6 : LowMeanIntegerExpr := .add (11, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (8481, 4000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (230433, 4000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (8851, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (121, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1070971, 160000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1070971, 160000000) e11
  let e13 : LowMeanIntegerExpr := .add (8146349, 160000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (14231, 232875) e29 e3
  let e31 : LowMeanIntegerExpr := .add (33392328187, 298080000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (909, 1000)
  let e33 : LowMeanIntegerExpr := .pow (10000000000000000000000000000, 265206910560805882369006879852449) e21 14
  let e34 : LowMeanIntegerExpr := .mul (1010000000000000000000000000, 29467434506756209152111875539161) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1010000000000000000000000000, 29467434506756209152111875539161) e34
  let e36 : LowMeanIntegerExpr := .add (528011370412523781431740607699281633189, 4714789521080993464337900086265760000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (528058518307734591366383986700144290789, 4714789521080993464337900086265760000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-528011370412523781431740607699281633189, 4714789521080993464337900086265760000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0274 : LowMeanDirectSeedInput :=
  { record := 274, positions := [{ j := 7, mode := 0, left := 629, right := 0 }, { j := 8, mode := 0, left := 630, right := 0 }], target := { R := 14, expr := lowMeanSeedTargetExpr0274 } }

noncomputable def lowMeanSeedTargetExpr0275 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (15941, 500000)
  let e2 : LowMeanIntegerExpr := .atom (277, 250000)
  let e3 : LowMeanIntegerExpr := .atom (0, 1)
  let e4 : LowMeanIntegerExpr := .atom (65, 4)
  let e5 : LowMeanIntegerExpr := .neg (-65, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-65, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-3601, 200000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (13877, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1707, 5000000)
  let e10 : LowMeanIntegerExpr := .pow (4225, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (288483, 3200000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-288483, 3200000) e11
  let e13 : LowMeanIntegerExpr := .add (-1220383, 16000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (0, 1) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-1220383, 16000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1679, 1000)
  let e33 : LowMeanIntegerExpr := .pow (1, 1) e21 0
  let e34 : LowMeanIntegerExpr := .mul (1679, 1000) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1679, 1000) e34
  let e36 : LowMeanIntegerExpr := .add (-28084383, 16000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-28084223, 16000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (28084383, 16000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0275 : LowMeanDirectSeedInput :=
  { record := 275, positions := [], target := { R := 0, expr := lowMeanSeedTargetExpr0275 } }

noncomputable def lowMeanSeedTargetExpr0276 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (15941, 500000)
  let e2 : LowMeanIntegerExpr := .atom (277, 250000)
  let e3 : LowMeanIntegerExpr := .atom (1, 1)
  let e4 : LowMeanIntegerExpr := .atom (65, 4)
  let e5 : LowMeanIntegerExpr := .neg (-65, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-61, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-16897, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (2997, 200000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1707, 5000000)
  let e10 : LowMeanIntegerExpr := .pow (3721, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (6351747, 80000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-6351747, 80000000) e11
  let e13 : LowMeanIntegerExpr := .add (-5152947, 80000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (3671, 500000)
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
  let e28 : LowMeanIntegerExpr := .mul (392797, 214245000) e14 e27
  let e29 : LowMeanIntegerExpr := .mul (392797, 214245000) e28 e3
  let e30 : LowMeanIntegerExpr := .add (-214513874003, 3427920000000) e13 e29
  let e31 : LowMeanIntegerExpr := .atom (1679, 1000)
  let e32 : LowMeanIntegerExpr := .pow (100, 207) e20 1
  let e33 : LowMeanIntegerExpr := .mul (73, 90) e31 e32
  let e34 : LowMeanIntegerExpr := .neg (-73, 90) e33
  let e35 : LowMeanIntegerExpr := .add (-2994937874003, 3427920000000) e30 e34
  let e36 : LowMeanIntegerExpr := .add (-2994903594803, 3427920000000) e0 e35
  let e37 : LowMeanIntegerExpr := .neg (2994937874003, 3427920000000) e35
  let e38 : LowMeanIntegerExpr := .add (1, 100000) e36 e37
  e38

noncomputable def lowMeanSeedRecord0276 : LowMeanDirectSeedInput :=
  { record := 276, positions := [], target := { R := 1, expr := lowMeanSeedTargetExpr0276 } }

noncomputable def lowMeanSeedTargetExpr0277 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (15941, 500000)
  let e2 : LowMeanIntegerExpr := .atom (277, 250000)
  let e3 : LowMeanIntegerExpr := .atom (2, 1)
  let e4 : LowMeanIntegerExpr := .atom (65, 4)
  let e5 : LowMeanIntegerExpr := .neg (-65, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-57, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-15789, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (16093, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1707, 5000000)
  let e10 : LowMeanIntegerExpr := .pow (3249, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (5546043, 80000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-5546043, 80000000) e11
  let e13 : LowMeanIntegerExpr := .add (-4258603, 80000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (392797, 107122500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-169907375947, 3427920000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1679, 1000)
  let e33 : LowMeanIntegerExpr := .pow (10000, 42849) e21 2
  let e34 : LowMeanIntegerExpr := .mul (730, 1863) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-730, 1863) e34
  let e36 : LowMeanIntegerExpr := .add (-1513107375947, 3427920000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-1513073096747, 3427920000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (1513107375947, 3427920000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0277 : LowMeanDirectSeedInput :=
  { record := 277, positions := [], target := { R := 2, expr := lowMeanSeedTargetExpr0277 } }

noncomputable def lowMeanSeedTargetExpr0278 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (15941, 500000)
  let e2 : LowMeanIntegerExpr := .atom (277, 250000)
  let e3 : LowMeanIntegerExpr := .atom (3, 1)
  let e4 : LowMeanIntegerExpr := .atom (65, 4)
  let e5 : LowMeanIntegerExpr := .neg (-65, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-53, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-14681, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (17201, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1707, 5000000)
  let e10 : LowMeanIntegerExpr := .pow (2809, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (4794963, 80000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-4794963, 80000000) e11
  let e13 : LowMeanIntegerExpr := .add (-3418883, 80000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (392797, 71415000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-42547153889, 1142640000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1679, 1000)
  let e33 : LowMeanIntegerExpr := .pow (1000000, 8869743) e21 3
  let e34 : LowMeanIntegerExpr := .mul (73000, 385641) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-73000, 385641) e34
  let e36 : LowMeanIntegerExpr := .add (-6988773155003, 30851280000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-6988464642203, 30851280000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (6988773155003, 30851280000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0278 : LowMeanDirectSeedInput :=
  { record := 278, positions := [], target := { R := 3, expr := lowMeanSeedTargetExpr0278 } }

noncomputable def lowMeanSeedTargetExpr0279 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (15941, 500000)
  let e2 : LowMeanIntegerExpr := .atom (277, 250000)
  let e3 : LowMeanIntegerExpr := .atom (4, 1)
  let e4 : LowMeanIntegerExpr := .atom (65, 4)
  let e5 : LowMeanIntegerExpr := .neg (-65, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-49, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-13573, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (18309, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1707, 5000000)
  let e10 : LowMeanIntegerExpr := .pow (2401, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (4098507, 80000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-4098507, 80000000) e11
  let e13 : LowMeanIntegerExpr := .add (-2633787, 80000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (392797, 53561250) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-87716131163, 3427920000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1679, 1000)
  let e33 : LowMeanIntegerExpr := .pow (100000000, 1836036801) e21 4
  let e34 : LowMeanIntegerExpr := .mul (7300000, 79827687) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-7300000, 79827687) e34
  let e36 : LowMeanIntegerExpr := .add (-747415152356669, 6386214960000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-747351290207069, 6386214960000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (747415152356669, 6386214960000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0279 : LowMeanDirectSeedInput :=
  { record := 279, positions := [], target := { R := 4, expr := lowMeanSeedTargetExpr0279 } }

noncomputable def lowMeanSeedTargetExpr0280 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (15941, 500000)
  let e2 : LowMeanIntegerExpr := .atom (277, 250000)
  let e3 : LowMeanIntegerExpr := .atom (5, 1)
  let e4 : LowMeanIntegerExpr := .atom (65, 4)
  let e5 : LowMeanIntegerExpr := .neg (-65, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-45, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-2493, 200000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (19417, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1707, 5000000)
  let e10 : LowMeanIntegerExpr := .pow (2025, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (138267, 3200000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-138267, 3200000) e11
  let e13 : LowMeanIntegerExpr := .add (-380663, 16000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (392797, 42849000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-10026276887, 685584000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1679, 1000)
  let e33 : LowMeanIntegerExpr := .pow (10000000000, 380059617807) e21 5
  let e34 : LowMeanIntegerExpr := .mul (730000000, 16524331209) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-730000000, 16524331209) e34
  let e36 : LowMeanIntegerExpr := .add (-15546543444979567, 264389299344000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-15543899551986127, 264389299344000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (15546543444979567, 264389299344000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0280 : LowMeanDirectSeedInput :=
  { record := 280, positions := [], target := { R := 5, expr := lowMeanSeedTargetExpr0280 } }

noncomputable def lowMeanSeedTargetExpr0281 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (15941, 500000)
  let e2 : LowMeanIntegerExpr := .atom (277, 250000)
  let e3 : LowMeanIntegerExpr := .atom (6, 1)
  let e4 : LowMeanIntegerExpr := .atom (65, 4)
  let e5 : LowMeanIntegerExpr := .neg (-65, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-41, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-11357, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (821, 40000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1707, 5000000)
  let e10 : LowMeanIntegerExpr := .pow (1681, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (2869467, 80000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-2869467, 80000000) e11
  let e13 : LowMeanIntegerExpr := .add (-1227467, 80000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (392797, 35707500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-4962407161, 1142640000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1679, 1000)
  let e33 : LowMeanIntegerExpr := .pow (1000000000000, 78672340886049) e21 6
  let e34 : LowMeanIntegerExpr := .mul (73000000000, 3420536560263) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-73000000000, 3420536560263) e34
  let e36 : LowMeanIntegerExpr := .add (-7028412456844599821, 273642924821040000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-7025676027596389421, 273642924821040000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (7028412456844599821, 273642924821040000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0281 : LowMeanDirectSeedInput :=
  { record := 281, positions := [{ j := 1, mode := 0, left := 631, right := 0 }], target := { R := 6, expr := lowMeanSeedTargetExpr0281 } }

noncomputable def lowMeanSeedTargetExpr0282 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (15941, 500000)
  let e2 : LowMeanIntegerExpr := .atom (277, 250000)
  let e3 : LowMeanIntegerExpr := .atom (7, 1)
  let e4 : LowMeanIntegerExpr := .atom (65, 4)
  let e5 : LowMeanIntegerExpr := .neg (-65, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-37, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-10249, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (21633, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1707, 5000000)
  let e10 : LowMeanIntegerExpr := .pow (1369, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (2336883, 80000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-2336883, 80000000) e11
  let e13 : LowMeanIntegerExpr := .add (-606243, 80000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (2749579, 214245000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (18016357693, 3427920000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1679, 1000)
  let e33 : LowMeanIntegerExpr := .pow (100000000000000, 16285174563412143) e21 7
  let e34 : LowMeanIntegerExpr := .mul (7300000000000, 708051067974441) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-7300000000000, 708051067974441) e34
  let e36 : LowMeanIntegerExpr := .add (-286291738301052859163, 56644085437955280000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-285725297446673306363, 56644085437955280000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (286291738301052859163, 56644085437955280000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0282 : LowMeanDirectSeedInput :=
  { record := 282, positions := [{ j := 6, mode := 0, left := 632, right := 0 }], target := { R := 7, expr := lowMeanSeedTargetExpr0282 } }

noncomputable def lowMeanSeedTargetExpr0283 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (15941, 500000)
  let e2 : LowMeanIntegerExpr := .atom (277, 250000)
  let e3 : LowMeanIntegerExpr := .atom (8, 1)
  let e4 : LowMeanIntegerExpr := .atom (65, 4)
  let e5 : LowMeanIntegerExpr := .neg (-65, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-33, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-9141, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (22741, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1707, 5000000)
  let e10 : LowMeanIntegerExpr := .pow (1089, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1858923, 80000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1858923, 80000000) e11
  let e13 : LowMeanIntegerExpr := .add (-39643, 80000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (392797, 26780625) e29 e3
  let e31 : LowMeanIntegerExpr := .add (48579353093, 3427920000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1679, 1000)
  let e33 : LowMeanIntegerExpr := .pow (10000000000000000, 3371031134626313601) e21 8
  let e34 : LowMeanIntegerExpr := .mul (730000000000000, 146566571070709287) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-730000000000000, 146566571070709287) e34
  let e36 : LowMeanIntegerExpr := .add (107767453328531949943459, 11725325685656742960000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (107884706585388517373059, 11725325685656742960000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-107767453328531949943459, 11725325685656742960000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0283 : LowMeanDirectSeedInput :=
  { record := 283, positions := [{ j := 2, mode := 0, left := 633, right := 0 }], target := { R := 8, expr := lowMeanSeedTargetExpr0283 } }

noncomputable def lowMeanSeedTargetExpr0284 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (15941, 500000)
  let e2 : LowMeanIntegerExpr := .atom (277, 250000)
  let e3 : LowMeanIntegerExpr := .atom (9, 1)
  let e4 : LowMeanIntegerExpr := .atom (65, 4)
  let e5 : LowMeanIntegerExpr := .neg (-65, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-29, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-8033, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (23849, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1707, 5000000)
  let e10 : LowMeanIntegerExpr := .pow (841, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1435587, 80000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1435587, 80000000) e11
  let e13 : LowMeanIntegerExpr := .add (472333, 80000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (392797, 23805000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (8533529413, 380880000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1679, 1000)
  let e33 : LowMeanIntegerExpr := .pow (1000000000000000000, 697803444867646915407) e21 9
  let e34 : LowMeanIntegerExpr := .mul (73000000000000000, 30339280211636822409) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-73000000000000000, 30339280211636822409) e34
  let e36 : LowMeanIntegerExpr := .add (48539571530193591451598197, 2427142416930945792720000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (48563842954362900909525397, 2427142416930945792720000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-48539571530193591451598197, 2427142416930945792720000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0284 : LowMeanDirectSeedInput :=
  { record := 284, positions := [{ j := 7, mode := 0, left := 634, right := 0 }], target := { R := 9, expr := lowMeanSeedTargetExpr0284 } }

noncomputable def lowMeanSeedTargetExpr0285 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (15941, 500000)
  let e2 : LowMeanIntegerExpr := .atom (277, 250000)
  let e3 : LowMeanIntegerExpr := .atom (10, 1)
  let e4 : LowMeanIntegerExpr := .atom (65, 4)
  let e5 : LowMeanIntegerExpr := .neg (-65, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-25, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-277, 40000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (24957, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1707, 5000000)
  let e10 : LowMeanIntegerExpr := .pow (625, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1707, 128000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1707, 128000) e11
  let e13 : LowMeanIntegerExpr := .add (185937, 16000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (392797, 21424500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (20536718513, 685584000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1679, 1000)
  let e33 : LowMeanIntegerExpr := .pow (100000000000000000000, 144445313087602911489249) e21 10
  let e34 : LowMeanIntegerExpr := .mul (7300000000000000000, 6280231003808822238663) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-7300000000000000000, 6280231003808822238663) e34
  let e36 : LowMeanIntegerExpr := .add (2893196413494765646373930231, 100483696060941155818608000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (2894201250455375057932116311, 100483696060941155818608000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-2893196413494765646373930231, 100483696060941155818608000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0285 : LowMeanDirectSeedInput :=
  { record := 285, positions := [{ j := 3, mode := 0, left := 635, right := 0 }], target := { R := 10, expr := lowMeanSeedTargetExpr0285 } }

noncomputable def lowMeanSeedTargetExpr0286 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (15941, 500000)
  let e2 : LowMeanIntegerExpr := .atom (277, 250000)
  let e3 : LowMeanIntegerExpr := .atom (11, 1)
  let e4 : LowMeanIntegerExpr := .atom (65, 4)
  let e5 : LowMeanIntegerExpr := .neg (-65, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-21, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-5817, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (5213, 200000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1707, 5000000)
  let e10 : LowMeanIntegerExpr := .pow (441, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (752787, 80000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-752787, 80000000) e11
  let e13 : LowMeanIntegerExpr := .add (1332413, 80000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (4320767, 214245000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (126224836637, 3427920000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1679, 1000)
  let e33 : LowMeanIntegerExpr := .pow (10000000000000000000000, 29900179809133802678274543) e21 11
  let e34 : LowMeanIntegerExpr := .mul (730000000000000000000, 1300007817788426203403241) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-730000000000000000000, 1300007817788426203403241) e34
  let e36 : LowMeanIntegerExpr := .add (3771170688398024694949805798533, 104000625423074096272259280000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (3772210694652255435912528391333, 104000625423074096272259280000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-3771170688398024694949805798533, 104000625423074096272259280000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0286 : LowMeanDirectSeedInput :=
  { record := 286, positions := [], target := { R := 11, expr := lowMeanSeedTargetExpr0286 } }

noncomputable def lowMeanSeedTargetExpr0287 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (15941, 500000)
  let e2 : LowMeanIntegerExpr := .atom (277, 250000)
  let e3 : LowMeanIntegerExpr := .atom (12, 1)
  let e4 : LowMeanIntegerExpr := .atom (65, 4)
  let e5 : LowMeanIntegerExpr := .neg (-65, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-17, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-4709, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (27173, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1707, 5000000)
  let e10 : LowMeanIntegerExpr := .pow (289, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (493323, 80000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-493323, 80000000) e11
  let e13 : LowMeanIntegerExpr := .add (1680517, 80000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (392797, 17853750) e29 e3
  let e31 : LowMeanIntegerExpr := .add (49141832311, 1142640000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1679, 1000)
  let e33 : LowMeanIntegerExpr := .pow (1000000000000000000000000, 6189337220490697154402830401) e21 12
  let e34 : LowMeanIntegerExpr := .mul (73000000000000000000000, 269101618282204224104470887) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-73000000000000000000000, 269101618282204224104470887) e34
  let e36 : LowMeanIntegerExpr := .add (920026176590549034264354300520579, 21528129462576337928357670960000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (920241457885174797643637877230179, 21528129462576337928357670960000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-920026176590549034264354300520579, 21528129462576337928357670960000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0287 : LowMeanDirectSeedInput :=
  { record := 287, positions := [], target := { R := 12, expr := lowMeanSeedTargetExpr0287 } }

noncomputable def lowMeanSeedGroup0272 : List LowMeanDirectSeedInput := [lowMeanSeedRecord0272, lowMeanSeedRecord0273, lowMeanSeedRecord0274, lowMeanSeedRecord0275, lowMeanSeedRecord0276, lowMeanSeedRecord0277, lowMeanSeedRecord0278, lowMeanSeedRecord0279, lowMeanSeedRecord0280, lowMeanSeedRecord0281, lowMeanSeedRecord0282, lowMeanSeedRecord0283, lowMeanSeedRecord0284, lowMeanSeedRecord0285, lowMeanSeedRecord0286, lowMeanSeedRecord0287]

end Erdos993Lean.Analytic.V213
