module

public import Erdos993Lean.Analytic.V213.LowMeanCoreAll
public import Erdos993Lean.Analytic.V213.LowMeanData.Seed0048
public import Erdos993Lean.Analytic.V213.LowMeanFiberSeed
public import Erdos993Lean.Analytic.V213.LowMeanIntegerExpr
public import Erdos993Lean.Analytic.V213.LowMeanSeedGeometry
public import Erdos993Lean.Analytic.V213.LowMeanWidthData
public import Erdos993Lean.Ceiling.Prefix
public import Erdos993Lean.Ceiling.Statement

/-! Exact core/budget keys and equation-51 targets for the direct fibers. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanSeedTargetExpr0112 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (56593, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (363, 200000)
  let e3 : LowMeanIntegerExpr := .atom (17, 1)
  let e4 : LowMeanIntegerExpr := .atom (33, 2)
  let e5 : LowMeanIntegerExpr := .neg (-33, 2) e4
  let e6 : LowMeanIntegerExpr := .add (1, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (363, 400000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (115001, 2000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (4727, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (1, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (4727, 40000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-4727, 40000000) e11
  let e13 : LowMeanIntegerExpr := .add (2295293, 40000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (113, 10000)
  let e15 : LowMeanIntegerExpr := .atom (39, 89)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (87, 187)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-39, 89) e15
  let e21 : LowMeanIntegerExpr := .add (50, 89) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (1950, 7921) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-87, 187) e17
  let e24 : LowMeanIntegerExpr := .add (100, 187) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (8700, 34969) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (8700, 34969) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (8700, 34969) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (8700, 34969) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (9831, 3496900) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (9831, 205700) e29 e3
  let e31 : LowMeanIntegerExpr := .add (8653817701, 82280000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1619, 1000)
  let e33 : LowMeanIntegerExpr := .pow (76293945312500000000000000000, 1379209096840925342723840168019929) e21 17
  let e34 : LowMeanIntegerExpr := .mul (123519897460937500000000000000, 1379209096840925342723840168019929) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-123519897460937500000000000000, 1379209096840925342723840168019929) e34
  let e36 : LowMeanIntegerExpr := .add (11925260878459136974583059600705675700963229, 113481324488071337199317569024679758120000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (11926395691704017687955052776395922498544429, 113481324488071337199317569024679758120000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-11925260878459136974583059600705675700963229, 113481324488071337199317569024679758120000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0112 : LowMeanDirectSeedInput :=
  { record := 112, positions := [{ j := 5, mode := 0, left := 389, right := 0 }, { j := 6, mode := 0, left := 390, right := 0 }, { j := 9, mode := 0, left := 391, right := 0 }], target := { R := 17, expr := lowMeanSeedTargetExpr0112 } }

noncomputable def lowMeanSeedTargetExpr0113 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (56593, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (363, 200000)
  let e3 : LowMeanIntegerExpr := .atom (18, 1)
  let e4 : LowMeanIntegerExpr := .atom (33, 2)
  let e5 : LowMeanIntegerExpr := .neg (-33, 2) e4
  let e6 : LowMeanIntegerExpr := .add (3, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (1089, 400000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (118631, 2000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (4727, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (9, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (42543, 40000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-42543, 40000000) e11
  let e13 : LowMeanIntegerExpr := .add (2330077, 40000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (113, 10000)
  let e15 : LowMeanIntegerExpr := .atom (39, 89)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (87, 187)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-39, 89) e15
  let e21 : LowMeanIntegerExpr := .add (50, 89) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (1950, 7921) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-87, 187) e17
  let e24 : LowMeanIntegerExpr := .add (100, 187) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (8700, 34969) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (8700, 34969) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (8700, 34969) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (8700, 34969) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (9831, 3496900) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (88479, 1748450) e29 e3
  let e31 : LowMeanIntegerExpr := .add (152263662613, 1398760000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1619, 1000)
  let e33 : LowMeanIntegerExpr := .pow (3814697265625000000000000000000, 122749609618842355502421774953773681) e21 18
  let e34 : LowMeanIntegerExpr := .mul (6175994873046875000000000000000, 122749609618842355502421774953773681) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-6175994873046875000000000000000, 122749609618842355502421774953773681) e34
  let e36 : LowMeanIntegerExpr := .add (18681666410292248898979953245986009434943088453, 171697243950451933182567481934340474035560000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (18683383382731753418311778920805352839683444053, 171697243950451933182567481934340474035560000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-18681666410292248898979953245986009434943088453, 171697243950451933182567481934340474035560000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0113 : LowMeanDirectSeedInput :=
  { record := 113, positions := [{ j := 5, mode := 0, left := 392, right := 0 }, { j := 6, mode := 0, left := 393, right := 0 }, { j := 9, mode := 0, left := 394, right := 0 }, { j := 10, mode := 0, left := 395, right := 0 }], target := { R := 18, expr := lowMeanSeedTargetExpr0113 } }

noncomputable def lowMeanSeedTargetExpr0114 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (56593, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (363, 200000)
  let e3 : LowMeanIntegerExpr := .atom (19, 1)
  let e4 : LowMeanIntegerExpr := .atom (33, 2)
  let e5 : LowMeanIntegerExpr := .neg (-33, 2) e4
  let e6 : LowMeanIntegerExpr := .add (5, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (363, 80000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (122261, 2000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (4727, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (25, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (4727, 1600000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-4727, 1600000) e11
  let e13 : LowMeanIntegerExpr := .add (465409, 8000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (113, 10000)
  let e15 : LowMeanIntegerExpr := .atom (39, 89)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (87, 187)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-39, 89) e15
  let e21 : LowMeanIntegerExpr := .add (50, 89) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (1950, 7921) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-87, 187) e17
  let e24 : LowMeanIntegerExpr := .add (100, 187) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (8700, 34969) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (8700, 34969) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (8700, 34969) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (8700, 34969) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (9831, 3496900) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (186789, 3496900) e29 e3
  let e31 : LowMeanIntegerExpr := .add (31218007321, 279752000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1619, 1000)
  let e33 : LowMeanIntegerExpr := .pow (190734863281250000000000000000000, 10924715256076969639715537970885857609) e21 19
  let e34 : LowMeanIntegerExpr := .mul (308799743652343750000000000000000, 10924715256076969639715537970885857609) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-308799743652343750000000000000000, 10924715256076969639715537970885857609) e34
  let e36 : LowMeanIntegerExpr := .add (340961453498164997483384396732568187693125555489, 3056210942318044410649701178431260437832968000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (340992015607588177927490893744352500297503885169, 3056210942318044410649701178431260437832968000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-340961453498164997483384396732568187693125555489, 3056210942318044410649701178431260437832968000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0114 : LowMeanDirectSeedInput :=
  { record := 114, positions := [{ j := 6, mode := 0, left := 396, right := 0 }, { j := 7, mode := 0, left := 397, right := 0 }, { j := 10, mode := 0, left := 398, right := 0 }], target := { R := 19, expr := lowMeanSeedTargetExpr0114 } }

noncomputable def lowMeanSeedTargetExpr0115 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (56593, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (363, 200000)
  let e3 : LowMeanIntegerExpr := .atom (20, 1)
  let e4 : LowMeanIntegerExpr := .atom (33, 2)
  let e5 : LowMeanIntegerExpr := .neg (-33, 2) e4
  let e6 : LowMeanIntegerExpr := .add (7, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (2541, 400000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (125891, 2000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (4727, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (49, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (231623, 40000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-231623, 40000000) e11
  let e13 : LowMeanIntegerExpr := .add (2286197, 40000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (113, 10000)
  let e15 : LowMeanIntegerExpr := .atom (39, 89)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (87, 187)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-39, 89) e15
  let e21 : LowMeanIntegerExpr := .add (50, 89) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (1950, 7921) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-87, 187) e17
  let e24 : LowMeanIntegerExpr := .add (100, 187) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (8700, 34969) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (8700, 34969) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (8700, 34969) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (8700, 34969) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (9831, 3496900) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (9831, 174845) e29 e3
  let e31 : LowMeanIntegerExpr := .add (158594022893, 1398760000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1619, 1000)
  let e33 : LowMeanIntegerExpr := .pow (9536743164062500000000000000000000, 972299657790850297934682879408841327201) e21 20
  let e34 : LowMeanIntegerExpr := .mul (15439987182617187500000000000000000, 972299657790850297934682879408841327201) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-15439987182617187500000000000000000, 972299657790850297934682879408841327201) e34
  let e36 : LowMeanIntegerExpr := .add (154179317350066620339401467195660939752719897612493, 1360013869331529762739117024401910894835670760000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (154192917488759935637028858365904958861668254320093, 1360013869331529762739117024401910894835670760000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-154179317350066620339401467195660939752719897612493, 1360013869331529762739117024401910894835670760000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0115 : LowMeanDirectSeedInput :=
  { record := 115, positions := [{ j := 6, mode := 0, left := 399, right := 0 }, { j := 7, mode := 0, left := 400, right := 0 }, { j := 10, mode := 0, left := 401, right := 0 }], target := { R := 20, expr := lowMeanSeedTargetExpr0115 } }

noncomputable def lowMeanSeedTargetExpr0116 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (56593, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (363, 200000)
  let e3 : LowMeanIntegerExpr := .atom (21, 1)
  let e4 : LowMeanIntegerExpr := .atom (33, 2)
  let e5 : LowMeanIntegerExpr := .neg (-33, 2) e4
  let e6 : LowMeanIntegerExpr := .add (9, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (3267, 400000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (129521, 2000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (4727, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (81, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (382887, 40000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-382887, 40000000) e11
  let e13 : LowMeanIntegerExpr := .add (2207533, 40000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (113, 10000)
  let e15 : LowMeanIntegerExpr := .atom (39, 89)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (87, 187)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-39, 89) e15
  let e21 : LowMeanIntegerExpr := .add (50, 89) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (1950, 7921) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-87, 187) e17
  let e24 : LowMeanIntegerExpr := .add (100, 187) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (8700, 34969) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (8700, 34969) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (8700, 34969) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (8700, 34969) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (9831, 3496900) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (206451, 3496900) e29 e3
  let e31 : LowMeanIntegerExpr := .add (159775621477, 1398760000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1619, 1000)
  let e33 : LowMeanIntegerExpr := .pow (476837158203125000000000000000000000, 86534669543385676516186776267386878120889) e21 21
  let e34 : LowMeanIntegerExpr := .mul (771999359130859375000000000000000000, 86534669543385676516186776267386878120889) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-771999359130859375000000000000000000, 86534669543385676516186776267386878120889) e34
  let e36 : LowMeanIntegerExpr := .add (13825050763777692399214451428330892778559893910733053, 121041234370506148883781415171770069640374697640000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (13826261176121397460703289242482610479256297657709453, 121041234370506148883781415171770069640374697640000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-13825050763777692399214451428330892778559893910733053, 121041234370506148883781415171770069640374697640000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0116 : LowMeanDirectSeedInput :=
  { record := 116, positions := [{ j := 7, mode := 0, left := 402, right := 0 }, { j := 8, mode := 0, left := 403, right := 0 }, { j := 10, mode := 0, left := 404, right := 0 }], target := { R := 21, expr := lowMeanSeedTargetExpr0116 } }

noncomputable def lowMeanSeedTargetExpr0117 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (88879, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (-1417, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (0, 1)
  let e4 : LowMeanIntegerExpr := .atom (10, 1)
  let e5 : LowMeanIntegerExpr := .neg (-10, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-10, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (1417, 100000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (103049, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (303, 250000)
  let e10 : LowMeanIntegerExpr := .pow (100, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (303, 2500) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-303, 2500) e11
  let e13 : LowMeanIntegerExpr := .add (-18151, 1000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (783, 25000)
  let e15 : LowMeanIntegerExpr := .atom (87, 187)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (23, 48)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-87, 187) e15
  let e21 : LowMeanIntegerExpr := .add (100, 187) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (8700, 34969) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-23, 48) e17
  let e24 : LowMeanIntegerExpr := .add (25, 48) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (575, 2304) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (575, 2304) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (575, 2304) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (575, 2304) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2001, 256000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (0, 1) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-18151, 1000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (621, 500)
  let e33 : LowMeanIntegerExpr := .pow (1, 1) e21 0
  let e34 : LowMeanIntegerExpr := .mul (621, 500) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-621, 500) e34
  let e36 : LowMeanIntegerExpr := .add (-1260151, 1000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-1260141, 1000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (1260151, 1000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0117 : LowMeanDirectSeedInput :=
  { record := 117, positions := [], target := { R := 0, expr := lowMeanSeedTargetExpr0117 } }

noncomputable def lowMeanSeedTargetExpr0118 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (88879, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (-1417, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (1, 1)
  let e4 : LowMeanIntegerExpr := .atom (10, 1)
  let e5 : LowMeanIntegerExpr := .neg (-10, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-9, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (12753, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (1588, 15625) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (303, 250000)
  let e10 : LowMeanIntegerExpr := .pow (81, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (24543, 250000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-24543, 250000) e11
  let e13 : LowMeanIntegerExpr := .add (173, 50000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (783, 25000)
  let e15 : LowMeanIntegerExpr := .atom (87, 187)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (23, 48)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .neg (-87, 187) e15
  let e20 : LowMeanIntegerExpr := .add (100, 187) e3 e19
  let e21 : LowMeanIntegerExpr := .mul (8700, 34969) e15 e20
  let e22 : LowMeanIntegerExpr := .neg (-23, 48) e17
  let e23 : LowMeanIntegerExpr := .add (25, 48) e3 e22
  let e24 : LowMeanIntegerExpr := .mul (575, 2304) e17 e23
  let e25 : LowMeanIntegerExpr := .maximum (575, 2304) e21 e24
  let e26 : LowMeanIntegerExpr := .selectLE (575, 2304) e16 e17 e18 e25
  let e27 : LowMeanIntegerExpr := .selectLE (575, 2304) e15 e16 e26 e25
  let e28 : LowMeanIntegerExpr := .mul (2001, 256000) e14 e27
  let e29 : LowMeanIntegerExpr := .mul (2001, 256000) e28 e3
  let e30 : LowMeanIntegerExpr := .add (72169, 6400000) e13 e29
  let e31 : LowMeanIntegerExpr := .atom (621, 500)
  let e32 : LowMeanIntegerExpr := .pow (100, 187) e20 1
  let e33 : LowMeanIntegerExpr := .mul (621, 935) e31 e32
  let e34 : LowMeanIntegerExpr := .neg (-621, 935) e33
  let e35 : LowMeanIntegerExpr := .add (-781384397, 1196800000) e30 e34
  let e36 : LowMeanIntegerExpr := .add (-781372429, 1196800000) e0 e35
  let e37 : LowMeanIntegerExpr := .neg (781384397, 1196800000) e35
  let e38 : LowMeanIntegerExpr := .add (1, 100000) e36 e37
  e38

noncomputable def lowMeanSeedRecord0118 : LowMeanDirectSeedInput :=
  { record := 118, positions := [], target := { R := 1, expr := lowMeanSeedTargetExpr0118 } }

noncomputable def lowMeanSeedTargetExpr0119 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (88879, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (-1417, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (2, 1)
  let e4 : LowMeanIntegerExpr := .atom (10, 1)
  let e5 : LowMeanIntegerExpr := .neg (-10, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-8, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (1417, 125000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (20043, 200000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (303, 250000)
  let e10 : LowMeanIntegerExpr := .pow (64, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1212, 15625) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1212, 15625) e11
  let e13 : LowMeanIntegerExpr := .add (22647, 1000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (783, 25000)
  let e15 : LowMeanIntegerExpr := .atom (87, 187)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (23, 48)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-87, 187) e15
  let e21 : LowMeanIntegerExpr := .add (100, 187) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (8700, 34969) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-23, 48) e17
  let e24 : LowMeanIntegerExpr := .add (25, 48) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (575, 2304) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (575, 2304) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (575, 2304) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (575, 2304) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2001, 256000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (2001, 128000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (612477, 16000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (621, 500)
  let e33 : LowMeanIntegerExpr := .pow (10000, 34969) e21 2
  let e34 : LowMeanIntegerExpr := .mul (12420, 34969) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-12420, 34969) e34
  let e36 : LowMeanIntegerExpr := .add (-177302291787, 559504000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-177296696747, 559504000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (177302291787, 559504000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0119 : LowMeanDirectSeedInput :=
  { record := 119, positions := [], target := { R := 2, expr := lowMeanSeedTargetExpr0119 } }

noncomputable def lowMeanSeedTargetExpr0120 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (88879, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (-1417, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (3, 1)
  let e4 : LowMeanIntegerExpr := .atom (10, 1)
  let e5 : LowMeanIntegerExpr := .neg (-10, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-7, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (9919, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (49399, 500000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (303, 250000)
  let e10 : LowMeanIntegerExpr := .pow (49, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (14847, 250000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-14847, 250000) e11
  let e13 : LowMeanIntegerExpr := .add (3941, 100000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (783, 25000)
  let e15 : LowMeanIntegerExpr := .atom (87, 187)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (23, 48)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-87, 187) e15
  let e21 : LowMeanIntegerExpr := .add (100, 187) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (8700, 34969) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-23, 48) e17
  let e24 : LowMeanIntegerExpr := .add (25, 48) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (575, 2304) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (575, 2304) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (575, 2304) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (575, 2304) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2001, 256000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (6003, 256000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (402299, 6400000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (621, 500)
  let e33 : LowMeanIntegerExpr := .pow (1000000, 6539203) e21 3
  let e34 : LowMeanIntegerExpr := .mul (1242000, 6539203) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1242000, 6539203) e34
  let e36 : LowMeanIntegerExpr := .add (-5318085172303, 41850899200000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-5317666663311, 41850899200000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (5318085172303, 41850899200000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0120 : LowMeanDirectSeedInput :=
  { record := 120, positions := [], target := { R := 3, expr := lowMeanSeedTargetExpr0120 } }

noncomputable def lowMeanSeedTargetExpr0121 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (88879, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (-1417, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (4, 1)
  let e4 : LowMeanIntegerExpr := .atom (10, 1)
  let e5 : LowMeanIntegerExpr := .neg (-10, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-6, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (4251, 500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (97381, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (303, 250000)
  let e10 : LowMeanIntegerExpr := .pow (36, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (2727, 62500) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-2727, 62500) e11
  let e13 : LowMeanIntegerExpr := .add (53749, 1000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (783, 25000)
  let e15 : LowMeanIntegerExpr := .atom (87, 187)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (23, 48)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-87, 187) e15
  let e21 : LowMeanIntegerExpr := .add (100, 187) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (8700, 34969) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-23, 48) e17
  let e24 : LowMeanIntegerExpr := .add (25, 48) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (575, 2304) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (575, 2304) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (575, 2304) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (575, 2304) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2001, 256000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (2001, 64000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (680117, 8000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (621, 500)
  let e33 : LowMeanIntegerExpr := .pow (100000000, 1222830961) e21 4
  let e34 : LowMeanIntegerExpr := .mul (124200000, 1222830961) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-124200000, 1222830961) e34
  let e36 : LowMeanIntegerExpr := .add (-161931875297563, 9782647688000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-161834048820683, 9782647688000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (161931875297563, 9782647688000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0121 : LowMeanDirectSeedInput :=
  { record := 121, positions := [{ j := 0, mode := 0, left := 405, right := 0 }], target := { R := 4, expr := lowMeanSeedTargetExpr0121 } }

noncomputable def lowMeanSeedTargetExpr0122 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (88879, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (-1417, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (5, 1)
  let e4 : LowMeanIntegerExpr := .atom (10, 1)
  let e5 : LowMeanIntegerExpr := .neg (-10, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-5, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (1417, 200000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (23991, 250000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (303, 250000)
  let e10 : LowMeanIntegerExpr := .pow (25, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (303, 10000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-303, 10000) e11
  let e13 : LowMeanIntegerExpr := .add (1026, 15625) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (783, 25000)
  let e15 : LowMeanIntegerExpr := .atom (87, 187)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (23, 48)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-87, 187) e15
  let e21 : LowMeanIntegerExpr := .add (100, 187) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (8700, 34969) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-23, 48) e17
  let e24 : LowMeanIntegerExpr := .add (25, 48) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (575, 2304) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (575, 2304) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (575, 2304) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (575, 2304) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2001, 256000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (2001, 51200) e29 e3
  let e31 : LowMeanIntegerExpr := .add (3351873, 32000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (621, 500)
  let e33 : LowMeanIntegerExpr := .pow (10000000000, 228669389707) e21 5
  let e34 : LowMeanIntegerExpr := .mul (12420000000, 228669389707) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-12420000000, 228669389707) e34
  let e36 : LowMeanIntegerExpr := .add (369030753285371211, 7317420470624000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (369103927490077451, 7317420470624000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-369030753285371211, 7317420470624000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0122 : LowMeanDirectSeedInput :=
  { record := 122, positions := [{ j := 4, mode := 0, left := 406, right := 0 }], target := { R := 5, expr := lowMeanSeedTargetExpr0122 } }

noncomputable def lowMeanSeedTargetExpr0123 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (88879, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (-1417, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (6, 1)
  let e4 : LowMeanIntegerExpr := .atom (10, 1)
  let e5 : LowMeanIntegerExpr := .neg (-10, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-4, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (1417, 250000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (94547, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (303, 250000)
  let e10 : LowMeanIntegerExpr := .pow (16, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (303, 15625) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-303, 15625) e11
  let e13 : LowMeanIntegerExpr := .add (15031, 200000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (783, 25000)
  let e15 : LowMeanIntegerExpr := .atom (87, 187)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (23, 48)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-87, 187) e15
  let e21 : LowMeanIntegerExpr := .add (100, 187) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (8700, 34969) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-23, 48) e17
  let e24 : LowMeanIntegerExpr := .add (25, 48) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (575, 2304) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (575, 2304) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (575, 2304) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (575, 2304) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2001, 256000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (6003, 128000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (390571, 3200000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (621, 500)
  let e33 : LowMeanIntegerExpr := .pow (1000000000000, 42761175875209) e21 6
  let e34 : LowMeanIntegerExpr := .mul (1242000000000, 42761175875209) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1242000000000, 42761175875209) e34
  let e36 : LowMeanIntegerExpr := .add (12726875222756254339, 136835762800668800000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (12728243580384261027, 136835762800668800000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-12726875222756254339, 136835762800668800000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0123 : LowMeanDirectSeedInput :=
  { record := 123, positions := [{ j := 1, mode := 0, left := 407, right := 0 }], target := { R := 6, expr := lowMeanSeedTargetExpr0123 } }

noncomputable def lowMeanSeedTargetExpr0124 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (88879, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (-1417, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (7, 1)
  let e4 : LowMeanIntegerExpr := .atom (10, 1)
  let e5 : LowMeanIntegerExpr := .neg (-10, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-3, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (4251, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (9313, 100000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (303, 250000)
  let e10 : LowMeanIntegerExpr := .pow (9, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (2727, 250000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-2727, 250000) e11
  let e13 : LowMeanIntegerExpr := .add (41111, 500000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (783, 25000)
  let e15 : LowMeanIntegerExpr := .atom (87, 187)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (23, 48)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-87, 187) e15
  let e21 : LowMeanIntegerExpr := .add (100, 187) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (8700, 34969) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-23, 48) e17
  let e24 : LowMeanIntegerExpr := .add (25, 48) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (575, 2304) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (575, 2304) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (575, 2304) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (575, 2304) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2001, 256000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (14007, 256000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (4381979, 32000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (621, 500)
  let e33 : LowMeanIntegerExpr := .pow (100000000000000, 7996339888664083) e21 7
  let e34 : LowMeanIntegerExpr := .mul (124200000000000, 7996339888664083) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-124200000000000, 7996339888664083) e34
  let e36 : LowMeanIntegerExpr := .add (31065393468988349760257, 255882876437250656000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (31067952297752722266817, 255882876437250656000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-31065393468988349760257, 255882876437250656000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0124 : LowMeanDirectSeedInput :=
  { record := 124, positions := [{ j := 1, mode := 0, left := 408, right := 0 }, { j := 5, mode := 0, left := 409, right := 0 }], target := { R := 7, expr := lowMeanSeedTargetExpr0124 } }

noncomputable def lowMeanSeedTargetExpr0125 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (88879, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (-1417, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (8, 1)
  let e4 : LowMeanIntegerExpr := .atom (10, 1)
  let e5 : LowMeanIntegerExpr := .neg (-10, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-2, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (1417, 500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (91713, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (303, 250000)
  let e10 : LowMeanIntegerExpr := .pow (4, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (303, 62500) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-303, 62500) e11
  let e13 : LowMeanIntegerExpr := .add (17373, 200000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (783, 25000)
  let e15 : LowMeanIntegerExpr := .atom (87, 187)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (23, 48)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-87, 187) e15
  let e21 : LowMeanIntegerExpr := .add (100, 187) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (8700, 34969) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-23, 48) e17
  let e24 : LowMeanIntegerExpr := .add (25, 48) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (575, 2304) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (575, 2304) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (575, 2304) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (575, 2304) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2001, 256000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (2001, 32000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (119517, 800000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (621, 500)
  let e33 : LowMeanIntegerExpr := .pow (10000000000000000, 1495315559180183521) e21 8
  let e34 : LowMeanIntegerExpr := .mul (12420000000000000, 1495315559180183521) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-12420000000000000, 1495315559180183521) e34
  let e36 : LowMeanIntegerExpr := .add (168779629686537993879357, 1196252447344146816800000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (6751663688440457413901, 47850097893765872672000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-168779629686537993879357, 1196252447344146816800000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0125 : LowMeanDirectSeedInput :=
  { record := 125, positions := [{ j := 2, mode := 0, left := 410, right := 0 }, { j := 5, mode := 0, left := 411, right := 0 }], target := { R := 8, expr := lowMeanSeedTargetExpr0125 } }

noncomputable def lowMeanSeedTargetExpr0126 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (88879, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (-1417, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (9, 1)
  let e4 : LowMeanIntegerExpr := .atom (10, 1)
  let e5 : LowMeanIntegerExpr := .neg (-10, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-1, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (1417, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (11287, 125000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (303, 250000)
  let e10 : LowMeanIntegerExpr := .pow (1, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (303, 250000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-303, 250000) e11
  let e13 : LowMeanIntegerExpr := .add (22271, 250000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (783, 25000)
  let e15 : LowMeanIntegerExpr := .atom (87, 187)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (23, 48)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-87, 187) e15
  let e21 : LowMeanIntegerExpr := .add (100, 187) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (8700, 34969) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-23, 48) e17
  let e24 : LowMeanIntegerExpr := .add (25, 48) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (575, 2304) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (575, 2304) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (575, 2304) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (575, 2304) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (2001, 256000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (18009, 256000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (5101813, 32000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (621, 500)
  let e33 : LowMeanIntegerExpr := .pow (1000000000000000000, 279624009566694318427) e21 9
  let e34 : LowMeanIntegerExpr := .mul (1242000000000000000, 279624009566694318427) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1242000000000000000, 279624009566694318427) e34
  let e36 : LowMeanIntegerExpr := .add (1386845407119485440777008151, 8947968306134218189664000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (1386934886802546782958904791, 8947968306134218189664000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-1386845407119485440777008151, 8947968306134218189664000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0126 : LowMeanDirectSeedInput :=
  { record := 126, positions := [{ j := 3, mode := 0, left := 412, right := 0 }], target := { R := 9, expr := lowMeanSeedTargetExpr0126 } }

noncomputable def lowMeanSeedTargetExpr0127 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (88879, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (-1417, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (10, 1)
  let e4 : LowMeanIntegerExpr := .neg (-10, 1) e3
  let e5 : LowMeanIntegerExpr := .add (0, 1) e3 e4
  let e6 : LowMeanIntegerExpr := .mul (0, 1) e2 e5
  let e7 : LowMeanIntegerExpr := .add (88879, 1000000) e1 e6
  let e8 : LowMeanIntegerExpr := .atom (303, 250000)
  let e9 : LowMeanIntegerExpr := .pow (0, 1) e5 2
  let e10 : LowMeanIntegerExpr := .mul (0, 1) e8 e9
  let e11 : LowMeanIntegerExpr := .neg (0, 1) e10
  let e12 : LowMeanIntegerExpr := .add (88879, 1000000) e7 e11
  let e13 : LowMeanIntegerExpr := .atom (783, 25000)
  let e14 : LowMeanIntegerExpr := .atom (87, 187)
  let e15 : LowMeanIntegerExpr := .atom (1, 2)
  let e16 : LowMeanIntegerExpr := .atom (23, 48)
  let e17 : LowMeanIntegerExpr := .atom (1, 4)
  let e18 : LowMeanIntegerExpr := .atom (1, 1)
  let e19 : LowMeanIntegerExpr := .neg (-87, 187) e14
  let e20 : LowMeanIntegerExpr := .add (100, 187) e18 e19
  let e21 : LowMeanIntegerExpr := .mul (8700, 34969) e14 e20
  let e22 : LowMeanIntegerExpr := .neg (-23, 48) e16
  let e23 : LowMeanIntegerExpr := .add (25, 48) e18 e22
  let e24 : LowMeanIntegerExpr := .mul (575, 2304) e16 e23
  let e25 : LowMeanIntegerExpr := .maximum (575, 2304) e21 e24
  let e26 : LowMeanIntegerExpr := .selectLE (575, 2304) e15 e16 e17 e25
  let e27 : LowMeanIntegerExpr := .selectLE (575, 2304) e14 e15 e26 e25
  let e28 : LowMeanIntegerExpr := .mul (2001, 256000) e13 e27
  let e29 : LowMeanIntegerExpr := .mul (2001, 25600) e28 e3
  let e30 : LowMeanIntegerExpr := .add (2672689, 16000000) e12 e29
  let e31 : LowMeanIntegerExpr := .atom (621, 500)
  let e32 : LowMeanIntegerExpr := .pow (100000000000000000000, 52289689788971837545849) e20 10
  let e33 : LowMeanIntegerExpr := .mul (124200000000000000000, 52289689788971837545849) e31 e32
  let e34 : LowMeanIntegerExpr := .neg (-124200000000000000000, 52289689788971837545849) e33
  let e35 : LowMeanIntegerExpr := .add (137766878712397351518577617961, 836635036623549400733584000000) e30 e34
  let e36 : LowMeanIntegerExpr := .add (137775245062763587012584953801, 836635036623549400733584000000) e0 e35
  let e37 : LowMeanIntegerExpr := .neg (-137766878712397351518577617961, 836635036623549400733584000000) e35
  let e38 : LowMeanIntegerExpr := .add (1, 100000) e36 e37
  e38

noncomputable def lowMeanSeedRecord0127 : LowMeanDirectSeedInput :=
  { record := 127, positions := [{ j := 3, mode := 0, left := 413, right := 0 }, { j := 6, mode := 0, left := 414, right := 0 }], target := { R := 10, expr := lowMeanSeedTargetExpr0127 } }

noncomputable def lowMeanSeedGroup0112 : List LowMeanDirectSeedInput := [lowMeanSeedRecord0112, lowMeanSeedRecord0113, lowMeanSeedRecord0114, lowMeanSeedRecord0115, lowMeanSeedRecord0116, lowMeanSeedRecord0117, lowMeanSeedRecord0118, lowMeanSeedRecord0119, lowMeanSeedRecord0120, lowMeanSeedRecord0121, lowMeanSeedRecord0122, lowMeanSeedRecord0123, lowMeanSeedRecord0124, lowMeanSeedRecord0125, lowMeanSeedRecord0126, lowMeanSeedRecord0127]

end Erdos993Lean.Analytic.V213
