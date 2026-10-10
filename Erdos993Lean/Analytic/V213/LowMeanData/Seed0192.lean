module

public import Erdos993Lean.Analytic.V213.LowMeanCoreAll
public import Erdos993Lean.Analytic.V213.LowMeanData.Seed0112
public import Erdos993Lean.Analytic.V213.LowMeanFiberSeed
public import Erdos993Lean.Analytic.V213.LowMeanIntegerExpr
public import Erdos993Lean.Analytic.V213.LowMeanSeedGeometry
public import Erdos993Lean.Analytic.V213.LowMeanWidthData
public import Erdos993Lean.Ceiling.Prefix
public import Erdos993Lean.Ceiling.Statement

/-! Exact core/budget keys and equation-51 targets for the direct fibers. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanSeedTargetExpr0192 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (6447, 200000)
  let e2 : LowMeanIntegerExpr := .atom (253, 250000)
  let e3 : LowMeanIntegerExpr := .atom (13, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-3, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-759, 250000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (29199, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1749, 5000000)
  let e10 : LowMeanIntegerExpr := .pow (9, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (15741, 5000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-15741, 5000000) e11
  let e13 : LowMeanIntegerExpr := .add (65127, 2500000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (119, 15625)
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
  let e29 : LowMeanIntegerExpr := .mul (119, 62500) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (1547, 62500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (127007, 2500000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (187, 125)
  let e33 : LowMeanIntegerExpr := .pow (1490116119384765625, 7180192468708211294208) e21 13
  let e34 : LowMeanIntegerExpr := .mul (2229213714599609375, 7180192468708211294208) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-2229213714599609375, 7180192468708211294208) e34
  let e36 : LowMeanIntegerExpr := .add (28323802205835149012686733, 560952536617829007360000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (28329411731201327302760333, 560952536617829007360000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-28323802205835149012686733, 560952536617829007360000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0192 : LowMeanDirectSeedInput :=
  { record := 192, positions := [{ j := 4, mode := 0, left := 527, right := 0 }, { j := 5, mode := 0, left := 528, right := 0 }, { j := 8, mode := 0, left := 529, right := 0 }, { j := 9, mode := 0, left := 530, right := 0 }], target := { R := 13, expr := lowMeanSeedTargetExpr0192 } }

noncomputable def lowMeanSeedTargetExpr0193 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (6447, 200000)
  let e2 : LowMeanIntegerExpr := .atom (253, 250000)
  let e3 : LowMeanIntegerExpr := .atom (14, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-2, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-253, 125000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (30211, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1749, 5000000)
  let e10 : LowMeanIntegerExpr := .pow (4, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1749, 1250000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1749, 1250000) e11
  let e13 : LowMeanIntegerExpr := .add (144059, 5000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (119, 15625)
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
  let e29 : LowMeanIntegerExpr := .mul (119, 62500) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (833, 31250) e29 e3
  let e31 : LowMeanIntegerExpr := .add (277339, 5000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (187, 125)
  let e33 : LowMeanIntegerExpr := .pow (37252902984619140625, 344649238497994142121984) e21 14
  let e34 : LowMeanIntegerExpr := .mul (55730342864990234375, 344649238497994142121984) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-55730342864990234375, 344649238497994142121984) e34
  let e36 : LowMeanIntegerExpr := .add (1489156616272972597032717509, 26925721757655792353280000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (1489425873490549154956250309, 26925721757655792353280000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-1489156616272972597032717509, 26925721757655792353280000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0193 : LowMeanDirectSeedInput :=
  { record := 193, positions := [{ j := 4, mode := 0, left := 531, right := 0 }, { j := 5, mode := 0, left := 532, right := 0 }, { j := 9, mode := 0, left := 533, right := 0 }], target := { R := 14, expr := lowMeanSeedTargetExpr0193 } }

noncomputable def lowMeanSeedTargetExpr0194 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (6447, 200000)
  let e2 : LowMeanIntegerExpr := .atom (253, 250000)
  let e3 : LowMeanIntegerExpr := .atom (15, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-1, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-253, 250000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (31223, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1749, 5000000)
  let e10 : LowMeanIntegerExpr := .pow (1, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1749, 5000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1749, 5000000) e11
  let e13 : LowMeanIntegerExpr := .add (77183, 2500000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (119, 15625)
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
  let e29 : LowMeanIntegerExpr := .mul (119, 62500) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (357, 12500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (148583, 2500000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (187, 125)
  let e33 : LowMeanIntegerExpr := .pow (931322574615478515625, 16543163447903718821855232) e21 15
  let e34 : LowMeanIntegerExpr := .mul (1393258571624755859375, 16543163447903718821855232) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1393258571624755859375, 16543163447903718821855232) e34
  let e36 : LowMeanIntegerExpr := .add (76704678379713011376852451133, 1292434644367478032957440000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (76717602726156686157182025533, 1292434644367478032957440000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-76704678379713011376852451133, 1292434644367478032957440000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0194 : LowMeanDirectSeedInput :=
  { record := 194, positions := [{ j := 5, mode := 0, left := 534, right := 0 }, { j := 6, mode := 0, left := 535, right := 0 }, { j := 9, mode := 0, left := 536, right := 0 }, { j := 10, mode := 0, left := 537, right := 0 }], target := { R := 15, expr := lowMeanSeedTargetExpr0194 } }

noncomputable def lowMeanSeedTargetExpr0195 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (6447, 200000)
  let e2 : LowMeanIntegerExpr := .atom (253, 250000)
  let e3 : LowMeanIntegerExpr := .atom (16, 1)
  let e4 : LowMeanIntegerExpr := .neg (-16, 1) e3
  let e5 : LowMeanIntegerExpr := .add (0, 1) e3 e4
  let e6 : LowMeanIntegerExpr := .mul (0, 1) e2 e5
  let e7 : LowMeanIntegerExpr := .add (6447, 200000) e1 e6
  let e8 : LowMeanIntegerExpr := .atom (1749, 5000000)
  let e9 : LowMeanIntegerExpr := .pow (0, 1) e5 2
  let e10 : LowMeanIntegerExpr := .mul (0, 1) e8 e9
  let e11 : LowMeanIntegerExpr := .neg (0, 1) e10
  let e12 : LowMeanIntegerExpr := .add (6447, 200000) e7 e11
  let e13 : LowMeanIntegerExpr := .atom (119, 15625)
  let e14 : LowMeanIntegerExpr := .atom (23, 48)
  let e15 : LowMeanIntegerExpr := .atom (1, 2)
  let e16 : LowMeanIntegerExpr := .atom (103, 203)
  let e17 : LowMeanIntegerExpr := .atom (1, 4)
  let e18 : LowMeanIntegerExpr := .atom (1, 1)
  let e19 : LowMeanIntegerExpr := .neg (-23, 48) e14
  let e20 : LowMeanIntegerExpr := .add (25, 48) e18 e19
  let e21 : LowMeanIntegerExpr := .mul (575, 2304) e14 e20
  let e22 : LowMeanIntegerExpr := .neg (-103, 203) e16
  let e23 : LowMeanIntegerExpr := .add (100, 203) e18 e22
  let e24 : LowMeanIntegerExpr := .mul (10300, 41209) e16 e23
  let e25 : LowMeanIntegerExpr := .maximum (10300, 41209) e21 e24
  let e26 : LowMeanIntegerExpr := .selectLE (1, 4) e15 e16 e17 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e14 e15 e26 e25
  let e28 : LowMeanIntegerExpr := .mul (119, 62500) e13 e27
  let e29 : LowMeanIntegerExpr := .mul (476, 15625) e28 e3
  let e30 : LowMeanIntegerExpr := .add (62699, 1000000) e12 e29
  let e31 : LowMeanIntegerExpr := .atom (187, 125)
  let e32 : LowMeanIntegerExpr := .pow (23283064365386962890625, 794071845499378503449051136) e20 16
  let e33 : LowMeanIntegerExpr := .mul (34831464290618896484375, 794071845499378503449051136) e31 e32
  let e34 : LowMeanIntegerExpr := .neg (-34831464290618896484375, 794071845499378503449051136) e33
  let e35 : LowMeanIntegerExpr := .add (777385612135545529551057534001, 12407372585927789116391424000000) e30 e34
  let e36 : LowMeanIntegerExpr := .add (777509685861404807442221448241, 12407372585927789116391424000000) e0 e35
  let e37 : LowMeanIntegerExpr := .neg (-777385612135545529551057534001, 12407372585927789116391424000000) e35
  let e38 : LowMeanIntegerExpr := .add (1, 100000) e36 e37
  e38

noncomputable def lowMeanSeedRecord0195 : LowMeanDirectSeedInput :=
  { record := 195, positions := [{ j := 5, mode := 0, left := 538, right := 0 }, { j := 6, mode := 0, left := 539, right := 0 }, { j := 7, mode := 0, left := 540, right := 0 }, { j := 9, mode := 0, left := 541, right := 0 }, { j := 10, mode := 0, left := 542, right := 0 }], target := { R := 16, expr := lowMeanSeedTargetExpr0195 } }

noncomputable def lowMeanSeedTargetExpr0196 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (6447, 200000)
  let e2 : LowMeanIntegerExpr := .atom (253, 250000)
  let e3 : LowMeanIntegerExpr := .atom (17, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (1, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (253, 250000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (33247, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1749, 5000000)
  let e10 : LowMeanIntegerExpr := .pow (1, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1749, 5000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1749, 5000000) e11
  let e13 : LowMeanIntegerExpr := .add (82243, 2500000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (119, 15625)
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
  let e29 : LowMeanIntegerExpr := .mul (119, 62500) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (2023, 62500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (163163, 2500000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (187, 125)
  let e33 : LowMeanIntegerExpr := .pow (582076609134674072265625, 38115448583970168165554454528) e21 17
  let e34 : LowMeanIntegerExpr := .mul (870786607265472412109375, 38115448583970168165554454528) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-870786607265472412109375, 38115448583970168165554454528) e34
  let e36 : LowMeanIntegerExpr := .add (194276686587130027105190250832877, 2977769420622669387933941760000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (194306464281336253799069590250477, 2977769420622669387933941760000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-194276686587130027105190250832877, 2977769420622669387933941760000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0196 : LowMeanDirectSeedInput :=
  { record := 196, positions := [{ j := 6, mode := 0, left := 543, right := 0 }, { j := 7, mode := 0, left := 544, right := 0 }, { j := 10, mode := 0, left := 545, right := 0 }, { j := 11, mode := 0, left := 546, right := 0 }], target := { R := 17, expr := lowMeanSeedTargetExpr0196 } }

noncomputable def lowMeanSeedTargetExpr0197 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (6447, 200000)
  let e2 : LowMeanIntegerExpr := .atom (253, 250000)
  let e3 : LowMeanIntegerExpr := .atom (18, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (2, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (253, 125000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (34259, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1749, 5000000)
  let e10 : LowMeanIntegerExpr := .pow (4, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1749, 1250000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1749, 1250000) e11
  let e13 : LowMeanIntegerExpr := .add (164299, 5000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (119, 15625)
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
  let e29 : LowMeanIntegerExpr := .mul (119, 62500) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (1071, 31250) e29 e3
  let e31 : LowMeanIntegerExpr := .add (335659, 5000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (187, 125)
  let e33 : LowMeanIntegerExpr := .pow (14551915228366851806640625, 1829541532030568071946613817344) e21 18
  let e34 : LowMeanIntegerExpr := .mul (21769665181636810302734375, 1829541532030568071946613817344) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-21769665181636810302734375, 1829541532030568071946613817344) e34
  let e36 : LowMeanIntegerExpr := .add (9593644262092816631406480866263589, 142932932189888130620829204480000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (9595073591414715512712689158308389, 142932932189888130620829204480000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-9593644262092816631406480866263589, 142932932189888130620829204480000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0197 : LowMeanDirectSeedInput :=
  { record := 197, positions := [{ j := 7, mode := 0, left := 547, right := 0 }, { j := 8, mode := 0, left := 548, right := 0 }, { j := 10, mode := 0, left := 549, right := 0 }, { j := 11, mode := 0, left := 550, right := 0 }], target := { R := 18, expr := lowMeanSeedTargetExpr0197 } }

noncomputable def lowMeanSeedTargetExpr0198 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (6447, 200000)
  let e2 : LowMeanIntegerExpr := .atom (253, 250000)
  let e3 : LowMeanIntegerExpr := .atom (20, 1)
  let e4 : LowMeanIntegerExpr := .atom (16, 1)
  let e5 : LowMeanIntegerExpr := .neg (-16, 1) e4
  let e6 : LowMeanIntegerExpr := .add (4, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (253, 62500) e2 e6
  let e8 : LowMeanIntegerExpr := .add (36283, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1749, 5000000)
  let e10 : LowMeanIntegerExpr := .pow (16, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1749, 312500) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1749, 312500) e11
  let e13 : LowMeanIntegerExpr := .add (153431, 5000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (119, 15625)
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
  let e29 : LowMeanIntegerExpr := .mul (119, 62500) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (119, 3125) e29 e3
  let e31 : LowMeanIntegerExpr := .add (343831, 5000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (187, 125)
  let e33 : LowMeanIntegerExpr := .pow (9094947017729282379150390625, 4215263689798428837764998235160576) e21 20
  let e34 : LowMeanIntegerExpr := .mul (13606040738523006439208984375, 4215263689798428837764998235160576) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-13606040738523006439208984375, 4215263689798428837764998235160576) e34
  let e36 : LowMeanIntegerExpr := .add (22644848430052983916959079113619078229, 329317475765502252950390487121920000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (22648141604810638939488583018490297429, 329317475765502252950390487121920000000) e0 e36
  let e38 : LowMeanIntegerExpr := .atom (19, 1)
  let e39 : LowMeanIntegerExpr := .add (3, 1) e38 e5
  let e40 : LowMeanIntegerExpr := .mul (759, 250000) e2 e39
  let e41 : LowMeanIntegerExpr := .add (35271, 1000000) e1 e40
  let e42 : LowMeanIntegerExpr := .pow (9, 1) e39 2
  let e43 : LowMeanIntegerExpr := .mul (15741, 5000000) e9 e42
  let e44 : LowMeanIntegerExpr := .neg (-15741, 5000000) e43
  let e45 : LowMeanIntegerExpr := .add (80307, 2500000) e41 e44
  let e46 : LowMeanIntegerExpr := .mul (2261, 62500) e29 e38
  let e47 : LowMeanIntegerExpr := .add (170747, 2500000) e45 e46
  let e48 : LowMeanIntegerExpr := .pow (363797880709171295166015625, 87817993537467267453437463232512) e21 19
  let e49 : LowMeanIntegerExpr := .mul (544241629540920257568359375, 87817993537467267453437463232512) e32 e48
  let e50 : LowMeanIntegerExpr := .neg (-544241629540920257568359375, 87817993537467267453437463232512) e49
  let e51 : LowMeanIntegerExpr := .add (468540573077127225475880176128882077, 6860780745114630269799801815040000000) e47 e50
  let e52 : LowMeanIntegerExpr := .neg (-468540573077127225475880176128882077, 6860780745114630269799801815040000000) e51
  let e53 : LowMeanIntegerExpr := .add (158194097108532116646334564303957733, 329317475765502252950390487121920000000) e37 e52
  e53

noncomputable def lowMeanSeedRecord0198 : LowMeanDirectSeedInput :=
  { record := 198, positions := [{ j := 7, mode := 0, left := 551, right := 0 }, { j := 8, mode := 0, left := 552, right := 0 }, { j := 9, mode := 0, left := 553, right := 0 }, { j := 10, mode := 0, left := 554, right := 0 }, { j := 11, mode := 0, left := 555, right := 0 }, { j := 12, mode := 0, left := 556, right := 0 }], target := { R := 20, expr := lowMeanSeedTargetExpr0198 } }

noncomputable def lowMeanSeedTargetExpr0199 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (86799, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (-1229, 500000)
  let e3 : LowMeanIntegerExpr := .atom (0, 1)
  let e4 : LowMeanIntegerExpr := .atom (17, 2)
  let e5 : LowMeanIntegerExpr := .neg (-17, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-17, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (20893, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (26923, 250000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (227, 200000)
  let e10 : LowMeanIntegerExpr := .pow (289, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (65603, 800000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-65603, 800000) e11
  let e13 : LowMeanIntegerExpr := .add (102753, 4000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (3957, 100000)
  let e15 : LowMeanIntegerExpr := .atom (103, 203)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (107, 207)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-103, 203) e15
  let e21 : LowMeanIntegerExpr := .add (100, 203) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (10300, 41209) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-107, 207) e17
  let e24 : LowMeanIntegerExpr := .add (100, 207) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (10700, 42849) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (10300, 41209) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (10300, 41209) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (407571, 41209000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (0, 1) e29 e3
  let e31 : LowMeanIntegerExpr := .add (102753, 4000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (9851, 10000)
  let e33 : LowMeanIntegerExpr := .pow (1, 1) e21 0
  let e34 : LowMeanIntegerExpr := .mul (9851, 10000) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-9851, 10000) e34
  let e36 : LowMeanIntegerExpr := .add (-3837647, 4000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-3837607, 4000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (3837647, 4000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0199 : LowMeanDirectSeedInput :=
  { record := 199, positions := [], target := { R := 0, expr := lowMeanSeedTargetExpr0199 } }

noncomputable def lowMeanSeedTargetExpr0200 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (86799, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (-1229, 500000)
  let e3 : LowMeanIntegerExpr := .atom (1, 1)
  let e4 : LowMeanIntegerExpr := .atom (17, 2)
  let e5 : LowMeanIntegerExpr := .neg (-17, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-15, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (3687, 200000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (52617, 500000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (227, 200000)
  let e10 : LowMeanIntegerExpr := .pow (225, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (2043, 32000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-2043, 32000) e11
  let e13 : LowMeanIntegerExpr := .add (165561, 4000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (3957, 100000)
  let e15 : LowMeanIntegerExpr := .atom (103, 203)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (107, 207)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .neg (-103, 203) e15
  let e20 : LowMeanIntegerExpr := .add (100, 203) e3 e19
  let e21 : LowMeanIntegerExpr := .mul (10300, 41209) e15 e20
  let e22 : LowMeanIntegerExpr := .neg (-107, 207) e17
  let e23 : LowMeanIntegerExpr := .add (100, 207) e3 e22
  let e24 : LowMeanIntegerExpr := .mul (10700, 42849) e17 e23
  let e25 : LowMeanIntegerExpr := .maximum (10300, 41209) e21 e24
  let e26 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e25
  let e27 : LowMeanIntegerExpr := .selectLE (10300, 41209) e15 e16 e26 e25
  let e28 : LowMeanIntegerExpr := .mul (407571, 41209000) e14 e27
  let e29 : LowMeanIntegerExpr := .mul (407571, 41209000) e28 e3
  let e30 : LowMeanIntegerExpr := .add (8452887249, 164836000000) e13 e29
  let e31 : LowMeanIntegerExpr := .atom (9851, 10000)
  let e32 : LowMeanIntegerExpr := .pow (100, 203) e20 1
  let e33 : LowMeanIntegerExpr := .mul (9851, 20300) e31 e32
  let e34 : LowMeanIntegerExpr := .neg (-9851, 20300) e33
  let e35 : LowMeanIntegerExpr := .add (-71537232751, 164836000000) e30 e34
  let e36 : LowMeanIntegerExpr := .add (-71535584391, 164836000000) e0 e35
  let e37 : LowMeanIntegerExpr := .neg (71537232751, 164836000000) e35
  let e38 : LowMeanIntegerExpr := .add (1, 100000) e36 e37
  e38

noncomputable def lowMeanSeedRecord0200 : LowMeanDirectSeedInput :=
  { record := 200, positions := [], target := { R := 1, expr := lowMeanSeedTargetExpr0200 } }

noncomputable def lowMeanSeedTargetExpr0201 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (86799, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (-1229, 500000)
  let e3 : LowMeanIntegerExpr := .atom (2, 1)
  let e4 : LowMeanIntegerExpr := .atom (17, 2)
  let e5 : LowMeanIntegerExpr := .neg (-17, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-13, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (15977, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (12847, 125000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (227, 200000)
  let e10 : LowMeanIntegerExpr := .pow (169, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (38363, 800000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-38363, 800000) e11
  let e13 : LowMeanIntegerExpr := .add (219289, 4000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (3957, 100000)
  let e15 : LowMeanIntegerExpr := .atom (103, 203)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (107, 207)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-103, 203) e15
  let e21 : LowMeanIntegerExpr := .add (100, 203) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (10300, 41209) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-107, 207) e17
  let e24 : LowMeanIntegerExpr := .add (100, 207) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (10700, 42849) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (10300, 41209) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (10300, 41209) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (407571, 41209000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (407571, 20604500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (12297248401, 164836000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (9851, 10000)
  let e33 : LowMeanIntegerExpr := .pow (10000, 41209) e21 2
  let e34 : LowMeanIntegerExpr := .mul (9851, 41209) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-9851, 41209) e34
  let e36 : LowMeanIntegerExpr := .add (-27106751599, 164836000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-27105103239, 164836000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (27106751599, 164836000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0201 : LowMeanDirectSeedInput :=
  { record := 201, positions := [], target := { R := 2, expr := lowMeanSeedTargetExpr0201 } }

noncomputable def lowMeanSeedTargetExpr0202 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (86799, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (-1229, 500000)
  let e3 : LowMeanIntegerExpr := .atom (3, 1)
  let e4 : LowMeanIntegerExpr := .atom (17, 2)
  let e5 : LowMeanIntegerExpr := .neg (-17, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-11, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (13519, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (50159, 500000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (227, 200000)
  let e10 : LowMeanIntegerExpr := .pow (121, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (27467, 800000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-27467, 800000) e11
  let e13 : LowMeanIntegerExpr := .add (263937, 4000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (3957, 100000)
  let e15 : LowMeanIntegerExpr := .atom (103, 203)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (107, 207)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-103, 203) e15
  let e21 : LowMeanIntegerExpr := .add (100, 203) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (10300, 41209) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-107, 207) e17
  let e24 : LowMeanIntegerExpr := .add (100, 207) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (10700, 42849) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (10300, 41209) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (10300, 41209) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (407571, 41209000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (1222713, 41209000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (15767431833, 164836000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (9851, 10000)
  let e33 : LowMeanIntegerExpr := .pow (1000000, 8365427) e21 3
  let e34 : LowMeanIntegerExpr := .mul (985100, 8365427) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-985100, 8365427) e34
  let e36 : LowMeanIntegerExpr := .add (-739611337901, 33461708000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-739276720821, 33461708000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (739611337901, 33461708000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0202 : LowMeanDirectSeedInput :=
  { record := 202, positions := [{ j := 0, mode := 0, left := 557, right := 0 }], target := { R := 3, expr := lowMeanSeedTargetExpr0202 } }

noncomputable def lowMeanSeedTargetExpr0203 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (86799, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (-1229, 500000)
  let e3 : LowMeanIntegerExpr := .atom (4, 1)
  let e4 : LowMeanIntegerExpr := .atom (17, 2)
  let e5 : LowMeanIntegerExpr := .neg (-17, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-9, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (11061, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (4893, 50000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (227, 200000)
  let e10 : LowMeanIntegerExpr := .pow (81, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (18387, 800000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-18387, 800000) e11
  let e13 : LowMeanIntegerExpr := .add (59901, 800000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (3957, 100000)
  let e15 : LowMeanIntegerExpr := .atom (103, 203)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (107, 207)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-103, 203) e15
  let e21 : LowMeanIntegerExpr := .add (100, 203) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (10300, 41209) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-107, 207) e17
  let e24 : LowMeanIntegerExpr := .add (100, 207) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (10700, 42849) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (10300, 41209) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (10300, 41209) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (407571, 41209000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (407571, 10302250) e29 e3
  let e31 : LowMeanIntegerExpr := .add (3772687509, 32967200000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (9851, 10000)
  let e33 : LowMeanIntegerExpr := .pow (100000000, 1698181681) e21 4
  let e34 : LowMeanIntegerExpr := .mul (98510000, 1698181681) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-98510000, 1698181681) e34
  let e36 : LowMeanIntegerExpr := .add (76660679558381, 1358545344800000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (76674265011829, 1358545344800000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-76660679558381, 1358545344800000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0203 : LowMeanDirectSeedInput :=
  { record := 203, positions := [{ j := 4, mode := 0, left := 558, right := 0 }], target := { R := 4, expr := lowMeanSeedTargetExpr0203 } }

noncomputable def lowMeanSeedTargetExpr0204 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (86799, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (-1229, 500000)
  let e3 : LowMeanIntegerExpr := .atom (5, 1)
  let e4 : LowMeanIntegerExpr := .atom (17, 2)
  let e5 : LowMeanIntegerExpr := .neg (-17, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-7, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (8603, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (47701, 500000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (227, 200000)
  let e10 : LowMeanIntegerExpr := .pow (49, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (11123, 800000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-11123, 800000) e11
  let e13 : LowMeanIntegerExpr := .add (325993, 4000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (3957, 100000)
  let e15 : LowMeanIntegerExpr := .atom (103, 203)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (107, 207)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-103, 203) e15
  let e21 : LowMeanIntegerExpr := .add (100, 203) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (10300, 41209) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-107, 207) e17
  let e24 : LowMeanIntegerExpr := .add (100, 207) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (10700, 42849) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (10300, 41209) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (10300, 41209) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (407571, 41209000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (407571, 8241800) e29 e3
  let e31 : LowMeanIntegerExpr := .add (21585265537, 164836000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (9851, 10000)
  let e33 : LowMeanIntegerExpr := .pow (10000000000, 344730881243) e21 5
  let e34 : LowMeanIntegerExpr := .mul (9851000000, 344730881243) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-9851000000, 344730881243) e34
  let e36 : LowMeanIntegerExpr := .add (141165963125389299, 1378923524972000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (141179752360639019, 1378923524972000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-141165963125389299, 1378923524972000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0204 : LowMeanDirectSeedInput :=
  { record := 204, positions := [{ j := 1, mode := 0, left := 559, right := 0 }, { j := 4, mode := 0, left := 560, right := 0 }], target := { R := 5, expr := lowMeanSeedTargetExpr0204 } }

noncomputable def lowMeanSeedTargetExpr0205 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (86799, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (-1229, 500000)
  let e3 : LowMeanIntegerExpr := .atom (6, 1)
  let e4 : LowMeanIntegerExpr := .atom (17, 2)
  let e5 : LowMeanIntegerExpr := .neg (-17, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-5, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (1229, 200000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (5809, 62500) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (227, 200000)
  let e10 : LowMeanIntegerExpr := .pow (25, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (227, 32000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-227, 32000) e11
  let e13 : LowMeanIntegerExpr := .add (343401, 4000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (3957, 100000)
  let e15 : LowMeanIntegerExpr := .atom (103, 203)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (107, 207)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-103, 203) e15
  let e21 : LowMeanIntegerExpr := .add (100, 203) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (10300, 41209) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-107, 207) e17
  let e24 : LowMeanIntegerExpr := .add (100, 207) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (10700, 42849) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (10300, 41209) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (10300, 41209) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (407571, 41209000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (1222713, 20604500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (23932915809, 164836000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (9851, 10000)
  let e33 : LowMeanIntegerExpr := .pow (1000000000000, 69980368892329) e21 6
  let e34 : LowMeanIntegerExpr := .mul (985100000000, 69980368892329) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-985100000000, 69980368892329) e34
  let e36 : LowMeanIntegerExpr := .add (36702039199759094929, 279921475569316000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (36704838414514788089, 279921475569316000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-36702039199759094929, 279921475569316000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0205 : LowMeanDirectSeedInput :=
  { record := 205, positions := [], target := { R := 6, expr := lowMeanSeedTargetExpr0205 } }

noncomputable def lowMeanSeedTargetExpr0206 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (86799, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (-1229, 500000)
  let e3 : LowMeanIntegerExpr := .atom (7, 1)
  let e4 : LowMeanIntegerExpr := .atom (17, 2)
  let e5 : LowMeanIntegerExpr := .neg (-17, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-3, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (3687, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (45243, 500000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (227, 200000)
  let e10 : LowMeanIntegerExpr := .pow (9, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (2043, 800000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-2043, 800000) e11
  let e13 : LowMeanIntegerExpr := .add (351729, 4000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (3957, 100000)
  let e15 : LowMeanIntegerExpr := .atom (103, 203)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (107, 207)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-103, 203) e15
  let e21 : LowMeanIntegerExpr := .add (100, 203) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (10300, 41209) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-107, 207) e17
  let e24 : LowMeanIntegerExpr := .add (100, 207) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (10700, 42849) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (10300, 41209) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (10300, 41209) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (407571, 41209000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (407571, 5887000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (3700912623, 23548000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (9851, 10000)
  let e33 : LowMeanIntegerExpr := .pow (100000000000000, 14206014885142787) e21 7
  let e34 : LowMeanIntegerExpr := .mul (98510000000000, 14206014885142787) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-98510000000000, 14206014885142787) e34
  let e36 : LowMeanIntegerExpr := .add (8536692089510928412723, 56824059540571148000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (8537260330106334124203, 56824059540571148000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-8536692089510928412723, 56824059540571148000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0206 : LowMeanDirectSeedInput :=
  { record := 206, positions := [{ j := 5, mode := 0, left := 561, right := 0 }], target := { R := 7, expr := lowMeanSeedTargetExpr0206 } }

noncomputable def lowMeanSeedTargetExpr0207 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (86799, 1000000)
  let e2 : LowMeanIntegerExpr := .atom (-1229, 500000)
  let e3 : LowMeanIntegerExpr := .atom (8, 1)
  let e4 : LowMeanIntegerExpr := .atom (17, 2)
  let e5 : LowMeanIntegerExpr := .neg (-17, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-1, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (1229, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (22007, 250000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (227, 200000)
  let e10 : LowMeanIntegerExpr := .pow (1, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (227, 800000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-227, 800000) e11
  let e13 : LowMeanIntegerExpr := .add (350977, 4000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (3957, 100000)
  let e15 : LowMeanIntegerExpr := .atom (103, 203)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (107, 207)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-103, 203) e15
  let e21 : LowMeanIntegerExpr := .add (100, 203) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (10300, 41209) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-107, 207) e17
  let e24 : LowMeanIntegerExpr := .add (100, 207) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (10700, 42849) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (10300, 41209) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (10300, 41209) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (407571, 41209000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (407571, 5151125) e29 e3
  let e31 : LowMeanIntegerExpr := .add (27505683193, 164836000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (9851, 10000)
  let e33 : LowMeanIntegerExpr := .pow (10000000000000000, 2883821021683985761) e21 8
  let e34 : LowMeanIntegerExpr := .mul (9851000000000000, 2883821021683985761) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-9851000000000000, 2883821021683985761) e34
  let e36 : LowMeanIntegerExpr := .add (1885453856481673801926497, 11535284086735943044000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (1885569209322541161356937, 11535284086735943044000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-1885453856481673801926497, 11535284086735943044000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0207 : LowMeanDirectSeedInput :=
  { record := 207, positions := [], target := { R := 8, expr := lowMeanSeedTargetExpr0207 } }

noncomputable def lowMeanSeedGroup0192 : List LowMeanDirectSeedInput := [lowMeanSeedRecord0192, lowMeanSeedRecord0193, lowMeanSeedRecord0194, lowMeanSeedRecord0195, lowMeanSeedRecord0196, lowMeanSeedRecord0197, lowMeanSeedRecord0198, lowMeanSeedRecord0199, lowMeanSeedRecord0200, lowMeanSeedRecord0201, lowMeanSeedRecord0202, lowMeanSeedRecord0203, lowMeanSeedRecord0204, lowMeanSeedRecord0205, lowMeanSeedRecord0206, lowMeanSeedRecord0207]

end Erdos993Lean.Analytic.V213
