module

public import Erdos993Lean.Analytic.V213.LowMeanCoreAll
public import Erdos993Lean.Analytic.V213.LowMeanData.Seed0464
public import Erdos993Lean.Analytic.V213.LowMeanFiberSeed
public import Erdos993Lean.Analytic.V213.LowMeanIntegerExpr
public import Erdos993Lean.Analytic.V213.LowMeanSeedGeometry
public import Erdos993Lean.Analytic.V213.LowMeanWidthData
public import Erdos993Lean.Ceiling.Prefix
public import Erdos993Lean.Ceiling.Statement

/-! Exact core/budget keys and equation-51 targets for the direct fibers. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanSeedTargetExpr0544 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (83, 800)
  let e2 : LowMeanIntegerExpr := .atom (883, 500000)
  let e3 : LowMeanIntegerExpr := .atom (9, 1)
  let e4 : LowMeanIntegerExpr := .atom (32, 1)
  let e5 : LowMeanIntegerExpr := .neg (-32, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-23, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-20309, 500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (15783, 250000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1087, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (529, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (575023, 10000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-575023, 10000000) e11
  let e13 : LowMeanIntegerExpr := .add (56297, 10000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (1009, 200000)
  let e15 : LowMeanIntegerExpr := .atom (19, 29)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (7, 10)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-19, 29) e15
  let e21 : LowMeanIntegerExpr := .add (10, 29) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (190, 841) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-7, 10) e17
  let e24 : LowMeanIntegerExpr := .add (3, 10) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (21, 100) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (190, 841) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (190, 841) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (19171, 16820000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (172539, 16820000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (133615277, 8410000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (3743, 1000)
  let e33 : LowMeanIntegerExpr := .pow (1000000000, 14507145975869) e21 9
  let e34 : LowMeanIntegerExpr := .mul (3743000000, 14507145975869) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-3743000000, 14507145975869) e34
  let e36 : LowMeanIntegerExpr := .add (2267417001242772593, 145071459758690000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (2268867715840359493, 145071459758690000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-2267417001242772593, 145071459758690000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0544 : LowMeanDirectSeedInput :=
  { record := 544, positions := [], target := { R := 9, expr := lowMeanSeedTargetExpr0544 } }

noncomputable def lowMeanSeedTargetExpr0545 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (83, 800)
  let e2 : LowMeanIntegerExpr := .atom (883, 500000)
  let e3 : LowMeanIntegerExpr := .atom (10, 1)
  let e4 : LowMeanIntegerExpr := .atom (32, 1)
  let e5 : LowMeanIntegerExpr := .neg (-32, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-22, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-9713, 250000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (32449, 500000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1087, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (484, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (131527, 2500000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-131527, 2500000) e11
  let e13 : LowMeanIntegerExpr := .add (15359, 1250000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (1009, 200000)
  let e15 : LowMeanIntegerExpr := .atom (19, 29)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (7, 10)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-19, 29) e15
  let e21 : LowMeanIntegerExpr := .add (10, 29) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (190, 841) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-7, 10) e17
  let e24 : LowMeanIntegerExpr := .add (3, 10) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (21, 100) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (190, 841) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (190, 841) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (19171, 16820000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (19171, 1682000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (12449397, 525625000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (3743, 1000)
  let e33 : LowMeanIntegerExpr := .pow (10000000000, 420707233300201) e21 10
  let e34 : LowMeanIntegerExpr := .mul (37430000000, 420707233300201) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-37430000000, 420707233300201) e34
  let e36 : LowMeanIntegerExpr := .add (6204372442777434517, 262942020812625625000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (24828007451942243093, 1051768083250502500000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-6204372442777434517, 262942020812625625000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0545 : LowMeanDirectSeedInput :=
  { record := 545, positions := [], target := { R := 10, expr := lowMeanSeedTargetExpr0545 } }

noncomputable def lowMeanSeedTargetExpr0546 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (83, 800)
  let e2 : LowMeanIntegerExpr := .atom (883, 500000)
  let e3 : LowMeanIntegerExpr := .atom (11, 1)
  let e4 : LowMeanIntegerExpr := .atom (32, 1)
  let e5 : LowMeanIntegerExpr := .neg (-32, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-21, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-18543, 500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (8333, 125000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1087, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (441, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (479367, 10000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-479367, 10000000) e11
  let e13 : LowMeanIntegerExpr := .add (187273, 10000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (1009, 200000)
  let e15 : LowMeanIntegerExpr := .atom (19, 29)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (7, 10)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-19, 29) e15
  let e21 : LowMeanIntegerExpr := .add (10, 29) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (190, 841) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-7, 10) e17
  let e24 : LowMeanIntegerExpr := .add (3, 10) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (21, 100) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (190, 841) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (190, 841) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (19171, 16820000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (210881, 16820000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (262937093, 8410000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (3743, 1000)
  let e33 : LowMeanIntegerExpr := .pow (100000000000, 12200509765705829) e21 11
  let e34 : LowMeanIntegerExpr := .mul (374300000000, 12200509765705829) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-374300000000, 12200509765705829) e34
  let e36 : LowMeanIntegerExpr := .add (3810723790621643008817, 122005097657058290000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (3811943841598213591717, 122005097657058290000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-3810723790621643008817, 122005097657058290000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0546 : LowMeanDirectSeedInput :=
  { record := 546, positions := [], target := { R := 11, expr := lowMeanSeedTargetExpr0546 } }

noncomputable def lowMeanSeedTargetExpr0547 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (83, 800)
  let e2 : LowMeanIntegerExpr := .atom (883, 500000)
  let e3 : LowMeanIntegerExpr := .atom (12, 1)
  let e4 : LowMeanIntegerExpr := .atom (32, 1)
  let e5 : LowMeanIntegerExpr := .neg (-32, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-20, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-883, 25000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (6843, 100000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1087, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (400, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1087, 25000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1087, 25000) e11
  let e13 : LowMeanIntegerExpr := .add (499, 20000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (1009, 200000)
  let e15 : LowMeanIntegerExpr := .atom (19, 29)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (7, 10)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-19, 29) e15
  let e21 : LowMeanIntegerExpr := .add (10, 29) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (190, 841) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-7, 10) e17
  let e24 : LowMeanIntegerExpr := .add (3, 10) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (21, 100) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (190, 841) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (190, 841) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (19171, 16820000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (57513, 4205000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (649711, 16820000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (3743, 1000)
  let e33 : LowMeanIntegerExpr := .pow (1000000000000, 353814783205469041) e21 12
  let e34 : LowMeanIntegerExpr := .mul (3743000000000, 353814783205469041) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-3743000000000, 353814783205469041) e34
  let e36 : LowMeanIntegerExpr := .add (273263257254706891911, 7076295664109380820000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (341667525264184982149, 8845369580136726025000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-273263257254706891911, 7076295664109380820000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0547 : LowMeanDirectSeedInput :=
  { record := 547, positions := [], target := { R := 12, expr := lowMeanSeedTargetExpr0547 } }

noncomputable def lowMeanSeedTargetExpr0548 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (83, 800)
  let e2 : LowMeanIntegerExpr := .atom (883, 500000)
  let e3 : LowMeanIntegerExpr := .atom (13, 1)
  let e4 : LowMeanIntegerExpr := .atom (32, 1)
  let e5 : LowMeanIntegerExpr := .neg (-32, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-19, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-16777, 500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (17549, 250000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1087, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (361, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (392407, 10000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-392407, 10000000) e11
  let e13 : LowMeanIntegerExpr := .add (309553, 10000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (1009, 200000)
  let e15 : LowMeanIntegerExpr := .atom (19, 29)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (7, 10)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-19, 29) e15
  let e21 : LowMeanIntegerExpr := .add (10, 29) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (190, 841) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-7, 10) e17
  let e24 : LowMeanIntegerExpr := .add (3, 10) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (21, 100) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (190, 841) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (190, 841) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (19171, 16820000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (249223, 16820000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (384945573, 8410000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (3743, 1000)
  let e33 : LowMeanIntegerExpr := .pow (10000000000000, 10260628712958602189) e21 13
  let e34 : LowMeanIntegerExpr := .mul (37430000000000, 10260628712958602189) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-37430000000000, 10260628712958602189) e34
  let e36 : LowMeanIntegerExpr := .add (4696157922651726093845017, 102606287129586021890000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (4697183985523021954063917, 102606287129586021890000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-4696157922651726093845017, 102606287129586021890000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0548 : LowMeanDirectSeedInput :=
  { record := 548, positions := [], target := { R := 13, expr := lowMeanSeedTargetExpr0548 } }

noncomputable def lowMeanSeedTargetExpr0549 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (83, 800)
  let e2 : LowMeanIntegerExpr := .atom (883, 500000)
  let e3 : LowMeanIntegerExpr := .atom (14, 1)
  let e4 : LowMeanIntegerExpr := .atom (32, 1)
  let e5 : LowMeanIntegerExpr := .neg (-32, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-18, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-7947, 250000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (35981, 500000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1087, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (324, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (88047, 2500000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-88047, 2500000) e11
  let e13 : LowMeanIntegerExpr := .add (45929, 1250000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (1009, 200000)
  let e15 : LowMeanIntegerExpr := .atom (19, 29)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (7, 10)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-19, 29) e15
  let e21 : LowMeanIntegerExpr := .add (10, 29) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (190, 841) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-7, 10) e17
  let e24 : LowMeanIntegerExpr := .add (3, 10) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (21, 100) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (190, 841) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (190, 841) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (19171, 16820000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (134197, 8410000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (27700457, 525625000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (3743, 1000)
  let e33 : LowMeanIntegerExpr := .pow (100000000000000, 297558232675799463481) e21 14
  let e34 : LowMeanIntegerExpr := .mul (374300000000000, 297558232675799463481) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-374300000000000, 297558232675799463481) e34
  let e36 : LowMeanIntegerExpr := .add (9800597250647417335051737, 185973895422374664675625000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (39209827958406564326793973, 743895581689498658702500000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-9800597250647417335051737, 185973895422374664675625000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0549 : LowMeanDirectSeedInput :=
  { record := 549, positions := [], target := { R := 14, expr := lowMeanSeedTargetExpr0549 } }

noncomputable def lowMeanSeedTargetExpr0550 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (83, 800)
  let e2 : LowMeanIntegerExpr := .atom (883, 500000)
  let e3 : LowMeanIntegerExpr := .atom (15, 1)
  let e4 : LowMeanIntegerExpr := .atom (32, 1)
  let e5 : LowMeanIntegerExpr := .neg (-32, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-17, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-15011, 500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (1152, 15625) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1087, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (289, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (314143, 10000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-314143, 10000000) e11
  let e13 : LowMeanIntegerExpr := .add (423137, 10000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (1009, 200000)
  let e15 : LowMeanIntegerExpr := .atom (19, 29)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (7, 10)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-19, 29) e15
  let e21 : LowMeanIntegerExpr := .add (10, 29) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (190, 841) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-7, 10) e17
  let e24 : LowMeanIntegerExpr := .add (3, 10) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (21, 100) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (190, 841) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (190, 841) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (19171, 16820000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (57513, 3364000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (499640717, 8410000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (3743, 1000)
  let e33 : LowMeanIntegerExpr := .pow (1000000000000000, 8629188747598184440949) e21 15
  let e34 : LowMeanIntegerExpr := .mul (3743000000000000, 8629188747598184440949) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-3743000000000000, 8629188747598184440949) e34
  let e36 : LowMeanIntegerExpr := .add (5126590457013423189029729513, 86291887475981844409490000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (5127453375888183007473824413, 86291887475981844409490000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-5126590457013423189029729513, 86291887475981844409490000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0550 : LowMeanDirectSeedInput :=
  { record := 550, positions := [], target := { R := 15, expr := lowMeanSeedTargetExpr0550 } }

noncomputable def lowMeanSeedTargetExpr0551 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (83, 800)
  let e2 : LowMeanIntegerExpr := .atom (883, 500000)
  let e3 : LowMeanIntegerExpr := .atom (16, 1)
  let e4 : LowMeanIntegerExpr := .atom (32, 1)
  let e5 : LowMeanIntegerExpr := .neg (-32, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-16, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-883, 31250) e2 e6
  let e8 : LowMeanIntegerExpr := .add (37747, 500000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1087, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (256, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (2174, 78125) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-2174, 78125) e11
  let e13 : LowMeanIntegerExpr := .add (119167, 2500000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (1009, 200000)
  let e15 : LowMeanIntegerExpr := .atom (19, 29)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (7, 10)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-19, 29) e15
  let e21 : LowMeanIntegerExpr := .add (10, 29) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (190, 841) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-7, 10) e17
  let e24 : LowMeanIntegerExpr := .add (3, 10) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (21, 100) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (190, 841) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (190, 841) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (19171, 16820000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (19171, 1051250) e29 e3
  let e31 : LowMeanIntegerExpr := .add (138561447, 2102500000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (3743, 1000)
  let e33 : LowMeanIntegerExpr := .pow (10000000000000000, 250246473680347348787521) e21 16
  let e34 : LowMeanIntegerExpr := .mul (37430000000000000, 250246473680347348787521) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-37430000000000000, 250246473680347348787521) e34
  let e36 : LowMeanIntegerExpr := .add (41230005711321455541751017007, 625616184200868371968802500000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (5154532734145433028183838129, 78202023025108546496100312500) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-41230005711321455541751017007, 625616184200868371968802500000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0551 : LowMeanDirectSeedInput :=
  { record := 551, positions := [], target := { R := 16, expr := lowMeanSeedTargetExpr0551 } }

noncomputable def lowMeanSeedTargetExpr0552 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (83, 800)
  let e2 : LowMeanIntegerExpr := .atom (883, 500000)
  let e3 : LowMeanIntegerExpr := .atom (17, 1)
  let e4 : LowMeanIntegerExpr := .atom (32, 1)
  let e5 : LowMeanIntegerExpr := .neg (-32, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-15, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-2649, 100000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (3863, 50000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1087, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (225, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (9783, 400000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-9783, 400000) e11
  let e13 : LowMeanIntegerExpr := .add (21121, 400000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (1009, 200000)
  let e15 : LowMeanIntegerExpr := .atom (19, 29)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (7, 10)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-19, 29) e15
  let e21 : LowMeanIntegerExpr := .add (10, 29) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (190, 841) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-7, 10) e17
  let e24 : LowMeanIntegerExpr := .add (3, 10) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (21, 100) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (190, 841) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (190, 841) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (19171, 16820000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (325907, 16820000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (24280901, 336400000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (3743, 1000)
  let e33 : LowMeanIntegerExpr := .pow (100000000000000000, 7257147736730073114838109) e21 17
  let e34 : LowMeanIntegerExpr := .mul (374300000000000000, 7257147736730073114838109) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-374300000000000000, 7257147736730073114838109) e34
  let e36 : LowMeanIntegerExpr := .add (209524327970745504190423015049, 2902859094692029245935243600000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (41910671312338484896576473497, 580571818938405849187048720000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-209524327970745504190423015049, 2902859094692029245935243600000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0552 : LowMeanDirectSeedInput :=
  { record := 552, positions := [], target := { R := 17, expr := lowMeanSeedTargetExpr0552 } }

noncomputable def lowMeanSeedTargetExpr0553 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (83, 800)
  let e2 : LowMeanIntegerExpr := .atom (883, 500000)
  let e3 : LowMeanIntegerExpr := .atom (18, 1)
  let e4 : LowMeanIntegerExpr := .atom (32, 1)
  let e5 : LowMeanIntegerExpr := .neg (-32, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-14, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-6181, 250000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (39513, 500000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1087, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (196, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (53263, 2500000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-53263, 2500000) e11
  let e13 : LowMeanIntegerExpr := .add (72151, 1250000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (1009, 200000)
  let e15 : LowMeanIntegerExpr := .atom (19, 29)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (7, 10)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-19, 29) e15
  let e21 : LowMeanIntegerExpr := .add (10, 29) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (190, 841) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-7, 10) e17
  let e24 : LowMeanIntegerExpr := .add (3, 10) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (21, 100) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (190, 841) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (190, 841) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (19171, 16820000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (172539, 8410000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (41123183, 525625000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (3743, 1000)
  let e33 : LowMeanIntegerExpr := .pow (1000000000000000000, 210457284365172120330305161) e21 18
  let e34 : LowMeanIntegerExpr := .mul (3743000000000000000, 210457284365172120330305161) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-3743000000000000000, 210457284365172120330305161) e34
  let e36 : LowMeanIntegerExpr := .add (10290929192886607527754054199343, 131535802728232575206440725625000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (41168978203655559414024474426397, 526143210912930300825762902500000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-10290929192886607527754054199343, 131535802728232575206440725625000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0553 : LowMeanDirectSeedInput :=
  { record := 553, positions := [], target := { R := 18, expr := lowMeanSeedTargetExpr0553 } }

noncomputable def lowMeanSeedTargetExpr0554 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (83, 800)
  let e2 : LowMeanIntegerExpr := .atom (883, 500000)
  let e3 : LowMeanIntegerExpr := .atom (19, 1)
  let e4 : LowMeanIntegerExpr := .atom (32, 1)
  let e5 : LowMeanIntegerExpr := .neg (-32, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-13, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-11479, 500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (10099, 125000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1087, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (169, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (183703, 10000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-183703, 10000000) e11
  let e13 : LowMeanIntegerExpr := .add (624217, 10000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (1009, 200000)
  let e15 : LowMeanIntegerExpr := .atom (19, 29)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (7, 10)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-19, 29) e15
  let e21 : LowMeanIntegerExpr := .add (10, 29) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (190, 841) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-7, 10) e17
  let e24 : LowMeanIntegerExpr := .add (3, 10) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (21, 100) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (190, 841) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (190, 841) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (19171, 16820000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (364249, 16820000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (707090997, 8410000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (3743, 1000)
  let e33 : LowMeanIntegerExpr := .pow (10000000000000000000, 6103261246589991489578849669) e21 19
  let e34 : LowMeanIntegerExpr := .mul (37430000000000000000, 6103261246589991489578849669) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-37430000000000000000, 6103261246589991489578849669) e34
  let e36 : LowMeanIntegerExpr := .add (5131463454240760918653773986404673, 61032612465899914895788496690000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (5132073780365419917802731871371573, 61032612465899914895788496690000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-5131463454240760918653773986404673, 61032612465899914895788496690000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0554 : LowMeanDirectSeedInput :=
  { record := 554, positions := [{ j := 17, mode := 0, left := 1057, right := 0 }], target := { R := 19, expr := lowMeanSeedTargetExpr0554 } }

noncomputable def lowMeanSeedTargetExpr0555 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (83, 800)
  let e2 : LowMeanIntegerExpr := .atom (883, 500000)
  let e3 : LowMeanIntegerExpr := .atom (20, 1)
  let e4 : LowMeanIntegerExpr := .atom (32, 1)
  let e5 : LowMeanIntegerExpr := .neg (-32, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-12, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-2649, 125000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (41279, 500000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1087, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (144, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (9783, 625000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-9783, 625000) e11
  let e13 : LowMeanIntegerExpr := .add (167263, 2500000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (1009, 200000)
  let e15 : LowMeanIntegerExpr := .atom (19, 29)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (7, 10)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-19, 29) e15
  let e21 : LowMeanIntegerExpr := .add (10, 29) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (190, 841) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-7, 10) e17
  let e24 : LowMeanIntegerExpr := .add (3, 10) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (21, 100) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (190, 841) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (190, 841) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (19171, 16820000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (19171, 841000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (188595683, 2102500000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (3743, 1000)
  let e33 : LowMeanIntegerExpr := .pow (100000000000000000000, 176994576151109753197786640401) e21 20
  let e34 : LowMeanIntegerExpr := .mul (374300000000000000000, 176994576151109753197786640401) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-374300000000000000000, 176994576151109753197786640401) e34
  let e36 : LowMeanIntegerExpr := .add (39691334351424857446252087437219963, 442486440377774382994466601002500000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (9923939803957158797520508025807497, 110621610094443595748616650250625000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-39691334351424857446252087437219963, 442486440377774382994466601002500000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0555 : LowMeanDirectSeedInput :=
  { record := 555, positions := [{ j := 18, mode := 0, left := 1058, right := 0 }], target := { R := 20, expr := lowMeanSeedTargetExpr0555 } }

noncomputable def lowMeanSeedTargetExpr0556 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (83, 800)
  let e2 : LowMeanIntegerExpr := .atom (883, 500000)
  let e3 : LowMeanIntegerExpr := .atom (24, 1)
  let e4 : LowMeanIntegerExpr := .atom (32, 1)
  let e5 : LowMeanIntegerExpr := .neg (-32, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-8, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-883, 62500) e2 e6
  let e8 : LowMeanIntegerExpr := .add (44811, 500000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1087, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (64, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1087, 156250) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1087, 156250) e11
  let e13 : LowMeanIntegerExpr := .add (206663, 2500000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (1009, 200000)
  let e15 : LowMeanIntegerExpr := .atom (19, 29)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (7, 10)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-19, 29) e15
  let e21 : LowMeanIntegerExpr := .add (10, 29) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (190, 841) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-7, 10) e17
  let e24 : LowMeanIntegerExpr := .add (3, 10) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (21, 100) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (190, 841) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (190, 841) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (19171, 16820000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (57513, 2102500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (231316583, 2102500000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (3743, 1000)
  let e33 : LowMeanIntegerExpr := .pow (1000000000000000000000000, 125184900814733057351483732809459681) e21 24
  let e34 : LowMeanIntegerExpr := .mul (3743000000000000000000000, 125184900814733057351483732809459681) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-3743000000000000000000000, 125184900814733057351483732809459681) e34
  let e36 : LowMeanIntegerExpr := .add (34432037445646027804623361538132227687503, 312962252036832643378709332023649202500000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (4304395883520799516382143578931558022441, 39120281504604080422338666502956150312500) e0 e36
  let e38 : LowMeanIntegerExpr := .atom (21, 1)
  let e39 : LowMeanIntegerExpr := .add (-11, 1) e38 e5
  let e40 : LowMeanIntegerExpr := .mul (-9713, 500000) e2 e39
  let e41 : LowMeanIntegerExpr := .add (21081, 250000) e1 e40
  let e42 : LowMeanIntegerExpr := .pow (121, 1) e39 2
  let e43 : LowMeanIntegerExpr := .mul (131527, 10000000) e9 e42
  let e44 : LowMeanIntegerExpr := .neg (-131527, 10000000) e43
  let e45 : LowMeanIntegerExpr := .add (711713, 10000000) e41 e44
  let e46 : LowMeanIntegerExpr := .mul (402591, 16820000) e29 e38
  let e47 : LowMeanIntegerExpr := .add (799846133, 8410000000) e45 e46
  let e48 : LowMeanIntegerExpr := .pow (1000000000000000000000, 5132842708382182842735812571629) e21 21
  let e49 : LowMeanIntegerExpr := .mul (3743000000000000000000, 5132842708382182842735812571629) e32 e48
  let e50 : LowMeanIntegerExpr := .neg (-3743000000000000000000, 5132842708382182842735812571629) e49
  let e51 : LowMeanIntegerExpr := .add (4881669869343764129442552706337979977, 51328427083821828427358125716290000000) e47 e50
  let e52 : LowMeanIntegerExpr := .neg (-4881669869343764129442552706337979977, 51328427083821828427358125716290000000) e51
  let e53 : LowMeanIntegerExpr := .add (18681621829240521171254176570932863059059, 1251849008147330573514837328094596810000000) e37 e52
  e53

noncomputable def lowMeanSeedRecord0556 : LowMeanDirectSeedInput :=
  { record := 556, positions := [{ j := 11, mode := 0, left := 1059, right := 0 }, { j := 12, mode := 0, left := 1060, right := 0 }, { j := 18, mode := 0, left := 1061, right := 0 }, { j := 19, mode := 0, left := 1062, right := 0 }], target := { R := 24, expr := lowMeanSeedTargetExpr0556 } }

noncomputable def lowMeanSeedTargetExpr0557 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (83, 800)
  let e2 : LowMeanIntegerExpr := .atom (883, 500000)
  let e3 : LowMeanIntegerExpr := .atom (28, 1)
  let e4 : LowMeanIntegerExpr := .atom (32, 1)
  let e5 : LowMeanIntegerExpr := .neg (-32, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-4, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-883, 125000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (48343, 500000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1087, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (16, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1087, 625000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1087, 625000) e11
  let e13 : LowMeanIntegerExpr := .add (237367, 2500000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (1009, 200000)
  let e15 : LowMeanIntegerExpr := .atom (19, 29)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (7, 10)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-19, 29) e15
  let e21 : LowMeanIntegerExpr := .add (10, 29) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (190, 841) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-7, 10) e17
  let e24 : LowMeanIntegerExpr := .add (3, 10) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (21, 100) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (190, 841) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (190, 841) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (19171, 16820000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (134197, 4205000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (266724147, 2102500000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (3743, 1000)
  let e33 : LowMeanIntegerExpr := .pow (10000000000000000000000000000, 88540901833145211536614766025207452637361) e21 28
  let e34 : LowMeanIntegerExpr := .mul (37430000000000000000000000000, 88540901833145211536614766025207452637361) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-37430000000000000000000000000, 88540901833145211536614766025207452637361) e34
  let e36 : LowMeanIntegerExpr := .add (28080851980948509273767101944920378481263986987, 221352254582863028841536915063018631593402500000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (7020766375873584476013879328517752166894980253, 55338063645715757210384228765754657898350625000) e0 e36
  let e38 : LowMeanIntegerExpr := .atom (25, 1)
  let e39 : LowMeanIntegerExpr := .add (-7, 1) e38 e5
  let e40 : LowMeanIntegerExpr := .mul (-6181, 500000) e2 e39
  let e41 : LowMeanIntegerExpr := .add (22847, 250000) e1 e40
  let e42 : LowMeanIntegerExpr := .pow (49, 1) e39 2
  let e43 : LowMeanIntegerExpr := .mul (53263, 10000000) e9 e42
  let e44 : LowMeanIntegerExpr := .neg (-53263, 10000000) e43
  let e45 : LowMeanIntegerExpr := .add (860617, 10000000) e41 e44
  let e46 : LowMeanIntegerExpr := .mul (19171, 672800) e29 e38
  let e47 : LowMeanIntegerExpr := .add (963416397, 8410000000) e45 e46
  let e48 : LowMeanIntegerExpr := .pow (10000000000000000000000000, 3630362123627258663193028251474330749) e21 25
  let e49 : LowMeanIntegerExpr := .mul (37430000000000000000000000, 3630362123627258663193028251474330749) e32 e48
  let e50 : LowMeanIntegerExpr := .neg (-37430000000000000000000000, 3630362123627258663193028251474330749) e49
  let e51 : LowMeanIntegerExpr := .add (4158799520375096090702097257496563220199633, 36303621236272586631930282514743307490000000) e47 e50
  let e52 : LowMeanIntegerExpr := .neg (-4158799520375096090702097257496563220199633, 36303621236272586631930282514743307490000000) e51
  let e53 : LowMeanIntegerExpr := .add (10903300511549133060088619243200354292870834811, 885409018331452115366147660252074526373610000000) e37 e52
  e53

noncomputable def lowMeanSeedRecord0557 : LowMeanDirectSeedInput :=
  { record := 557, positions := [{ j := 14, mode := 0, left := 1063, right := 0 }, { j := 15, mode := 0, left := 1064, right := 0 }, { j := 20, mode := 0, left := 1065, right := 0 }, { j := 21, mode := 0, left := 1066, right := 0 }, { j := 22, mode := 0, left := 1067, right := 0 }], target := { R := 28, expr := lowMeanSeedTargetExpr0557 } }

noncomputable def lowMeanSeedTargetExpr0558 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (83, 800)
  let e2 : LowMeanIntegerExpr := .atom (883, 500000)
  let e3 : LowMeanIntegerExpr := .atom (31, 1)
  let e4 : LowMeanIntegerExpr := .atom (32, 1)
  let e5 : LowMeanIntegerExpr := .neg (-32, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-1, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-883, 500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (3187, 31250) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1087, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (1, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1087, 10000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1087, 10000000) e11
  let e13 : LowMeanIntegerExpr := .add (1018753, 10000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (1009, 200000)
  let e15 : LowMeanIntegerExpr := .atom (19, 29)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (7, 10)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-19, 29) e15
  let e21 : LowMeanIntegerExpr := .add (10, 29) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (190, 841) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-7, 10) e17
  let e24 : LowMeanIntegerExpr := .add (3, 10) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (21, 100) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (190, 841) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (190, 841) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (19171, 16820000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (594301, 16820000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (1153921773, 8410000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (3743, 1000)
  let e33 : LowMeanIntegerExpr := .pow (10000000000000000000000000000000, 2159424054808578564166497528588784562372597429) e21 31
  let e34 : LowMeanIntegerExpr := .mul (37430000000000000000000000000000, 2159424054808578564166497528588784562372597429) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-37430000000000000000000000000000, 2159424054808578564166497528588784562372597429) e34
  let e36 : LowMeanIntegerExpr := .add (2962908958362960007220926391663838846763396803670537, 21594240548085785641664975285887845623725974290000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (2963124900768440865077343041416697725219634063413437, 21594240548085785641664975285887845623725974290000000) e0 e36
  let e38 : LowMeanIntegerExpr := .atom (29, 1)
  let e39 : LowMeanIntegerExpr := .add (-3, 1) e38 e5
  let e40 : LowMeanIntegerExpr := .mul (-2649, 500000) e2 e39
  let e41 : LowMeanIntegerExpr := .add (24613, 250000) e1 e40
  let e42 : LowMeanIntegerExpr := .pow (9, 1) e39 2
  let e43 : LowMeanIntegerExpr := .mul (9783, 10000000) e9 e42
  let e44 : LowMeanIntegerExpr := .neg (-9783, 10000000) e43
  let e45 : LowMeanIntegerExpr := .add (974737, 10000000) e41 e44
  let e46 : LowMeanIntegerExpr := .mul (19171, 580000) e29 e38
  let e47 : LowMeanIntegerExpr := .add (37852873, 290000000) e45 e46
  let e48 : LowMeanIntegerExpr := .pow (100000000000000000000000000000, 2567686153161211134561828214731016126483469) e21 29
  let e49 : LowMeanIntegerExpr := .mul (374300000000000000000000000000, 2567686153161211134561828214731016126483469) e32 e48
  let e50 : LowMeanIntegerExpr := .neg (-374300000000000000000000000000, 2567686153161211134561828214731016126483469) e49
  let e51 : LowMeanIntegerExpr := .add (3351527512391769882853613588276892503335540988153, 25676861531612111345618282147310161264834690000000) e47 e50
  let e52 : LowMeanIntegerExpr := .neg (-3351527512391769882853613588276892503335540988153, 25676861531612111345618282147310161264834690000000) e51
  let e53 : LowMeanIntegerExpr := .add (36122565711740598399363503418957782478611023094191, 5398560137021446410416243821471961405931493572500000) e37 e52
  e53

noncomputable def lowMeanSeedRecord0558 : LowMeanDirectSeedInput :=
  { record := 558, positions := [{ j := 16, mode := 0, left := 1068, right := 0 }, { j := 17, mode := 0, left := 1069, right := 0 }, { j := 18, mode := 0, left := 1070, right := 0 }, { j := 23, mode := 0, left := 1071, right := 0 }, { j := 24, mode := 0, left := 1072, right := 0 }, { j := 25, mode := 0, left := 1073, right := 0 }], target := { R := 31, expr := lowMeanSeedTargetExpr0558 } }

noncomputable def lowMeanSeedTargetExpr0559 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (83, 800)
  let e2 : LowMeanIntegerExpr := .atom (883, 500000)
  let e3 : LowMeanIntegerExpr := .atom (34, 1)
  let e4 : LowMeanIntegerExpr := .atom (32, 1)
  let e5 : LowMeanIntegerExpr := .neg (-32, 1) e4
  let e6 : LowMeanIntegerExpr := .add (2, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (883, 250000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (53641, 500000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1087, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (4, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1087, 2500000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1087, 2500000) e11
  let e13 : LowMeanIntegerExpr := .add (133559, 1250000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (1009, 200000)
  let e15 : LowMeanIntegerExpr := .atom (19, 29)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (7, 10)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-19, 29) e15
  let e21 : LowMeanIntegerExpr := .add (10, 29) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (190, 841) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-7, 10) e17
  let e24 : LowMeanIntegerExpr := .add (3, 10) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (21, 100) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (190, 841) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (190, 841) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (19171, 16820000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (325907, 8410000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (76530747, 525625000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (3743, 1000)
  let e33 : LowMeanIntegerExpr := .pow (10000000000000000000000000000000000, 52666193272726422601456708224751866691705278695881) e21 34
  let e34 : LowMeanIntegerExpr := .mul (37430000000000000000000000000000000, 52666193272726422601456708224751866691705278695881) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-37430000000000000000000000000000000, 52666193272726422601456708224751866691705278695881) e34
  let e36 : LowMeanIntegerExpr := .add (4792607744123790932441635158860052613032846233577834427, 32916370795454014125910442640469916682315799184925625000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (19171747631326981890331577053145829248798677566278734733, 131665483181816056503641770561879666729263196739702500000) e0 e36
  let e38 : LowMeanIntegerExpr := .add (0, 1) e4 e5
  let e39 : LowMeanIntegerExpr := .mul (0, 1) e2 e38
  let e40 : LowMeanIntegerExpr := .add (83, 800) e1 e39
  let e41 : LowMeanIntegerExpr := .pow (0, 1) e38 2
  let e42 : LowMeanIntegerExpr := .mul (0, 1) e9 e41
  let e43 : LowMeanIntegerExpr := .neg (0, 1) e42
  let e44 : LowMeanIntegerExpr := .add (83, 800) e40 e43
  let e45 : LowMeanIntegerExpr := .mul (19171, 525625) e29 e4
  let e46 : LowMeanIntegerExpr := .add (2358547, 16820000) e44 e45
  let e47 : LowMeanIntegerExpr := .pow (100000000000000000000000000000000, 62623297589448778360828428329074752308805325441) e21 32
  let e48 : LowMeanIntegerExpr := .mul (374300000000000000000000000000000, 62623297589448778360828428329074752308805325441) e32 e47
  let e49 : LowMeanIntegerExpr := .neg (-374300000000000000000000000000000, 62623297589448778360828428329074752308805325441) e48
  let e50 : LowMeanIntegerExpr := .add (175624245730910050095834491260706622870006984426747, 1252465951788975567216568566581495046176106508820000) e46 e49
  let e51 : LowMeanIntegerExpr := .neg (-175624245730910050095834491260706622870006984426747, 1252465951788975567216568566581495046176106508820000) e50
  let e52 : LowMeanIntegerExpr := .add (354624399432531437003488079682022759794596664208478179, 65832741590908028251820885280939833364631598369851250000) e37 e51
  e52

noncomputable def lowMeanSeedRecord0559 : LowMeanDirectSeedInput :=
  { record := 559, positions := [{ j := 18, mode := 0, left := 1074, right := 0 }, { j := 19, mode := 0, left := 1075, right := 0 }, { j := 20, mode := 0, left := 1076, right := 0 }, { j := 24, mode := 0, left := 1077, right := 0 }, { j := 25, mode := 0, left := 1078, right := 0 }, { j := 26, mode := 0, left := 1079, right := 0 }, { j := 27, mode := 0, left := 1080, right := 0 }, { j := 28, mode := 0, left := 1081, right := 0 }], target := { R := 34, expr := lowMeanSeedTargetExpr0559 } }

noncomputable def lowMeanSeedGroup0544 : List LowMeanDirectSeedInput := [lowMeanSeedRecord0544, lowMeanSeedRecord0545, lowMeanSeedRecord0546, lowMeanSeedRecord0547, lowMeanSeedRecord0548, lowMeanSeedRecord0549, lowMeanSeedRecord0550, lowMeanSeedRecord0551, lowMeanSeedRecord0552, lowMeanSeedRecord0553, lowMeanSeedRecord0554, lowMeanSeedRecord0555, lowMeanSeedRecord0556, lowMeanSeedRecord0557, lowMeanSeedRecord0558, lowMeanSeedRecord0559]

end Erdos993Lean.Analytic.V213
