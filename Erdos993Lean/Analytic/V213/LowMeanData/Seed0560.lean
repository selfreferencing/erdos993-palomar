module

public import Erdos993Lean.Analytic.V213.LowMeanCoreAll
public import Erdos993Lean.Analytic.V213.LowMeanData.Seed0480
public import Erdos993Lean.Analytic.V213.LowMeanFiberSeed
public import Erdos993Lean.Analytic.V213.LowMeanIntegerExpr
public import Erdos993Lean.Analytic.V213.LowMeanSeedGeometry
public import Erdos993Lean.Analytic.V213.LowMeanWidthData
public import Erdos993Lean.Ceiling.Prefix
public import Erdos993Lean.Ceiling.Statement

/-! Exact core/budget keys and equation-51 targets for the direct fibers. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanSeedTargetExpr0560 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (83, 800)
  let e2 : LowMeanIntegerExpr := .atom (883, 500000)
  let e3 : LowMeanIntegerExpr := .atom (35, 1)
  let e4 : LowMeanIntegerExpr := .atom (32, 1)
  let e5 : LowMeanIntegerExpr := .neg (-32, 1) e4
  let e6 : LowMeanIntegerExpr := .add (3, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (2649, 500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (13631, 125000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1087, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (9, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (9783, 10000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-9783, 10000000) e11
  let e13 : LowMeanIntegerExpr := .add (1080697, 10000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (134197, 3364000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (1244358677, 8410000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (3743, 1000)
  let e33 : LowMeanIntegerExpr := .pow (100000000000000000000000000000000000, 1527319604909066255442244538517804134059453082180549) e21 35
  let e34 : LowMeanIntegerExpr := .mul (374300000000000000000000000000000000, 1527319604909066255442244538517804134059453082180549) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-374300000000000000000000000000000000, 1527319604909066255442244538517804134059453082180549) e34
  let e36 : LowMeanIntegerExpr := .add (2259849468395725616010054059287146603095543016273198845153, 15273196049090662554422445385178041340594530821805490000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (2260002200356216522635598283740998383508948961581416900053, 15273196049090662554422445385178041340594530821805490000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-2259849468395725616010054059287146603095543016273198845153, 15273196049090662554422445385178041340594530821805490000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0560 : LowMeanDirectSeedInput :=
  { record := 560, positions := [{ j := 20, mode := 0, left := 1082, right := 0 }, { j := 21, mode := 0, left := 1083, right := 0 }, { j := 22, mode := 0, left := 1084, right := 0 }, { j := 26, mode := 0, left := 1085, right := 0 }, { j := 27, mode := 0, left := 1086, right := 0 }, { j := 28, mode := 0, left := 1087, right := 0 }, { j := 29, mode := 0, left := 1088, right := 0 }, { j := 30, mode := 0, left := 1089, right := 0 }], target := { R := 35, expr := lowMeanSeedTargetExpr0560 } }

noncomputable def lowMeanSeedTargetExpr0561 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (83, 800)
  let e2 : LowMeanIntegerExpr := .atom (883, 500000)
  let e3 : LowMeanIntegerExpr := .atom (38, 1)
  let e4 : LowMeanIntegerExpr := .atom (32, 1)
  let e5 : LowMeanIntegerExpr := .neg (-32, 1) e4
  let e6 : LowMeanIntegerExpr := .add (6, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (2649, 250000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (57173, 500000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1087, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (36, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (9783, 2500000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-9783, 2500000) e11
  let e13 : LowMeanIntegerExpr := .add (138041, 1250000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (364249, 8410000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (80811803, 525625000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (3743, 1000)
  let e33 : LowMeanIntegerExpr := .pow (100000000000000000000000000000000000000, 37249797844127216903980902049910725025576001221301409561) e21 38
  let e34 : LowMeanIntegerExpr := .mul (374300000000000000000000000000000000000, 37249797844127216903980902049910725025576001221301409561) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-374300000000000000000000000000000000000, 37249797844127216903980902049910725025576001221301409561) e34
  let e36 : LowMeanIntegerExpr := .add (3579338079868529325376143962211274290551745270182602750375563, 23281123652579510564988063781194203140985000763313380975625000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (14318283564420220481927175371396344930332620480760943536741277, 93124494610318042259952255124776812563940003053253523902500000) e0 e36
  let e38 : LowMeanIntegerExpr := .atom (36, 1)
  let e39 : LowMeanIntegerExpr := .add (4, 1) e38 e5
  let e40 : LowMeanIntegerExpr := .mul (883, 125000) e2 e39
  let e41 : LowMeanIntegerExpr := .add (55407, 500000) e1 e40
  let e42 : LowMeanIntegerExpr := .pow (16, 1) e39 2
  let e43 : LowMeanIntegerExpr := .mul (1087, 625000) e9 e42
  let e44 : LowMeanIntegerExpr := .neg (-1087, 625000) e43
  let e45 : LowMeanIntegerExpr := .add (272687, 2500000) e41 e44
  let e46 : LowMeanIntegerExpr := .mul (172539, 4205000) e29 e38
  let e47 : LowMeanIntegerExpr := .add (315599267, 2102500000) e45 e46
  let e48 : LowMeanIntegerExpr := .pow (1000000000000000000000000000000000000, 44292268542362921407825091617016319887724139383235921) e21 36
  let e49 : LowMeanIntegerExpr := .mul (3743000000000000000000000000000000000, 44292268542362921407825091617016319887724139383235921) e32 e48
  let e50 : LowMeanIntegerExpr := .neg (-3743000000000000000000000000000000000, 44292268542362921407825091617016319887724139383235921) e49
  let e51 : LowMeanIntegerExpr := .add (16621411992552780707051970247964560384783900936450759519227, 110730671355907303519562729042540799719310348458089802500000) e47 e50
  let e52 : LowMeanIntegerExpr := .neg (-16621411992552780707051970247964560384783900936450759519227, 110730671355907303519562729042540799719310348458089802500000) e51
  let e53 : LowMeanIntegerExpr := .add (33967607868333190729646839285814964672935979320585478107137, 9312449461031804225995225512477681256394000305325352390250000) e37 e52
  e53

noncomputable def lowMeanSeedRecord0561 : LowMeanDirectSeedInput :=
  { record := 561, positions := [{ j := 21, mode := 0, left := 1090, right := 0 }, { j := 22, mode := 0, left := 1091, right := 0 }, { j := 23, mode := 0, left := 1092, right := 0 }, { j := 27, mode := 0, left := 1093, right := 0 }, { j := 28, mode := 0, left := 1094, right := 0 }, { j := 29, mode := 0, left := 1095, right := 0 }, { j := 30, mode := 0, left := 1096, right := 0 }], target := { R := 38, expr := lowMeanSeedTargetExpr0561 } }

noncomputable def lowMeanSeedTargetExpr0562 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (83, 800)
  let e2 : LowMeanIntegerExpr := .atom (883, 500000)
  let e3 : LowMeanIntegerExpr := .atom (40, 1)
  let e4 : LowMeanIntegerExpr := .atom (32, 1)
  let e5 : LowMeanIntegerExpr := .neg (-32, 1) e4
  let e6 : LowMeanIntegerExpr := .add (8, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (883, 62500) e2 e6
  let e8 : LowMeanIntegerExpr := .add (58939, 500000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1087, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (64, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1087, 156250) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1087, 156250) e11
  let e13 : LowMeanIntegerExpr := .add (277303, 2500000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (19171, 420500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (329066823, 2102500000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (3743, 1000)
  let e33 : LowMeanIntegerExpr := .pow (10000000000000000000000000000000000000000, 31327079986910989416247938623974919746509417027114485440801) e21 40
  let e34 : LowMeanIntegerExpr := .mul (37430000000000000000000000000000000000000, 31327079986910989416247938623974919746509417027114485440801) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-37430000000000000000000000000000000000000, 31327079986910989416247938623974919746509417027114485440801) e34
  let e36 : LowMeanIntegerExpr := .add (12257672633959192380849891490238309717792888466937774769660094703, 78317699967277473540619846559937299366273542567786213602002500000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (1532306976369858144448162211087988636348318900295431578974514341, 9789712495909684192577480819992162420784192820973276700250312500) e0 e36
  let e38 : LowMeanIntegerExpr := .atom (39, 1)
  let e39 : LowMeanIntegerExpr := .add (7, 1) e38 e5
  let e40 : LowMeanIntegerExpr := .mul (6181, 500000) e2 e39
  let e41 : LowMeanIntegerExpr := .add (7257, 62500) e1 e40
  let e42 : LowMeanIntegerExpr := .pow (49, 1) e39 2
  let e43 : LowMeanIntegerExpr := .mul (53263, 10000000) e9 e42
  let e44 : LowMeanIntegerExpr := .neg (-53263, 10000000) e43
  let e45 : LowMeanIntegerExpr := .add (1107857, 10000000) e41 e44
  let e46 : LowMeanIntegerExpr := .mul (747669, 16820000) e29 e38
  let e47 : LowMeanIntegerExpr := .add (1305542237, 8410000000) e45 e46
  let e48 : LowMeanIntegerExpr := .pow (1000000000000000000000000000000000000000, 1080244137479689290215446159447411025741704035417740877269) e21 39
  let e49 : LowMeanIntegerExpr := .mul (3743000000000000000000000000000000000000, 1080244137479689290215446159447411025741704035417740877269) e32 e48
  let e50 : LowMeanIntegerExpr := .neg (-3743000000000000000000000000000000000000, 1080244137479689290215446159447411025741704035417740877269) e49
  let e51 : LowMeanIntegerExpr := .add (1676937393283435275308187623017873572420081891309399113431763033, 10802441374796892902154461594474110257417040354177408772690000000) e47 e50
  let e52 : LowMeanIntegerExpr := .neg (-1676937393283435275308187623017873572420081891309399113431763033, 10802441374796892902154461594474110257417040354177408772690000000) e51
  let e53 : LowMeanIntegerExpr := .add (80527767723167527680749937459460552592765992296247247532666191, 62654159973821978832495877247949839493018834054228970881602000000) e37 e52
  e53

noncomputable def lowMeanSeedRecord0562 : LowMeanDirectSeedInput :=
  { record := 562, positions := [{ j := 23, mode := 0, left := 1097, right := 0 }, { j := 24, mode := 0, left := 1098, right := 0 }, { j := 25, mode := 0, left := 1099, right := 0 }, { j := 28, mode := 0, left := 1100, right := 0 }, { j := 29, mode := 0, left := 1101, right := 0 }, { j := 30, mode := 0, left := 1102, right := 0 }, { j := 31, mode := 0, left := 1103, right := 0 }, { j := 32, mode := 0, left := 1104, right := 0 }], target := { R := 40, expr := lowMeanSeedTargetExpr0562 } }

noncomputable def lowMeanSeedTargetExpr0563 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (83, 800)
  let e2 : LowMeanIntegerExpr := .atom (883, 500000)
  let e3 : LowMeanIntegerExpr := .atom (45, 1)
  let e4 : LowMeanIntegerExpr := .atom (32, 1)
  let e5 : LowMeanIntegerExpr := .neg (-32, 1) e4
  let e6 : LowMeanIntegerExpr := .add (13, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (11479, 500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (31677, 250000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1087, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (169, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (183703, 10000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-183703, 10000000) e11
  let e13 : LowMeanIntegerExpr := .add (1083377, 10000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (172539, 3364000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (1342467557, 8410000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (3743, 1000)
  let e33 : LowMeanIntegerExpr := .pow (1000000000000000000000000000000000000000000000, 642554405346449353654084490059204551183696882546282250934599990349) e21 45
  let e34 : LowMeanIntegerExpr := .mul (3743000000000000000000000000000000000000000000, 642554405346449353654084490059204551183696882546282250934599990349) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-3743000000000000000000000000000000000000000000, 642554405346449353654084490059204551183696882546282250934599990349) e34
  let e36 : LowMeanIntegerExpr := .add (1025693748852598813784481805518871723175813331914891168661870886820506073, 6425544053464493536540844900592045511836968825462822509345999903490000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (1025758004293133458719847213967877643630931701603145796886964346819540973, 6425544053464493536540844900592045511836968825462822509345999903490000000) e0 e36
  let e38 : LowMeanIntegerExpr := .atom (41, 1)
  let e39 : LowMeanIntegerExpr := .add (9, 1) e38 e5
  let e40 : LowMeanIntegerExpr := .mul (7947, 500000) e2 e39
  let e41 : LowMeanIntegerExpr := .add (29911, 250000) e1 e40
  let e42 : LowMeanIntegerExpr := .pow (81, 1) e39 2
  let e43 : LowMeanIntegerExpr := .mul (88047, 10000000) e9 e42
  let e44 : LowMeanIntegerExpr := .neg (-88047, 10000000) e43
  let e45 : LowMeanIntegerExpr := .add (1108393, 10000000) e41 e44
  let e46 : LowMeanIntegerExpr := .mul (786011, 16820000) e29 e38
  let e47 : LowMeanIntegerExpr := .add (1325164013, 8410000000) e45 e46
  let e48 : LowMeanIntegerExpr := .pow (100000000000000000000000000000000000000000, 908485319620418693071190220095272672648773093786320077783229) e21 41
  let e49 : LowMeanIntegerExpr := .mul (374300000000000000000000000000000000000000, 908485319620418693071190220095272672648773093786320077783229) e32 e48
  let e50 : LowMeanIntegerExpr := .neg (-374300000000000000000000000000000000000000, 908485319620418693071190220095272672648773093786320077783229) e49
  let e51 : LowMeanIntegerExpr := .add (1431500656242308762072022267238769057332322821032467632315928520497, 9084853196204186930711902200952726726487730937863200777832290000000) e47 e50
  let e52 : LowMeanIntegerExpr := .neg (-1431500656242308762072022267238769057332322821032467632315928520497, 9084853196204186930711902200952726726487730937863200777832290000000) e51
  let e53 : LowMeanIntegerExpr := .add (3321197161354268793196308193243456497967271105120264358730526728475579, 1606386013366123384135211225148011377959242206365705627336499975872500000) e37 e52
  e53

noncomputable def lowMeanSeedRecord0563 : LowMeanDirectSeedInput :=
  { record := 563, positions := [{ j := 24, mode := 0, left := 1105, right := 0 }, { j := 25, mode := 0, left := 1106, right := 0 }, { j := 26, mode := 0, left := 1107, right := 0 }, { j := 27, mode := 0, left := 1108, right := 0 }, { j := 30, mode := 0, left := 1109, right := 0 }, { j := 31, mode := 0, left := 1110, right := 0 }, { j := 32, mode := 0, left := 1111, right := 0 }, { j := 33, mode := 0, left := 1112, right := 0 }, { j := 34, mode := 0, left := 1113, right := 0 }], target := { R := 45, expr := lowMeanSeedTargetExpr0563 } }

noncomputable def lowMeanSeedGroup0560 : List LowMeanDirectSeedInput := [lowMeanSeedRecord0560, lowMeanSeedRecord0561, lowMeanSeedRecord0562, lowMeanSeedRecord0563]

end Erdos993Lean.Analytic.V213
