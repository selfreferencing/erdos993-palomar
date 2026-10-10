module

public import Erdos993Lean.Analytic.V213.LowMeanCoreAll
public import Erdos993Lean.Analytic.V213.LowMeanData.CoreBlock13
public import Erdos993Lean.Analytic.V213.LowMeanFiberSeed
public import Erdos993Lean.Analytic.V213.LowMeanIntegerExpr
public import Erdos993Lean.Analytic.V213.LowMeanSeedGeometry
public import Erdos993Lean.Analytic.V213.LowMeanWidthData
public import Erdos993Lean.Ceiling.Prefix
public import Erdos993Lean.Ceiling.Statement

/-! Exact core/budget keys and equation-51 targets for the direct fibers. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanSeedTargetExpr0032 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (9807, 125000)
  let e2 : LowMeanIntegerExpr := .atom (4183, 5000000)
  let e3 : LowMeanIntegerExpr := .atom (45, 1)
  let e4 : LowMeanIntegerExpr := .atom (121, 4)
  let e5 : LowMeanIntegerExpr := .neg (-121, 4) e4
  let e6 : LowMeanIntegerExpr := .add (59, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (246797, 20000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (1815917, 20000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (327, 6250000)
  let e10 : LowMeanIntegerExpr := .pow (3481, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1138287, 100000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1138287, 100000000) e11
  let e13 : LowMeanIntegerExpr := .add (3970649, 50000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (5511, 1000000)
  let e15 : LowMeanIntegerExpr := .atom (1, 4)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (3, 8)
  let e18 : LowMeanIntegerExpr := .atom (1, 1)
  let e19 : LowMeanIntegerExpr := .neg (-1, 4) e15
  let e20 : LowMeanIntegerExpr := .add (3, 4) e18 e19
  let e21 : LowMeanIntegerExpr := .mul (3, 16) e15 e20
  let e22 : LowMeanIntegerExpr := .neg (-3, 8) e17
  let e23 : LowMeanIntegerExpr := .add (5, 8) e18 e22
  let e24 : LowMeanIntegerExpr := .mul (15, 64) e17 e23
  let e25 : LowMeanIntegerExpr := .maximum (15, 64) e21 e24
  let e26 : LowMeanIntegerExpr := .selectLE (15, 64) e16 e17 e15 e25
  let e27 : LowMeanIntegerExpr := .selectLE (15, 64) e15 e16 e26 e25
  let e28 : LowMeanIntegerExpr := .mul (16533, 12800000) e14 e27
  let e29 : LowMeanIntegerExpr := .mul (148797, 2560000) e28 e3
  let e30 : LowMeanIntegerExpr := .add (220058893, 1600000000) e13 e29
  let e31 : LowMeanIntegerExpr := .atom (2461, 2500)
  let e32 : LowMeanIntegerExpr := .pow (2954312706550833698643, 1237940039285380274899124224) e20 45
  let e33 : LowMeanIntegerExpr := .mul (7270563570821601732360423, 3094850098213450687247810560000) e31 e32
  let e34 : LowMeanIntegerExpr := .neg (-7270563570821601732360423, 3094850098213450687247810560000) e33
  let e35 : LowMeanIntegerExpr := .add (266030333481281219290261965558793, 1934281311383406679529881600000000) e30 e34
  let e36 : LowMeanIntegerExpr := .add (266049676294395053357057264374793, 1934281311383406679529881600000000) e0 e35
  let e37 : LowMeanIntegerExpr := .atom (44, 1)
  let e38 : LowMeanIntegerExpr := .add (55, 4) e37 e5
  let e39 : LowMeanIntegerExpr := .mul (46013, 4000000) e2 e38
  let e40 : LowMeanIntegerExpr := .add (359837, 4000000) e1 e39
  let e41 : LowMeanIntegerExpr := .pow (3025, 16) e38 2
  let e42 : LowMeanIntegerExpr := .mul (39567, 4000000) e9 e41
  let e43 : LowMeanIntegerExpr := .neg (-39567, 4000000) e42
  let e44 : LowMeanIntegerExpr := .add (32027, 400000) e40 e43
  let e45 : LowMeanIntegerExpr := .mul (181863, 3200000) e28 e37
  let e46 : LowMeanIntegerExpr := .add (438079, 3200000) e44 e45
  let e47 : LowMeanIntegerExpr := .pow (984770902183611232881, 309485009821345068724781056) e20 44
  let e48 : LowMeanIntegerExpr := .mul (2423521190273867244120141, 773712524553362671811952640000) e31 e47
  let e49 : LowMeanIntegerExpr := .neg (-2423521190273867244120141, 773712524553362671811952640000) e48
  let e50 : LowMeanIntegerExpr := .add (529592896525005764889886275199, 3868562622766813359059763200000) e46 e49
  let e51 : LowMeanIntegerExpr := .neg (-529592896525005764889886275199, 3868562622766813359059763200000) e50
  let e52 : LowMeanIntegerExpr := .add (1253228031892170912114126775293, 1934281311383406679529881600000000) e36 e51
  e52

noncomputable def lowMeanSeedRecord0032 : LowMeanDirectSeedInput :=
  { record := 32, positions := [{ j := 6, mode := 0, left := 204, right := 0 }, { j := 7, mode := 0, left := 205, right := 0 }, { j := 8, mode := 0, left := 206, right := 0 }, { j := 9, mode := 0, left := 207, right := 0 }, { j := 10, mode := 1, left := 208, right := 209 }, { j := 11, mode := 1, left := 210, right := 211 }, { j := 12, mode := 1, left := 212, right := 213 }, { j := 13, mode := 1, left := 214, right := 215 }, { j := 14, mode := 1, left := 216, right := 217 }, { j := 15, mode := 0, left := 218, right := 0 }, { j := 16, mode := 0, left := 219, right := 0 }, { j := 17, mode := 0, left := 220, right := 0 }, { j := 18, mode := 0, left := 221, right := 0 }, { j := 19, mode := 0, left := 222, right := 0 }], target := { R := 45, expr := lowMeanSeedTargetExpr0032 } }

noncomputable def lowMeanSeedTargetExpr0033 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (9807, 125000)
  let e2 : LowMeanIntegerExpr := .atom (4183, 5000000)
  let e3 : LowMeanIntegerExpr := .atom (47, 1)
  let e4 : LowMeanIntegerExpr := .atom (121, 4)
  let e5 : LowMeanIntegerExpr := .neg (-121, 4) e4
  let e6 : LowMeanIntegerExpr := .add (67, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (280261, 20000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (1849381, 20000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (327, 6250000)
  let e10 : LowMeanIntegerExpr := .pow (4489, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1467903, 100000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1467903, 100000000) e11
  let e13 : LowMeanIntegerExpr := .add (3889501, 50000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (5511, 1000000)
  let e15 : LowMeanIntegerExpr := .atom (1, 4)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (3, 8)
  let e18 : LowMeanIntegerExpr := .atom (1, 1)
  let e19 : LowMeanIntegerExpr := .neg (-1, 4) e15
  let e20 : LowMeanIntegerExpr := .add (3, 4) e18 e19
  let e21 : LowMeanIntegerExpr := .mul (3, 16) e15 e20
  let e22 : LowMeanIntegerExpr := .neg (-3, 8) e17
  let e23 : LowMeanIntegerExpr := .add (5, 8) e18 e22
  let e24 : LowMeanIntegerExpr := .mul (15, 64) e17 e23
  let e25 : LowMeanIntegerExpr := .maximum (15, 64) e21 e24
  let e26 : LowMeanIntegerExpr := .selectLE (15, 64) e16 e17 e15 e25
  let e27 : LowMeanIntegerExpr := .selectLE (15, 64) e15 e16 e26 e25
  let e28 : LowMeanIntegerExpr := .mul (16533, 12800000) e14 e27
  let e29 : LowMeanIntegerExpr := .mul (777051, 12800000) e28 e3
  let e30 : LowMeanIntegerExpr := .add (221595407, 1600000000) e13 e29
  let e31 : LowMeanIntegerExpr := .atom (2461, 2500)
  let e32 : LowMeanIntegerExpr := .pow (26588814358957503287787, 19807040628566084398385987584) e20 47
  let e33 : LowMeanIntegerExpr := .mul (65435072137394415591243807, 49517601571415210995964968960000) e31 e32
  let e34 : LowMeanIntegerExpr := .neg (-65435072137394415591243807, 49517601571415210995964968960000) e33
  let e35 : LowMeanIntegerExpr := .add (4286237647564911490459682290758737, 30948500982134506872478105600000000) e30 e34
  let e36 : LowMeanIntegerExpr := .add (4286547132574732835528407071814737, 30948500982134506872478105600000000) e0 e35
  let e37 : LowMeanIntegerExpr := .atom (46, 1)
  let e38 : LowMeanIntegerExpr := .add (63, 4) e37 e5
  let e39 : LowMeanIntegerExpr := .mul (263529, 20000000) e2 e38
  let e40 : LowMeanIntegerExpr := .add (1832649, 20000000) e1 e39
  let e41 : LowMeanIntegerExpr := .pow (3969, 16) e38 2
  let e42 : LowMeanIntegerExpr := .mul (1297863, 100000000) e9 e41
  let e43 : LowMeanIntegerExpr := .neg (-1297863, 100000000) e42
  let e44 : LowMeanIntegerExpr := .add (3932691, 50000000) e40 e43
  let e45 : LowMeanIntegerExpr := .mul (380259, 6400000) e28 e37
  let e46 : LowMeanIntegerExpr := .add (110455431, 800000000) e44 e45
  let e47 : LowMeanIntegerExpr := .pow (8862938119652501095929, 4951760157141521099596496896) e20 46
  let e48 : LowMeanIntegerExpr := .mul (21811690712464805197081269, 12379400392853802748991242240000) e31 e47
  let e49 : LowMeanIntegerExpr := .neg (-21811690712464805197081269, 12379400392853802748991242240000) e48
  let e50 : LowMeanIntegerExpr := .add (1068245747313801664675511571741723, 7737125245533626718119526400000000) e46 e49
  let e51 : LowMeanIntegerExpr := .neg (-1068245747313801664675511571741723, 7737125245533626718119526400000000) e50
  let e52 : LowMeanIntegerExpr := .add (2712828663905235365272156969569, 6189700196426901374495621120000000) e36 e51
  e52

noncomputable def lowMeanSeedRecord0033 : LowMeanDirectSeedInput :=
  { record := 33, positions := [{ j := 7, mode := 0, left := 223, right := 0 }, { j := 8, mode := 0, left := 224, right := 0 }, { j := 9, mode := 0, left := 225, right := 0 }, { j := 10, mode := 0, left := 226, right := 0 }, { j := 11, mode := 1, left := 227, right := 228 }, { j := 12, mode := 1, left := 229, right := 230 }, { j := 13, mode := 1, left := 231, right := 232 }, { j := 14, mode := 1, left := 233, right := 234 }, { j := 15, mode := 1, left := 235, right := 236 }, { j := 16, mode := 0, left := 237, right := 0 }, { j := 17, mode := 0, left := 238, right := 0 }, { j := 18, mode := 0, left := 239, right := 0 }, { j := 19, mode := 0, left := 240, right := 0 }], target := { R := 47, expr := lowMeanSeedTargetExpr0033 } }

noncomputable def lowMeanSeedTargetExpr0034 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (9807, 125000)
  let e2 : LowMeanIntegerExpr := .atom (4183, 5000000)
  let e3 : LowMeanIntegerExpr := .atom (51, 1)
  let e4 : LowMeanIntegerExpr := .atom (121, 4)
  let e5 : LowMeanIntegerExpr := .neg (-121, 4) e4
  let e6 : LowMeanIntegerExpr := .add (83, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (347189, 20000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (1916309, 20000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (327, 6250000)
  let e10 : LowMeanIntegerExpr := .pow (6889, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (2252703, 100000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-2252703, 100000000) e11
  let e13 : LowMeanIntegerExpr := .add (3664421, 50000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (5511, 1000000)
  let e15 : LowMeanIntegerExpr := .atom (1, 4)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (3, 8)
  let e18 : LowMeanIntegerExpr := .atom (1, 1)
  let e19 : LowMeanIntegerExpr := .neg (-1, 4) e15
  let e20 : LowMeanIntegerExpr := .add (3, 4) e18 e19
  let e21 : LowMeanIntegerExpr := .mul (3, 16) e15 e20
  let e22 : LowMeanIntegerExpr := .neg (-3, 8) e17
  let e23 : LowMeanIntegerExpr := .add (5, 8) e18 e22
  let e24 : LowMeanIntegerExpr := .mul (15, 64) e17 e23
  let e25 : LowMeanIntegerExpr := .maximum (15, 64) e21 e24
  let e26 : LowMeanIntegerExpr := .selectLE (15, 64) e16 e17 e15 e25
  let e27 : LowMeanIntegerExpr := .selectLE (15, 64) e15 e16 e26 e25
  let e28 : LowMeanIntegerExpr := .mul (16533, 12800000) e14 e27
  let e29 : LowMeanIntegerExpr := .mul (843183, 12800000) e28 e3
  let e30 : LowMeanIntegerExpr := .add (222659347, 1600000000) e13 e29
  let e31 : LowMeanIntegerExpr := .atom (2461, 2500)
  let e32 : LowMeanIntegerExpr := .pow (2153693963075557766310747, 5070602400912917605986812821504) e20 51
  let e33 : LowMeanIntegerExpr := .mul (5300240843128947662890748367, 12676506002282294014967032053760000) e31 e32
  let e34 : LowMeanIntegerExpr := .neg (-5300240843128947662890748367, 12676506002282294014967032053760000) e33
  let e35 : LowMeanIntegerExpr := .add (1102552370439221519030588655633157537, 7922816251426433759354395033600000000) e30 e34
  let e36 : LowMeanIntegerExpr := .add (1102631598601735783368182199583493537, 7922816251426433759354395033600000000) e0 e35
  let e37 : LowMeanIntegerExpr := .atom (48, 1)
  let e38 : LowMeanIntegerExpr := .add (71, 4) e37 e5
  let e39 : LowMeanIntegerExpr := .mul (296993, 20000000) e2 e38
  let e40 : LowMeanIntegerExpr := .add (1866113, 20000000) e1 e39
  let e41 : LowMeanIntegerExpr := .pow (5041, 16) e38 2
  let e42 : LowMeanIntegerExpr := .mul (1648407, 100000000) e9 e41
  let e43 : LowMeanIntegerExpr := .neg (-1648407, 100000000) e42
  let e44 : LowMeanIntegerExpr := .add (3841079, 50000000) e40 e43
  let e45 : LowMeanIntegerExpr := .mul (49599, 800000) e28 e37
  let e46 : LowMeanIntegerExpr := .add (13882033, 100000000) e44 e45
  let e47 : LowMeanIntegerExpr := .pow (79766443076872509863361, 79228162514264337593543950336) e20 48
  let e48 : LowMeanIntegerExpr := .mul (196305216412183246773731421, 198070406285660843983859875840000) e31 e47
  let e49 : LowMeanIntegerExpr := .neg (-196305216412183246773731421, 198070406285660843983859875840000) e48
  let e50 : LowMeanIntegerExpr := .add (17185001786620687779169480566529267, 123794003928538027489912422400000000) e46 e49
  let e51 : LowMeanIntegerExpr := .neg (-17185001786620687779169480566529267, 123794003928538027489912422400000000) e50
  let e52 : LowMeanIntegerExpr := .add (2791484258011765501335443325620449, 7922816251426433759354395033600000000) e36 e51
  e52

noncomputable def lowMeanSeedRecord0034 : LowMeanDirectSeedInput :=
  { record := 34, positions := [{ j := 7, mode := 0, left := 241, right := 0 }, { j := 8, mode := 0, left := 242, right := 0 }, { j := 9, mode := 0, left := 243, right := 0 }, { j := 10, mode := 0, left := 244, right := 0 }, { j := 11, mode := 1, left := 245, right := 246 }, { j := 12, mode := 1, left := 247, right := 248 }, { j := 13, mode := 1, left := 249, right := 250 }, { j := 14, mode := 1, left := 251, right := 252 }, { j := 15, mode := 1, left := 253, right := 254 }, { j := 16, mode := 1, left := 255, right := 256 }, { j := 17, mode := 0, left := 257, right := 0 }, { j := 18, mode := 0, left := 258, right := 0 }, { j := 19, mode := 0, left := 259, right := 0 }, { j := 20, mode := 0, left := 260, right := 0 }], target := { R := 51, expr := lowMeanSeedTargetExpr0034 } }

noncomputable def lowMeanSeedTargetExpr0035 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (9, 25)
  let e2 : LowMeanIntegerExpr := .atom (1837, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (0, 1)
  let e4 : LowMeanIntegerExpr := .atom (15, 1)
  let e5 : LowMeanIntegerExpr := .neg (-15, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-15, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-5511, 200000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (66489, 200000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (691, 500000)
  let e10 : LowMeanIntegerExpr := .pow (225, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (6219, 20000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-6219, 20000) e11
  let e13 : LowMeanIntegerExpr := .add (4299, 200000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (973, 12500)
  let e15 : LowMeanIntegerExpr := .atom (3, 8)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (39, 89)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-3, 8) e15
  let e21 : LowMeanIntegerExpr := .add (5, 8) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (15, 64) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-39, 89) e17
  let e24 : LowMeanIntegerExpr := .add (50, 89) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (1950, 7921) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (1950, 7921) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1950, 7921) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1950, 7921) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (37947, 1980250) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (0, 1) e29 e3
  let e31 : LowMeanIntegerExpr := .add (4299, 200000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (567, 100)
  let e33 : LowMeanIntegerExpr := .pow (1, 1) e21 0
  let e34 : LowMeanIntegerExpr := .mul (567, 100) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-567, 100) e34
  let e36 : LowMeanIntegerExpr := .add (-1129701, 200000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-1129699, 200000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (1129701, 200000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0035 : LowMeanDirectSeedInput :=
  { record := 35, positions := [], target := { R := 0, expr := lowMeanSeedTargetExpr0035 } }

noncomputable def lowMeanSeedTargetExpr0036 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (9, 25)
  let e2 : LowMeanIntegerExpr := .atom (1837, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (1, 1)
  let e4 : LowMeanIntegerExpr := .atom (15, 1)
  let e5 : LowMeanIntegerExpr := .neg (-15, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-14, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-12859, 500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (167141, 500000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (691, 500000)
  let e10 : LowMeanIntegerExpr := .pow (196, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (33859, 125000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-33859, 125000) e11
  let e13 : LowMeanIntegerExpr := .add (6341, 100000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (973, 12500)
  let e15 : LowMeanIntegerExpr := .atom (3, 8)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (39, 89)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .neg (-3, 8) e15
  let e20 : LowMeanIntegerExpr := .add (5, 8) e3 e19
  let e21 : LowMeanIntegerExpr := .mul (15, 64) e15 e20
  let e22 : LowMeanIntegerExpr := .neg (-39, 89) e17
  let e23 : LowMeanIntegerExpr := .add (50, 89) e3 e22
  let e24 : LowMeanIntegerExpr := .mul (1950, 7921) e17 e23
  let e25 : LowMeanIntegerExpr := .maximum (1950, 7921) e21 e24
  let e26 : LowMeanIntegerExpr := .selectLE (1950, 7921) e16 e17 e18 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1950, 7921) e15 e16 e26 e25
  let e28 : LowMeanIntegerExpr := .mul (37947, 1980250) e14 e27
  let e29 : LowMeanIntegerExpr := .mul (37947, 1980250) e28 e3
  let e30 : LowMeanIntegerExpr := .add (65405861, 792100000) e13 e29
  let e31 : LowMeanIntegerExpr := .atom (567, 100)
  let e32 : LowMeanIntegerExpr := .pow (5, 8) e20 1
  let e33 : LowMeanIntegerExpr := .mul (567, 160) e31 e32
  let e34 : LowMeanIntegerExpr := .neg (-567, 160) e33
  let e35 : LowMeanIntegerExpr := .add (-1370799257, 396050000) e30 e34
  let e36 : LowMeanIntegerExpr := .add (-2741590593, 792100000) e0 e35
  let e37 : LowMeanIntegerExpr := .neg (1370799257, 396050000) e35
  let e38 : LowMeanIntegerExpr := .add (1, 100000) e36 e37
  e38

noncomputable def lowMeanSeedRecord0036 : LowMeanDirectSeedInput :=
  { record := 36, positions := [], target := { R := 1, expr := lowMeanSeedTargetExpr0036 } }

noncomputable def lowMeanSeedTargetExpr0037 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (9, 25)
  let e2 : LowMeanIntegerExpr := .atom (1837, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (2, 1)
  let e4 : LowMeanIntegerExpr := .atom (15, 1)
  let e5 : LowMeanIntegerExpr := .neg (-15, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-13, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-23881, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (336119, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (691, 500000)
  let e10 : LowMeanIntegerExpr := .pow (169, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (116779, 500000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-116779, 500000) e11
  let e13 : LowMeanIntegerExpr := .add (102561, 1000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (973, 12500)
  let e15 : LowMeanIntegerExpr := .atom (3, 8)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (39, 89)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-3, 8) e15
  let e21 : LowMeanIntegerExpr := .add (5, 8) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (15, 64) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-39, 89) e17
  let e24 : LowMeanIntegerExpr := .add (50, 89) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (1950, 7921) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (1950, 7921) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1950, 7921) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1950, 7921) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (37947, 1980250) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (37947, 990125) e29 e3
  let e31 : LowMeanIntegerExpr := .add (1115961681, 7921000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (567, 100)
  let e33 : LowMeanIntegerExpr := .pow (25, 64) e21 2
  let e34 : LowMeanIntegerExpr := .mul (567, 256) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-567, 256) e34
  let e36 : LowMeanIntegerExpr := .add (-65711262651, 31684000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-65710945811, 31684000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (65711262651, 31684000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0037 : LowMeanDirectSeedInput :=
  { record := 37, positions := [], target := { R := 2, expr := lowMeanSeedTargetExpr0037 } }

noncomputable def lowMeanSeedTargetExpr0038 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (9, 25)
  let e2 : LowMeanIntegerExpr := .atom (1837, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (3, 1)
  let e4 : LowMeanIntegerExpr := .atom (15, 1)
  let e5 : LowMeanIntegerExpr := .neg (-15, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-12, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-5511, 250000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (84489, 250000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (691, 500000)
  let e10 : LowMeanIntegerExpr := .pow (144, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (6219, 31250) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-6219, 31250) e11
  let e13 : LowMeanIntegerExpr := .add (34737, 250000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (973, 12500)
  let e15 : LowMeanIntegerExpr := .atom (3, 8)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (39, 89)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-3, 8) e15
  let e21 : LowMeanIntegerExpr := .add (5, 8) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (15, 64) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-39, 89) e17
  let e24 : LowMeanIntegerExpr := .add (50, 89) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (1950, 7921) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (1950, 7921) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1950, 7921) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1950, 7921) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (37947, 1980250) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (113841, 1980250) e29 e3
  let e31 : LowMeanIntegerExpr := .add (388992777, 1980250000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (567, 100)
  let e33 : LowMeanIntegerExpr := .pow (125, 512) e21 3
  let e34 : LowMeanIntegerExpr := .mul (2835, 2048) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-2835, 2048) e34
  let e36 : LowMeanIntegerExpr := .add (-301084471419, 253472000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-301081936699, 253472000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (301084471419, 253472000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0038 : LowMeanDirectSeedInput :=
  { record := 38, positions := [], target := { R := 3, expr := lowMeanSeedTargetExpr0038 } }

noncomputable def lowMeanSeedTargetExpr0039 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (9, 25)
  let e2 : LowMeanIntegerExpr := .atom (1837, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (4, 1)
  let e4 : LowMeanIntegerExpr := .atom (15, 1)
  let e5 : LowMeanIntegerExpr := .neg (-15, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-11, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-20207, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (339793, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (691, 500000)
  let e10 : LowMeanIntegerExpr := .pow (121, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (83611, 500000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-83611, 500000) e11
  let e13 : LowMeanIntegerExpr := .add (172571, 1000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (973, 12500)
  let e15 : LowMeanIntegerExpr := .atom (3, 8)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (39, 89)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-3, 8) e15
  let e21 : LowMeanIntegerExpr := .add (5, 8) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (15, 64) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-39, 89) e17
  let e24 : LowMeanIntegerExpr := .add (50, 89) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (1950, 7921) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (1950, 7921) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1950, 7921) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1950, 7921) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (37947, 1980250) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (75894, 990125) e29 e3
  let e31 : LowMeanIntegerExpr := .add (1974086891, 7921000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (567, 100)
  let e33 : LowMeanIntegerExpr := .pow (625, 4096) e21 4
  let e34 : LowMeanIntegerExpr := .mul (14175, 16384) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-14175, 16384) e34
  let e36 : LowMeanIntegerExpr := .add (-1249011490279, 2027776000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-1248991212519, 2027776000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (1249011490279, 2027776000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0039 : LowMeanDirectSeedInput :=
  { record := 39, positions := [{ j := 3, mode := 0, left := 261, right := 0 }], target := { R := 4, expr := lowMeanSeedTargetExpr0039 } }

noncomputable def lowMeanSeedTargetExpr0040 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (9, 25)
  let e2 : LowMeanIntegerExpr := .atom (1837, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (5, 1)
  let e4 : LowMeanIntegerExpr := .atom (15, 1)
  let e5 : LowMeanIntegerExpr := .neg (-15, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-10, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1837, 100000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (34163, 100000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (691, 500000)
  let e10 : LowMeanIntegerExpr := .pow (100, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (691, 5000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-691, 5000) e11
  let e13 : LowMeanIntegerExpr := .add (20343, 100000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (973, 12500)
  let e15 : LowMeanIntegerExpr := .atom (3, 8)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (39, 89)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-3, 8) e15
  let e21 : LowMeanIntegerExpr := .add (5, 8) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (15, 64) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-39, 89) e17
  let e24 : LowMeanIntegerExpr := .add (50, 89) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (1950, 7921) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (1950, 7921) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1950, 7921) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1950, 7921) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (37947, 1980250) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (37947, 396050) e29 e3
  let e31 : LowMeanIntegerExpr := .add (237030903, 792100000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (567, 100)
  let e33 : LowMeanIntegerExpr := .pow (3125, 32768) e21 5
  let e34 : LowMeanIntegerExpr := .mul (70875, 131072) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-70875, 131072) e34
  let e36 : LowMeanIntegerExpr := .add (-783499155687, 3244441600000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-783466711271, 3244441600000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (783499155687, 3244441600000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0040 : LowMeanDirectSeedInput :=
  { record := 40, positions := [{ j := 4, mode := 0, left := 262, right := 0 }], target := { R := 5, expr := lowMeanSeedTargetExpr0040 } }

noncomputable def lowMeanSeedTargetExpr0041 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (9, 25)
  let e2 : LowMeanIntegerExpr := .atom (1837, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (6, 1)
  let e4 : LowMeanIntegerExpr := .atom (15, 1)
  let e5 : LowMeanIntegerExpr := .neg (-15, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-9, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-16533, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (343467, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (691, 500000)
  let e10 : LowMeanIntegerExpr := .pow (81, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (55971, 500000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-55971, 500000) e11
  let e13 : LowMeanIntegerExpr := .add (9261, 40000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (973, 12500)
  let e15 : LowMeanIntegerExpr := .atom (3, 8)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (39, 89)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-3, 8) e15
  let e21 : LowMeanIntegerExpr := .add (5, 8) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (15, 64) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-39, 89) e17
  let e24 : LowMeanIntegerExpr := .add (50, 89) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (1950, 7921) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (1950, 7921) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1950, 7921) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1950, 7921) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (37947, 1980250) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (113841, 990125) e29 e3
  let e31 : LowMeanIntegerExpr := .add (109785501, 316840000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (567, 100)
  let e33 : LowMeanIntegerExpr := .pow (15625, 262144) e21 6
  let e34 : LowMeanIntegerExpr := .mul (354375, 1048576) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-354375, 1048576) e34
  let e36 : LowMeanIntegerExpr := .add (44347914009, 5191106560000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (221999125373, 25955532800000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-44347914009, 5191106560000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0041 : LowMeanDirectSeedInput :=
  { record := 41, positions := [{ j := 4, mode := 0, left := 263, right := 0 }], target := { R := 6, expr := lowMeanSeedTargetExpr0041 } }

noncomputable def lowMeanSeedTargetExpr0042 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (9, 25)
  let e2 : LowMeanIntegerExpr := .atom (1837, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (7, 1)
  let e4 : LowMeanIntegerExpr := .atom (15, 1)
  let e5 : LowMeanIntegerExpr := .neg (-15, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-8, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1837, 125000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (43163, 125000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (691, 500000)
  let e10 : LowMeanIntegerExpr := .pow (64, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1382, 15625) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1382, 15625) e11
  let e13 : LowMeanIntegerExpr := .add (32107, 125000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (973, 12500)
  let e15 : LowMeanIntegerExpr := .atom (3, 8)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (39, 89)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-3, 8) e15
  let e21 : LowMeanIntegerExpr := .add (5, 8) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (15, 64) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-39, 89) e17
  let e24 : LowMeanIntegerExpr := .add (50, 89) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (1950, 7921) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (1950, 7921) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1950, 7921) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1950, 7921) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (37947, 1980250) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (265629, 1980250) e29 e3
  let e31 : LowMeanIntegerExpr := .add (387134047, 990125000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (567, 100)
  let e33 : LowMeanIntegerExpr := .pow (78125, 2097152) e21 7
  let e34 : LowMeanIntegerExpr := .mul (1771875, 8388608) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1771875, 8388608) e34
  let e36 : LowMeanIntegerExpr := .add (186642253670197, 1038221312000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (186652635883317, 1038221312000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-186642253670197, 1038221312000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0042 : LowMeanDirectSeedInput :=
  { record := 42, positions := [{ j := 0, mode := 0, left := 264, right := 0 }, { j := 5, mode := 0, left := 265, right := 0 }], target := { R := 7, expr := lowMeanSeedTargetExpr0042 } }

noncomputable def lowMeanSeedTargetExpr0043 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (9, 25)
  let e2 : LowMeanIntegerExpr := .atom (1837, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (8, 1)
  let e4 : LowMeanIntegerExpr := .atom (15, 1)
  let e5 : LowMeanIntegerExpr := .neg (-15, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-7, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-12859, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (347141, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (691, 500000)
  let e10 : LowMeanIntegerExpr := .pow (49, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (33859, 500000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-33859, 500000) e11
  let e13 : LowMeanIntegerExpr := .add (279423, 1000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (973, 12500)
  let e15 : LowMeanIntegerExpr := .atom (3, 8)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (39, 89)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-3, 8) e15
  let e21 : LowMeanIntegerExpr := .add (5, 8) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (15, 64) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-39, 89) e17
  let e24 : LowMeanIntegerExpr := .add (50, 89) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (1950, 7921) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (1950, 7921) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1950, 7921) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1950, 7921) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (37947, 1980250) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (151788, 990125) e29 e3
  let e31 : LowMeanIntegerExpr := .add (3427613583, 7921000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (567, 100)
  let e33 : LowMeanIntegerExpr := .pow (390625, 16777216) e21 8
  let e34 : LowMeanIntegerExpr := .mul (8859375, 67108864) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-8859375, 67108864) e34
  let e36 : LowMeanIntegerExpr := .add (2497627256423433, 8305770496000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (2497710314128393, 8305770496000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-2497627256423433, 8305770496000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0043 : LowMeanDirectSeedInput :=
  { record := 43, positions := [{ j := 0, mode := 0, left := 266, right := 0 }, { j := 1, mode := 0, left := 267, right := 0 }, { j := 5, mode := 0, left := 268, right := 0 }], target := { R := 8, expr := lowMeanSeedTargetExpr0043 } }

noncomputable def lowMeanSeedTargetExpr0044 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (9, 25)
  let e2 : LowMeanIntegerExpr := .atom (1837, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (9, 1)
  let e4 : LowMeanIntegerExpr := .atom (15, 1)
  let e5 : LowMeanIntegerExpr := .neg (-15, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-6, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-5511, 500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (174489, 500000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (691, 500000)
  let e10 : LowMeanIntegerExpr := .pow (36, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (6219, 125000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-6219, 125000) e11
  let e13 : LowMeanIntegerExpr := .add (149613, 500000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (973, 12500)
  let e15 : LowMeanIntegerExpr := .atom (3, 8)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (39, 89)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-3, 8) e15
  let e21 : LowMeanIntegerExpr := .add (5, 8) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (15, 64) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-39, 89) e17
  let e24 : LowMeanIntegerExpr := .add (50, 89) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (1950, 7921) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (1950, 7921) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1950, 7921) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1950, 7921) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (37947, 1980250) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (341523, 1980250) e29 e3
  let e31 : LowMeanIntegerExpr := .add (1868130573, 3960500000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (567, 100)
  let e33 : LowMeanIntegerExpr := .pow (1953125, 134217728) e21 9
  let e34 : LowMeanIntegerExpr := .mul (44296875, 536870912) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-44296875, 536870912) e34
  let e36 : LowMeanIntegerExpr := .add (25859599719502893, 66446163968000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (25860264181142573, 66446163968000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-25859599719502893, 66446163968000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0044 : LowMeanDirectSeedInput :=
  { record := 44, positions := [{ j := 0, mode := 0, left := 269, right := 0 }, { j := 1, mode := 0, left := 270, right := 0 }], target := { R := 9, expr := lowMeanSeedTargetExpr0044 } }

noncomputable def lowMeanSeedTargetExpr0045 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (9, 25)
  let e2 : LowMeanIntegerExpr := .atom (1837, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (10, 1)
  let e4 : LowMeanIntegerExpr := .atom (15, 1)
  let e5 : LowMeanIntegerExpr := .neg (-15, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-5, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1837, 200000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (70163, 200000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (691, 500000)
  let e10 : LowMeanIntegerExpr := .pow (25, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (691, 20000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-691, 20000) e11
  let e13 : LowMeanIntegerExpr := .add (63253, 200000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (973, 12500)
  let e15 : LowMeanIntegerExpr := .atom (3, 8)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (39, 89)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-3, 8) e15
  let e21 : LowMeanIntegerExpr := .add (5, 8) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (15, 64) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-39, 89) e17
  let e24 : LowMeanIntegerExpr := .add (50, 89) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (1950, 7921) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (1950, 7921) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1950, 7921) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1950, 7921) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (37947, 1980250) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (37947, 198025) e29 e3
  let e31 : LowMeanIntegerExpr := .add (804603013, 1584200000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (567, 100)
  let e33 : LowMeanIntegerExpr := .pow (9765625, 1073741824) e21 10
  let e34 : LowMeanIntegerExpr := .mul (221484375, 4294967296) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-221484375, 4294967296) e34
  let e36 : LowMeanIntegerExpr := .add (48513563753485357, 106313862348800000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (9702925378421769, 21262772469760000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-48513563753485357, 106313862348800000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0045 : LowMeanDirectSeedInput :=
  { record := 45, positions := [{ j := 1, mode := 0, left := 271, right := 0 }, { j := 2, mode := 0, left := 272, right := 0 }, { j := 6, mode := 0, left := 273, right := 0 }], target := { R := 10, expr := lowMeanSeedTargetExpr0045 } }

noncomputable def lowMeanSeedTargetExpr0046 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (9, 25)
  let e2 : LowMeanIntegerExpr := .atom (1837, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (11, 1)
  let e4 : LowMeanIntegerExpr := .atom (15, 1)
  let e5 : LowMeanIntegerExpr := .neg (-15, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-4, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1837, 250000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (88163, 250000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (691, 500000)
  let e10 : LowMeanIntegerExpr := .pow (16, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (691, 31250) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-691, 31250) e11
  let e13 : LowMeanIntegerExpr := .add (16527, 50000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (973, 12500)
  let e15 : LowMeanIntegerExpr := .atom (3, 8)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (39, 89)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-3, 8) e15
  let e21 : LowMeanIntegerExpr := .add (5, 8) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (15, 64) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-39, 89) e17
  let e24 : LowMeanIntegerExpr := .add (50, 89) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (1950, 7921) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (1950, 7921) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1950, 7921) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1950, 7921) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (37947, 1980250) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (417417, 1980250) e29 e3
  let e31 : LowMeanIntegerExpr := .add (214393767, 396050000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (567, 100)
  let e33 : LowMeanIntegerExpr := .pow (48828125, 8589934592) e21 11
  let e34 : LowMeanIntegerExpr := .mul (1107421875, 34359738368) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1107421875, 34359738368) e34
  let e36 : LowMeanIntegerExpr := .add (432994956766012641, 850510898790400000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (86600692375000109, 170102179758080000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-432994956766012641, 850510898790400000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0046 : LowMeanDirectSeedInput :=
  { record := 46, positions := [{ j := 1, mode := 0, left := 274, right := 0 }, { j := 2, mode := 0, left := 275, right := 0 }], target := { R := 11, expr := lowMeanSeedTargetExpr0046 } }

noncomputable def lowMeanSeedTargetExpr0047 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (9, 25)
  let e2 : LowMeanIntegerExpr := .atom (1837, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (12, 1)
  let e4 : LowMeanIntegerExpr := .atom (15, 1)
  let e5 : LowMeanIntegerExpr := .neg (-15, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-3, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-5511, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (354489, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (691, 500000)
  let e10 : LowMeanIntegerExpr := .pow (9, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (6219, 500000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-6219, 500000) e11
  let e13 : LowMeanIntegerExpr := .add (342051, 1000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (973, 12500)
  let e15 : LowMeanIntegerExpr := .atom (3, 8)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (39, 89)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-3, 8) e15
  let e21 : LowMeanIntegerExpr := .add (5, 8) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (15, 64) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-39, 89) e17
  let e24 : LowMeanIntegerExpr := .add (50, 89) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (1950, 7921) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (1950, 7921) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1950, 7921) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (1950, 7921) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (37947, 1980250) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (227682, 990125) e29 e3
  let e31 : LowMeanIntegerExpr := .add (4530841971, 7921000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (567, 100)
  let e33 : LowMeanIntegerExpr := .pow (244140625, 68719476736) e21 12
  let e34 : LowMeanIntegerExpr := .mul (5537109375, 274877906944) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-5537109375, 274877906944) e34
  let e36 : LowMeanIntegerExpr := .add (18774514286298946041, 34020435951616000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (18774854490658462201, 34020435951616000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-18774514286298946041, 34020435951616000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0047 : LowMeanDirectSeedInput :=
  { record := 47, positions := [{ j := 1, mode := 0, left := 276, right := 0 }, { j := 2, mode := 0, left := 277, right := 0 }, { j := 3, mode := 0, left := 278, right := 0 }], target := { R := 12, expr := lowMeanSeedTargetExpr0047 } }

noncomputable def lowMeanSeedGroup0032 : List LowMeanDirectSeedInput := [lowMeanSeedRecord0032, lowMeanSeedRecord0033, lowMeanSeedRecord0034, lowMeanSeedRecord0035, lowMeanSeedRecord0036, lowMeanSeedRecord0037, lowMeanSeedRecord0038, lowMeanSeedRecord0039, lowMeanSeedRecord0040, lowMeanSeedRecord0041, lowMeanSeedRecord0042, lowMeanSeedRecord0043, lowMeanSeedRecord0044, lowMeanSeedRecord0045, lowMeanSeedRecord0046, lowMeanSeedRecord0047]

end Erdos993Lean.Analytic.V213
