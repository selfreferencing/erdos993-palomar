module

public import Erdos993Lean.Analytic.V213.LowMeanCoreAll
public import Erdos993Lean.Analytic.V213.LowMeanData.Seed0064
public import Erdos993Lean.Analytic.V213.LowMeanFiberSeed
public import Erdos993Lean.Analytic.V213.LowMeanIntegerExpr
public import Erdos993Lean.Analytic.V213.LowMeanSeedGeometry
public import Erdos993Lean.Analytic.V213.LowMeanWidthData
public import Erdos993Lean.Ceiling.Prefix
public import Erdos993Lean.Ceiling.Statement

/-! Exact core/budget keys and equation-51 targets for the direct fibers. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanSeedTargetExpr0144 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (3029, 50000)
  let e2 : LowMeanIntegerExpr := .atom (9609, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (13, 1)
  let e4 : LowMeanIntegerExpr := .atom (31, 2)
  let e5 : LowMeanIntegerExpr := .neg (-31, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-5, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-9609, 4000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (232711, 4000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (6041, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (25, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (6041, 1600000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-6041, 1600000) e11
  let e13 : LowMeanIntegerExpr := .add (435217, 8000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (357, 25000)
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
  let e29 : LowMeanIntegerExpr := .mul (2737, 768000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (35581, 768000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (9670229, 96000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (977, 500)
  let e33 : LowMeanIntegerExpr := .pow (100000000000000000000000000, 341932896337114006995328418347) e21 13
  let e34 : LowMeanIntegerExpr := .mul (195400000000000000000000000, 341932896337114006995328418347) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-195400000000000000000000000, 341932896337114006995328418347) e34
  let e36 : LowMeanIntegerExpr := .add (3287811010213153646752427735623291463, 32825558048362944671551528161312000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (3288139265793637276199143250904904583, 32825558048362944671551528161312000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-3287811010213153646752427735623291463, 32825558048362944671551528161312000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0144 : LowMeanDirectSeedInput :=
  { record := 144, positions := [{ j := 4, mode := 0, left := 429, right := 0 }, { j := 8, mode := 0, left := 430, right := 0 }], target := { R := 13, expr := lowMeanSeedTargetExpr0144 } }

noncomputable def lowMeanSeedTargetExpr0145 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (3029, 50000)
  let e2 : LowMeanIntegerExpr := .atom (9609, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (14, 1)
  let e4 : LowMeanIntegerExpr := .atom (31, 2)
  let e5 : LowMeanIntegerExpr := .neg (-31, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-3, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-28827, 20000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (1182773, 20000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (6041, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (9, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (54369, 40000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-54369, 40000000) e11
  let e13 : LowMeanIntegerExpr := .add (2311177, 40000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (357, 25000)
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
  let e29 : LowMeanIntegerExpr := .mul (2737, 768000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (19159, 384000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (25841437, 240000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (977, 500)
  let e33 : LowMeanIntegerExpr := .pow (10000000000000000000000000000, 63941451615040319308126414230889) e21 14
  let e34 : LowMeanIntegerExpr := .mul (19540000000000000000000000000, 63941451615040319308126414230889) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-19540000000000000000000000000, 63941451615040319308126414230889) e34
  let e36 : LowMeanIntegerExpr := .add (1647649393598612663860832321383421547493, 15345948387609676633950339415413360000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (1647802853082488760627171824777575681093, 15345948387609676633950339415413360000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-1647649393598612663860832321383421547493, 15345948387609676633950339415413360000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0145 : LowMeanDirectSeedInput :=
  { record := 145, positions := [{ j := 4, mode := 0, left := 431, right := 0 }, { j := 8, mode := 0, left := 432, right := 0 }], target := { R := 14, expr := lowMeanSeedTargetExpr0145 } }

noncomputable def lowMeanSeedTargetExpr0146 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (3029, 50000)
  let e2 : LowMeanIntegerExpr := .atom (9609, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (15, 1)
  let e4 : LowMeanIntegerExpr := .atom (31, 2)
  let e5 : LowMeanIntegerExpr := .neg (-31, 2) e4
  let e6 : LowMeanIntegerExpr := .add (-1, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-9609, 20000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (1201991, 20000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (6041, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (1, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (6041, 40000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-6041, 40000000) e11
  let e13 : LowMeanIntegerExpr := .add (2397941, 40000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (357, 25000)
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
  let e29 : LowMeanIntegerExpr := .mul (2737, 768000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (2737, 51200) e29 e3
  let e31 : LowMeanIntegerExpr := .add (18144889, 160000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (977, 500)
  let e33 : LowMeanIntegerExpr := .pow (1000000000000000000000000000000, 11957051452012539710619639461176243) e21 15
  let e34 : LowMeanIntegerExpr := .mul (1954000000000000000000000000000, 11957051452012539710619639461176243) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1954000000000000000000000000000, 11957051452012539710619639461176243) e34
  let e36 : LowMeanIntegerExpr := .add (216646731364056359657285479243062738672027, 1913128232322006353699142313788198880000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (216665862646379579720822470666200620660827, 1913128232322006353699142313788198880000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-216646731364056359657285479243062738672027, 1913128232322006353699142313788198880000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0146 : LowMeanDirectSeedInput :=
  { record := 146, positions := [{ j := 5, mode := 0, left := 433, right := 0 }], target := { R := 15, expr := lowMeanSeedTargetExpr0146 } }

noncomputable def lowMeanSeedTargetExpr0147 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (3029, 50000)
  let e2 : LowMeanIntegerExpr := .atom (9609, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (16, 1)
  let e4 : LowMeanIntegerExpr := .atom (31, 2)
  let e5 : LowMeanIntegerExpr := .neg (-31, 2) e4
  let e6 : LowMeanIntegerExpr := .add (1, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (9609, 20000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (1221209, 20000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (6041, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (1, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (6041, 40000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-6041, 40000000) e11
  let e13 : LowMeanIntegerExpr := .add (2436377, 40000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (357, 25000)
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
  let e29 : LowMeanIntegerExpr := .mul (2737, 768000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (2737, 48000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (14151631, 120000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (977, 500)
  let e33 : LowMeanIntegerExpr := .pow (100000000000000000000000000000000, 2235968621526344925885872579239957441) e21 16
  let e34 : LowMeanIntegerExpr := .mul (195400000000000000000000000000000, 2235968621526344925885872579239957441) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-195400000000000000000000000000000, 2235968621526344925885872579239957441) e34
  let e36 : LowMeanIntegerExpr := .add (31619154859419490169859216854422138160736271, 268316234583161391106304709508794892920000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (31621838021765321783770279901517226109665471, 268316234583161391106304709508794892920000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-31619154859419490169859216854422138160736271, 268316234583161391106304709508794892920000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0147 : LowMeanDirectSeedInput :=
  { record := 147, positions := [{ j := 5, mode := 0, left := 434, right := 0 }, { j := 6, mode := 0, left := 435, right := 0 }, { j := 9, mode := 0, left := 436, right := 0 }], target := { R := 16, expr := lowMeanSeedTargetExpr0147 } }

noncomputable def lowMeanSeedTargetExpr0148 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (3029, 50000)
  let e2 : LowMeanIntegerExpr := .atom (9609, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (17, 1)
  let e4 : LowMeanIntegerExpr := .atom (31, 2)
  let e5 : LowMeanIntegerExpr := .neg (-31, 2) e4
  let e6 : LowMeanIntegerExpr := .add (3, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (28827, 20000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (1240427, 20000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (6041, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (9, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (54369, 40000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-54369, 40000000) e11
  let e13 : LowMeanIntegerExpr := .add (485297, 8000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (357, 25000)
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
  let e29 : LowMeanIntegerExpr := .mul (2737, 768000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (46529, 768000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (11639689, 96000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (977, 500)
  let e33 : LowMeanIntegerExpr := .pow (10000000000000000000000000000000000, 418126132225426501140658172317872041467) e21 17
  let e34 : LowMeanIntegerExpr := .mul (19540000000000000000000000000000000, 418126132225426501140658172317872041467) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-19540000000000000000000000000000000, 418126132225426501140658172317872041467) e34
  let e36 : LowMeanIntegerExpr := .add (4864982301876842365635406381088439704470983763, 40140108693640944109503184542515715980832000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (4865383702963778775076501412933864861630792083, 40140108693640944109503184542515715980832000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-4864982301876842365635406381088439704470983763, 40140108693640944109503184542515715980832000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0148 : LowMeanDirectSeedInput :=
  { record := 148, positions := [{ j := 6, mode := 0, left := 437, right := 0 }, { j := 9, mode := 0, left := 438, right := 0 }], target := { R := 17, expr := lowMeanSeedTargetExpr0148 } }

noncomputable def lowMeanSeedTargetExpr0149 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (3029, 50000)
  let e2 : LowMeanIntegerExpr := .atom (9609, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (18, 1)
  let e4 : LowMeanIntegerExpr := .atom (31, 2)
  let e5 : LowMeanIntegerExpr := .neg (-31, 2) e4
  let e6 : LowMeanIntegerExpr := .add (5, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (9609, 4000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (251929, 4000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (6041, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (25, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (6041, 1600000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-6041, 1600000) e11
  let e13 : LowMeanIntegerExpr := .add (473653, 8000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (357, 25000)
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
  let e29 : LowMeanIntegerExpr := .mul (2737, 768000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (8211, 128000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (1973681, 16000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (977, 500)
  let e33 : LowMeanIntegerExpr := .pow (1000000000000000000000000000000000000, 78189586726154755713303078223442071754329) e21 18
  let e34 : LowMeanIntegerExpr := .mul (1954000000000000000000000000000000000, 78189586726154755713303078223442071754329) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-1954000000000000000000000000000000000, 78189586726154755713303078223442071754329) e34
  let e36 : LowMeanIntegerExpr := .add (154290037719263844410987732731121371622155815049, 1251033387618476091412849251575073148069264000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (154302548053140029171901861223637122353636507689, 1251033387618476091412849251575073148069264000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-154290037719263844410987732731121371622155815049, 1251033387618476091412849251575073148069264000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0149 : LowMeanDirectSeedInput :=
  { record := 149, positions := [{ j := 6, mode := 0, left := 439, right := 0 }, { j := 7, mode := 0, left := 440, right := 0 }, { j := 9, mode := 0, left := 441, right := 0 }], target := { R := 18, expr := lowMeanSeedTargetExpr0149 } }

noncomputable def lowMeanSeedTargetExpr0150 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (3029, 50000)
  let e2 : LowMeanIntegerExpr := .atom (9609, 10000000)
  let e3 : LowMeanIntegerExpr := .atom (19, 1)
  let e4 : LowMeanIntegerExpr := .atom (31, 2)
  let e5 : LowMeanIntegerExpr := .neg (-31, 2) e4
  let e6 : LowMeanIntegerExpr := .add (7, 2) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (67263, 20000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (1278863, 20000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (6041, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (49, 4) e6 2
  let e11 : LowMeanIntegerExpr := .mul (296009, 40000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-296009, 40000000) e11
  let e13 : LowMeanIntegerExpr := .add (2261717, 40000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (357, 25000)
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
  let e29 : LowMeanIntegerExpr := .mul (2737, 768000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (52003, 768000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (59642479, 480000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (977, 500)
  let e33 : LowMeanIntegerExpr := .pow (100000000000000000000000000000000000000, 14621452717790939318387675627783667418059523) e21 19
  let e34 : LowMeanIntegerExpr := .mul (195400000000000000000000000000000000000, 14621452717790939318387675627783667418059523) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-195400000000000000000000000000000000000, 14621452717790939318387675627783667418059523) e34
  let e36 : LowMeanIntegerExpr := .add (871965894670339024687211257488899200524599321277517, 7018297304539650872826084301336160360668571040000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (872036077643384421195939518331912562128206006987917, 7018297304539650872826084301336160360668571040000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-871965894670339024687211257488899200524599321277517, 7018297304539650872826084301336160360668571040000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0150 : LowMeanDirectSeedInput :=
  { record := 150, positions := [{ j := 7, mode := 0, left := 442, right := 0 }, { j := 8, mode := 0, left := 443, right := 0 }, { j := 10, mode := 0, left := 444, right := 0 }], target := { R := 19, expr := lowMeanSeedTargetExpr0150 } }

noncomputable def lowMeanSeedTargetExpr0151 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (4227, 50000)
  let e2 : LowMeanIntegerExpr := .atom (-439, 250000)
  let e3 : LowMeanIntegerExpr := .atom (0, 1)
  let e4 : LowMeanIntegerExpr := .atom (35, 4)
  let e5 : LowMeanIntegerExpr := .neg (-35, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-35, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (3073, 200000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (19981, 200000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (127, 100000)
  let e10 : LowMeanIntegerExpr := .pow (1225, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (6223, 64000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-6223, 64000) e11
  let e13 : LowMeanIntegerExpr := .add (4273, 1600000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (0, 1) e29 e3
  let e31 : LowMeanIntegerExpr := .add (4273, 1600000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (126, 125)
  let e33 : LowMeanIntegerExpr := .pow (1, 1) e21 0
  let e34 : LowMeanIntegerExpr := .mul (126, 125) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-126, 125) e34
  let e36 : LowMeanIntegerExpr := .add (-1608527, 1600000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-1608511, 1600000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (1608527, 1600000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0151 : LowMeanDirectSeedInput :=
  { record := 151, positions := [], target := { R := 0, expr := lowMeanSeedTargetExpr0151 } }

noncomputable def lowMeanSeedTargetExpr0152 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (4227, 50000)
  let e2 : LowMeanIntegerExpr := .atom (-439, 250000)
  let e3 : LowMeanIntegerExpr := .atom (1, 1)
  let e4 : LowMeanIntegerExpr := .atom (35, 4)
  let e5 : LowMeanIntegerExpr := .neg (-35, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-31, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (13609, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (98149, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (127, 100000)
  let e10 : LowMeanIntegerExpr := .pow (961, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (122047, 1600000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-122047, 1600000) e11
  let e13 : LowMeanIntegerExpr := .add (174957, 8000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (1719, 50000)
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
  let e28 : LowMeanIntegerExpr := .mul (1719, 200000) e14 e27
  let e29 : LowMeanIntegerExpr := .mul (1719, 200000) e28 e3
  let e30 : LowMeanIntegerExpr := .add (243717, 8000000) e13 e29
  let e31 : LowMeanIntegerExpr := .atom (126, 125)
  let e32 : LowMeanIntegerExpr := .pow (25, 48) e20 1
  let e33 : LowMeanIntegerExpr := .mul (21, 40) e31 e32
  let e34 : LowMeanIntegerExpr := .neg (-21, 40) e33
  let e35 : LowMeanIntegerExpr := .add (-3956283, 8000000) e30 e34
  let e36 : LowMeanIntegerExpr := .add (-3956203, 8000000) e0 e35
  let e37 : LowMeanIntegerExpr := .neg (3956283, 8000000) e35
  let e38 : LowMeanIntegerExpr := .add (1, 100000) e36 e37
  e38

noncomputable def lowMeanSeedRecord0152 : LowMeanDirectSeedInput :=
  { record := 152, positions := [], target := { R := 1, expr := lowMeanSeedTargetExpr0152 } }

noncomputable def lowMeanSeedTargetExpr0153 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (4227, 50000)
  let e2 : LowMeanIntegerExpr := .atom (-439, 250000)
  let e3 : LowMeanIntegerExpr := .atom (2, 1)
  let e4 : LowMeanIntegerExpr := .atom (35, 4)
  let e5 : LowMeanIntegerExpr := .neg (-35, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-27, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (11853, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (96393, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (127, 100000)
  let e10 : LowMeanIntegerExpr := .pow (729, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (92583, 1600000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-92583, 1600000) e11
  let e13 : LowMeanIntegerExpr := .add (308229, 8000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (1719, 100000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (445749, 8000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (126, 125)
  let e33 : LowMeanIntegerExpr := .pow (625, 2304) e21 2
  let e34 : LowMeanIntegerExpr := .mul (35, 128) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-35, 128) e34
  let e36 : LowMeanIntegerExpr := .add (-1741751, 8000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-1741671, 8000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (1741751, 8000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0153 : LowMeanDirectSeedInput :=
  { record := 153, positions := [], target := { R := 2, expr := lowMeanSeedTargetExpr0153 } }

noncomputable def lowMeanSeedTargetExpr0154 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (4227, 50000)
  let e2 : LowMeanIntegerExpr := .atom (-439, 250000)
  let e3 : LowMeanIntegerExpr := .atom (3, 1)
  let e4 : LowMeanIntegerExpr := .atom (35, 4)
  let e5 : LowMeanIntegerExpr := .neg (-35, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-23, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (10097, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (94637, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (127, 100000)
  let e10 : LowMeanIntegerExpr := .pow (529, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (67183, 1600000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-67183, 1600000) e11
  let e13 : LowMeanIntegerExpr := .add (421181, 8000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (5157, 200000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (627461, 8000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (126, 125)
  let e33 : LowMeanIntegerExpr := .pow (15625, 110592) e21 3
  let e34 : LowMeanIntegerExpr := .mul (875, 6144) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-875, 6144) e34
  let e36 : LowMeanIntegerExpr := .add (-6142343, 96000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-6141383, 96000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (6142343, 96000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0154 : LowMeanDirectSeedInput :=
  { record := 154, positions := [{ j := 0, mode := 0, left := 445, right := 0 }, { j := 3, mode := 0, left := 446, right := 0 }], target := { R := 3, expr := lowMeanSeedTargetExpr0154 } }

noncomputable def lowMeanSeedTargetExpr0155 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (4227, 50000)
  let e2 : LowMeanIntegerExpr := .atom (-439, 250000)
  let e3 : LowMeanIntegerExpr := .atom (4, 1)
  let e4 : LowMeanIntegerExpr := .atom (35, 4)
  let e5 : LowMeanIntegerExpr := .neg (-35, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-19, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (8341, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (92881, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (127, 100000)
  let e10 : LowMeanIntegerExpr := .pow (361, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (45847, 1600000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-45847, 1600000) e11
  let e13 : LowMeanIntegerExpr := .add (513813, 8000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (1719, 50000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (788853, 8000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (126, 125)
  let e33 : LowMeanIntegerExpr := .pow (390625, 5308416) e21 4
  let e34 : LowMeanIntegerExpr := .mul (21875, 294912) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-21875, 294912) e34
  let e36 : LowMeanIntegerExpr := .add (112582453, 4608000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (112628533, 4608000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-112582453, 4608000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0155 : LowMeanDirectSeedInput :=
  { record := 155, positions := [{ j := 0, mode := 0, left := 447, right := 0 }, { j := 4, mode := 0, left := 448, right := 0 }], target := { R := 4, expr := lowMeanSeedTargetExpr0155 } }

noncomputable def lowMeanSeedTargetExpr0156 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (4227, 50000)
  let e2 : LowMeanIntegerExpr := .atom (-439, 250000)
  let e3 : LowMeanIntegerExpr := .atom (5, 1)
  let e4 : LowMeanIntegerExpr := .atom (35, 4)
  let e5 : LowMeanIntegerExpr := .neg (-35, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-15, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (1317, 200000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (729, 8000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (127, 100000)
  let e10 : LowMeanIntegerExpr := .pow (225, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1143, 64000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1143, 64000) e11
  let e13 : LowMeanIntegerExpr := .add (4689, 64000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (1719, 40000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (37197, 320000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (126, 125)
  let e33 : LowMeanIntegerExpr := .pow (9765625, 254803968) e21 5
  let e34 : LowMeanIntegerExpr := .mul (546875, 14155776) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-546875, 14155776) e34
  let e36 : LowMeanIntegerExpr := .add (686625781, 8847360000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (3433571273, 44236800000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-686625781, 8847360000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0156 : LowMeanDirectSeedInput :=
  { record := 156, positions := [{ j := 1, mode := 0, left := 449, right := 0 }, { j := 4, mode := 0, left := 450, right := 0 }], target := { R := 5, expr := lowMeanSeedTargetExpr0156 } }

noncomputable def lowMeanSeedTargetExpr0157 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (4227, 50000)
  let e2 : LowMeanIntegerExpr := .atom (-439, 250000)
  let e3 : LowMeanIntegerExpr := .atom (6, 1)
  let e4 : LowMeanIntegerExpr := .atom (35, 4)
  let e5 : LowMeanIntegerExpr := .neg (-35, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-11, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (4829, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (89369, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (127, 100000)
  let e10 : LowMeanIntegerExpr := .pow (121, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (15367, 1600000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-15367, 1600000) e11
  let e13 : LowMeanIntegerExpr := .add (638117, 8000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (5157, 100000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (1050677, 8000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (126, 125)
  let e33 : LowMeanIntegerExpr := .pow (244140625, 12230590464) e21 6
  let e34 : LowMeanIntegerExpr := .mul (13671875, 679477248) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-13671875, 679477248) e34
  let e36 : LowMeanIntegerExpr := .add (1180734602533, 10616832000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (1180840770853, 10616832000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-1180734602533, 10616832000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0157 : LowMeanDirectSeedInput :=
  { record := 157, positions := [{ j := 1, mode := 0, left := 451, right := 0 }, { j := 5, mode := 0, left := 452, right := 0 }], target := { R := 6, expr := lowMeanSeedTargetExpr0157 } }

noncomputable def lowMeanSeedTargetExpr0158 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (4227, 50000)
  let e2 : LowMeanIntegerExpr := .atom (-439, 250000)
  let e3 : LowMeanIntegerExpr := .atom (7, 1)
  let e4 : LowMeanIntegerExpr := .atom (35, 4)
  let e5 : LowMeanIntegerExpr := .neg (-35, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-7, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (3073, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (87613, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (127, 100000)
  let e10 : LowMeanIntegerExpr := .pow (49, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (6223, 1600000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-6223, 1600000) e11
  let e13 : LowMeanIntegerExpr := .add (669789, 8000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (12033, 200000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (1151109, 8000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (126, 125)
  let e33 : LowMeanIntegerExpr := .pow (6103515625, 587068342272) e21 7
  let e34 : LowMeanIntegerExpr := .mul (341796875, 32614907904) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-341796875, 32614907904) e34
  let e36 : LowMeanIntegerExpr := .add (67986209028253, 509607936000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (67991305107613, 509607936000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-67986209028253, 509607936000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0158 : LowMeanDirectSeedInput :=
  { record := 158, positions := [{ j := 2, mode := 0, left := 453, right := 0 }, { j := 5, mode := 1, left := 454, right := 455 }], target := { R := 7, expr := lowMeanSeedTargetExpr0158 } }

noncomputable def lowMeanSeedTargetExpr0159 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (4227, 50000)
  let e2 : LowMeanIntegerExpr := .atom (-439, 250000)
  let e3 : LowMeanIntegerExpr := .atom (8, 1)
  let e4 : LowMeanIntegerExpr := .atom (35, 4)
  let e5 : LowMeanIntegerExpr := .neg (-35, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-3, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (1317, 1000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (85857, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (127, 100000)
  let e10 : LowMeanIntegerExpr := .pow (9, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1143, 1600000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1143, 1600000) e11
  let e13 : LowMeanIntegerExpr := .add (681141, 8000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (1719, 25000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (1231221, 8000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (126, 125)
  let e33 : LowMeanIntegerExpr := .pow (152587890625, 28179280429056) e21 8
  let e34 : LowMeanIntegerExpr := .mul (8544921875, 1565515579392) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-8544921875, 1565515579392) e34
  let e36 : LowMeanIntegerExpr := .add (3631125551122261, 24461180928000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (3631370162931541, 24461180928000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-3631125551122261, 24461180928000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0159 : LowMeanDirectSeedInput :=
  { record := 159, positions := [{ j := 2, mode := 0, left := 456, right := 0 }, { j := 3, mode := 0, left := 457, right := 0 }, { j := 5, mode := 0, left := 458, right := 0 }, { j := 6, mode := 0, left := 459, right := 0 }], target := { R := 8, expr := lowMeanSeedTargetExpr0159 } }

noncomputable def lowMeanSeedGroup0144 : List LowMeanDirectSeedInput := [lowMeanSeedRecord0144, lowMeanSeedRecord0145, lowMeanSeedRecord0146, lowMeanSeedRecord0147, lowMeanSeedRecord0148, lowMeanSeedRecord0149, lowMeanSeedRecord0150, lowMeanSeedRecord0151, lowMeanSeedRecord0152, lowMeanSeedRecord0153, lowMeanSeedRecord0154, lowMeanSeedRecord0155, lowMeanSeedRecord0156, lowMeanSeedRecord0157, lowMeanSeedRecord0158, lowMeanSeedRecord0159]

end Erdos993Lean.Analytic.V213
