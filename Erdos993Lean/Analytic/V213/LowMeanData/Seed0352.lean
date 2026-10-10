module

public import Erdos993Lean.Analytic.V213.LowMeanCoreAll
public import Erdos993Lean.Analytic.V213.LowMeanData.Seed0256
public import Erdos993Lean.Analytic.V213.LowMeanFiberSeed
public import Erdos993Lean.Analytic.V213.LowMeanIntegerExpr
public import Erdos993Lean.Analytic.V213.LowMeanSeedGeometry
public import Erdos993Lean.Analytic.V213.LowMeanWidthData
public import Erdos993Lean.Ceiling.Prefix
public import Erdos993Lean.Ceiling.Statement

/-! Exact core/budget keys and equation-51 targets for the direct fibers. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanSeedTargetExpr0352 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (773, 40000)
  let e2 : LowMeanIntegerExpr := .atom (1543, 2500000)
  let e3 : LowMeanIntegerExpr := .atom (10, 1)
  let e4 : LowMeanIntegerExpr := .atom (23, 1)
  let e5 : LowMeanIntegerExpr := .neg (-23, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-13, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-20059, 2500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (56507, 5000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (81, 625000)
  let e10 : LowMeanIntegerExpr := .pow (169, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (13689, 625000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-13689, 625000) e11
  let e13 : LowMeanIntegerExpr := .add (-10601, 1000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (32549, 4410000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-1420141, 441000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1129, 125)
  let e33 : LowMeanIntegerExpr := .pow (10000000000, 16679880978201) e21 10
  let e34 : LowMeanIntegerExpr := .mul (90320000000, 16679880978201) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-90320000000, 16679880978201) e34
  let e36 : LowMeanIntegerExpr := .add (-144033793315789901, 16679880978201000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-143866994506007891, 16679880978201000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (144033793315789901, 16679880978201000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0352 : LowMeanDirectSeedInput :=
  { record := 352, positions := [{ j := 3, mode := 0, left := 760, right := 0 }, { j := 8, mode := 0, left := 761, right := 0 }, { j := 9, mode := 0, left := 762, right := 0 }], target := { R := 10, expr := lowMeanSeedTargetExpr0352 } }

noncomputable def lowMeanSeedTargetExpr0353 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (773, 40000)
  let e2 : LowMeanIntegerExpr := .atom (1543, 2500000)
  let e3 : LowMeanIntegerExpr := .atom (11, 1)
  let e4 : LowMeanIntegerExpr := .atom (23, 1)
  let e5 : LowMeanIntegerExpr := .neg (-23, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-12, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-4629, 625000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (59593, 5000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (81, 625000)
  let e10 : LowMeanIntegerExpr := .pow (144, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1458, 78125) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1458, 78125) e11
  let e13 : LowMeanIntegerExpr := .add (-33719, 5000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (358039, 44100000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (3031871, 2205000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1129, 125)
  let e33 : LowMeanIntegerExpr := .pow (100000000000, 350277500542221) e21 11
  let e34 : LowMeanIntegerExpr := .mul (903200000000, 350277500542221) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-903200000000, 350277500542221) e34
  let e36 : LowMeanIntegerExpr := .add (-2107845360892416949, 1751387502711105000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-2090331485865305899, 1751387502711105000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (2107845360892416949, 1751387502711105000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0353 : LowMeanDirectSeedInput :=
  { record := 353, positions := [{ j := 3, mode := 0, left := 763, right := 0 }, { j := 4, mode := 0, left := 764, right := 0 }, { j := 9, mode := 0, left := 765, right := 0 }], target := { R := 11, expr := lowMeanSeedTargetExpr0353 } }

noncomputable def lowMeanSeedTargetExpr0354 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (773, 40000)
  let e2 : LowMeanIntegerExpr := .atom (1543, 2500000)
  let e3 : LowMeanIntegerExpr := .atom (12, 1)
  let e4 : LowMeanIntegerExpr := .atom (23, 1)
  let e5 : LowMeanIntegerExpr := .neg (-23, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-11, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-16973, 2500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (62679, 5000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (81, 625000)
  let e10 : LowMeanIntegerExpr := .pow (121, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (9801, 625000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-9801, 625000) e11
  let e13 : LowMeanIntegerExpr := .add (-15729, 5000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (32549, 3675000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (4197637, 735000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1129, 125)
  let e33 : LowMeanIntegerExpr := .pow (1000000000000, 7355827511386641) e21 12
  let e34 : LowMeanIntegerExpr := .mul (9032000000000, 7355827511386641) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-9032000000000, 7355827511386641) e34
  let e36 : LowMeanIntegerExpr := .add (164888256649078133111, 36779137556933205000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (165256048024647465161, 36779137556933205000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-164888256649078133111, 36779137556933205000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0354 : LowMeanDirectSeedInput :=
  { record := 354, positions := [{ j := 4, mode := 0, left := 766, right := 0 }, { j := 10, mode := 0, left := 767, right := 0 }], target := { R := 12, expr := lowMeanSeedTargetExpr0354 } }

noncomputable def lowMeanSeedTargetExpr0355 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (773, 40000)
  let e2 : LowMeanIntegerExpr := .atom (1543, 2500000)
  let e3 : LowMeanIntegerExpr := .atom (13, 1)
  let e4 : LowMeanIntegerExpr := .atom (23, 1)
  let e5 : LowMeanIntegerExpr := .neg (-23, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-10, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1543, 250000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (13153, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (81, 625000)
  let e10 : LowMeanIntegerExpr := .pow (100, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (81, 6250) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-81, 6250) e11
  let e13 : LowMeanIntegerExpr := .add (193, 1000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (423137, 44100000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (4316483, 441000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1129, 125)
  let e33 : LowMeanIntegerExpr := .pow (10000000000000, 154472377739119461) e21 13
  let e34 : LowMeanIntegerExpr := .mul (90320000000000, 154472377739119461) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-90320000000000, 154472377739119461) e34
  let e36 : LowMeanIntegerExpr := .add (1421646876372987728743, 154472377739119461000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (1423191600150378923353, 154472377739119461000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-1421646876372987728743, 154472377739119461000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0355 : LowMeanDirectSeedInput :=
  { record := 355, positions := [{ j := 4, mode := 0, left := 768, right := 0 }, { j := 5, mode := 0, left := 769, right := 0 }, { j := 10, mode := 0, left := 770, right := 0 }, { j := 11, mode := 0, left := 771, right := 0 }], target := { R := 13, expr := lowMeanSeedTargetExpr0355 } }

noncomputable def lowMeanSeedTargetExpr0356 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (773, 40000)
  let e2 : LowMeanIntegerExpr := .atom (1543, 2500000)
  let e3 : LowMeanIntegerExpr := .atom (14, 1)
  let e4 : LowMeanIntegerExpr := .atom (23, 1)
  let e5 : LowMeanIntegerExpr := .neg (-23, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-9, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-13887, 2500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (68851, 5000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (81, 625000)
  let e10 : LowMeanIntegerExpr := .pow (81, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (6561, 625000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-6561, 625000) e11
  let e13 : LowMeanIntegerExpr := .add (16363, 5000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (32549, 3150000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (4285769, 315000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1129, 125)
  let e33 : LowMeanIntegerExpr := .pow (100000000000000, 3243919932521508681) e21 14
  let e34 : LowMeanIntegerExpr := .mul (903200000000000, 3243919932521508681) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-903200000000000, 3243919932521508681) e34
  let e36 : LowMeanIntegerExpr := .add (216161642623536091083503, 16219599662607543405000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (216323838620162166517553, 16219599662607543405000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-216161642623536091083503, 16219599662607543405000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0356 : LowMeanDirectSeedInput :=
  { record := 356, positions := [{ j := 5, mode := 0, left := 772, right := 0 }, { j := 11, mode := 0, left := 773, right := 0 }], target := { R := 14, expr := lowMeanSeedTargetExpr0356 } }

noncomputable def lowMeanSeedTargetExpr0357 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (773, 40000)
  let e2 : LowMeanIntegerExpr := .atom (1543, 2500000)
  let e3 : LowMeanIntegerExpr := .atom (15, 1)
  let e4 : LowMeanIntegerExpr := .atom (23, 1)
  let e5 : LowMeanIntegerExpr := .neg (-23, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-8, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1543, 312500) e2 e6
  let e8 : LowMeanIntegerExpr := .add (71937, 5000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (81, 625000)
  let e10 : LowMeanIntegerExpr := .pow (64, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (648, 78125) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-648, 78125) e11
  let e13 : LowMeanIntegerExpr := .add (6093, 1000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (32549, 2940000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (2523121, 147000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1129, 125)
  let e33 : LowMeanIntegerExpr := .pow (1000000000000000, 68122318582951682301) e21 15
  let e34 : LowMeanIntegerExpr := .mul (9032000000000000, 68122318582951682301) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-9032000000000000, 68122318582951682301) e34
  let e36 : LowMeanIntegerExpr := .add (1160225500580514500673343, 68122318582951682301000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (1160906723766344017496353, 68122318582951682301000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-1160225500580514500673343, 68122318582951682301000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0357 : LowMeanDirectSeedInput :=
  { record := 357, positions := [{ j := 5, mode := 0, left := 774, right := 0 }, { j := 6, mode := 0, left := 775, right := 0 }, { j := 11, mode := 0, left := 776, right := 0 }, { j := 12, mode := 0, left := 777, right := 0 }], target := { R := 15, expr := lowMeanSeedTargetExpr0357 } }

noncomputable def lowMeanSeedTargetExpr0358 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (773, 40000)
  let e2 : LowMeanIntegerExpr := .atom (1543, 2500000)
  let e3 : LowMeanIntegerExpr := .atom (16, 1)
  let e4 : LowMeanIntegerExpr := .atom (23, 1)
  let e5 : LowMeanIntegerExpr := .neg (-23, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-7, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-10801, 2500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (75023, 5000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (81, 625000)
  let e10 : LowMeanIntegerExpr := .pow (49, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (3969, 625000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-3969, 625000) e11
  let e13 : LowMeanIntegerExpr := .add (43271, 5000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (32549, 2756250) e29 e3
  let e31 : LowMeanIntegerExpr := .add (45121711, 2205000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1129, 125)
  let e33 : LowMeanIntegerExpr := .pow (10000000000000000, 1430568690241985328321) e21 16
  let e34 : LowMeanIntegerExpr := .mul (90320000000000000, 1430568690241985328321) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-90320000000000000, 1430568690241985328321) e34
  let e36 : LowMeanIntegerExpr := .add (145919617702375015988073191, 7152843451209926641605000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (145991146136887115254489241, 7152843451209926641605000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-145919617702375015988073191, 7152843451209926641605000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0358 : LowMeanDirectSeedInput :=
  { record := 358, positions := [{ j := 6, mode := 0, left := 778, right := 0 }, { j := 12, mode := 0, left := 779, right := 0 }], target := { R := 16, expr := lowMeanSeedTargetExpr0358 } }

noncomputable def lowMeanSeedTargetExpr0359 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (773, 40000)
  let e2 : LowMeanIntegerExpr := .atom (1543, 2500000)
  let e3 : LowMeanIntegerExpr := .atom (17, 1)
  let e4 : LowMeanIntegerExpr := .atom (23, 1)
  let e5 : LowMeanIntegerExpr := .neg (-23, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-6, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-4629, 1250000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (78109, 5000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (81, 625000)
  let e10 : LowMeanIntegerExpr := .pow (36, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (729, 156250) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-729, 156250) e11
  let e13 : LowMeanIntegerExpr := .add (54781, 5000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (553333, 44100000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (51825071, 2205000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1129, 125)
  let e33 : LowMeanIntegerExpr := .pow (100000000000000000, 30041942495081691894741) e21 17
  let e34 : LowMeanIntegerExpr := .mul (903200000000000000, 30041942495081691894741) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-903200000000000000, 30041942495081691894741) e34
  let e36 : LowMeanIntegerExpr := .add (3525927997246090324818768371, 150209712475408459473705000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (3527430094370844409413505421, 150209712475408459473705000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-3525927997246090324818768371, 150209712475408459473705000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0359 : LowMeanDirectSeedInput :=
  { record := 359, positions := [{ j := 6, mode := 0, left := 780, right := 0 }, { j := 7, mode := 0, left := 781, right := 0 }, { j := 12, mode := 0, left := 782, right := 0 }, { j := 13, mode := 0, left := 783, right := 0 }], target := { R := 17, expr := lowMeanSeedTargetExpr0359 } }

noncomputable def lowMeanSeedTargetExpr0360 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (773, 40000)
  let e2 : LowMeanIntegerExpr := .atom (1543, 2500000)
  let e3 : LowMeanIntegerExpr := .atom (18, 1)
  let e4 : LowMeanIntegerExpr := .atom (23, 1)
  let e5 : LowMeanIntegerExpr := .neg (-23, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-5, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1543, 500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (16239, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (81, 625000)
  let e10 : LowMeanIntegerExpr := .pow (25, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (81, 25000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-81, 25000) e11
  let e13 : LowMeanIntegerExpr := .add (12999, 1000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (32549, 2450000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (1287931, 49000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1129, 125)
  let e33 : LowMeanIntegerExpr := .pow (1000000000000000000, 630880792396715529789561) e21 18
  let e34 : LowMeanIntegerExpr := .mul (9032000000000000000, 630880792396715529789561) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-9032000000000000000, 630880792396715529789561) e34
  let e36 : LowMeanIntegerExpr := .add (16573231874128453653008144659, 630880792396715529789561000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (16579540682052420808306040269, 630880792396715529789561000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-16573231874128453653008144659, 630880792396715529789561000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0360 : LowMeanDirectSeedInput :=
  { record := 360, positions := [{ j := 7, mode := 0, left := 784, right := 0 }, { j := 13, mode := 0, left := 785, right := 0 }, { j := 14, mode := 0, left := 786, right := 0 }], target := { R := 18, expr := lowMeanSeedTargetExpr0360 } }

noncomputable def lowMeanSeedTargetExpr0361 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (773, 40000)
  let e2 : LowMeanIntegerExpr := .atom (1543, 2500000)
  let e3 : LowMeanIntegerExpr := .atom (20, 1)
  let e4 : LowMeanIntegerExpr := .atom (23, 1)
  let e5 : LowMeanIntegerExpr := .neg (-23, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-3, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-4629, 2500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (87367, 5000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (81, 625000)
  let e10 : LowMeanIntegerExpr := .pow (9, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (729, 625000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-729, 625000) e11
  let e13 : LowMeanIntegerExpr := .add (16307, 1000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (32549, 2205000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (13701187, 441000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1129, 125)
  let e33 : LowMeanIntegerExpr := .pow (100000000000000000000, 278218429446951548637196401) e21 20
  let e34 : LowMeanIntegerExpr := .mul (903200000000000000000, 278218429446951548637196401) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-903200000000000000000, 278218429446951548637196401) e34
  let e36 : LowMeanIntegerExpr := .add (8642912511335577659450845908907, 278218429446951548637196401000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (8645694695630047174937217872917, 278218429446951548637196401000000) e0 e36
  let e38 : LowMeanIntegerExpr := .atom (19, 1)
  let e39 : LowMeanIntegerExpr := .add (-4, 1) e38 e5
  let e40 : LowMeanIntegerExpr := .mul (-1543, 625000) e2 e39
  let e41 : LowMeanIntegerExpr := .add (84281, 5000000) e1 e40
  let e42 : LowMeanIntegerExpr := .pow (16, 1) e39 2
  let e43 : LowMeanIntegerExpr := .mul (162, 78125) e9 e42
  let e44 : LowMeanIntegerExpr := .neg (-162, 78125) e43
  let e45 : LowMeanIntegerExpr := .add (73913, 5000000) e41 e44
  let e46 : LowMeanIntegerExpr := .mul (618431, 44100000) e29 e38
  let e47 : LowMeanIntegerExpr := .add (63517183, 2205000000) e45 e46
  let e48 : LowMeanIntegerExpr := .pow (10000000000000000000, 13248496640331026125580781) e21 19
  let e49 : LowMeanIntegerExpr := .mul (90320000000000000000, 13248496640331026125580781) e32 e48
  let e50 : LowMeanIntegerExpr := .neg (-90320000000000000000, 13248496640331026125580781) e49
  let e51 : LowMeanIntegerExpr := .add (1907727959135580424027880834603, 66242483201655130627903905000000) e47 e50
  let e52 : LowMeanIntegerExpr := .neg (-1907727959135580424027880834603, 66242483201655130627903905000000) e51
  let e53 : LowMeanIntegerExpr := .add (1583093168151523485050295918961, 695546073617378871592991002500000) e37 e52
  e53

noncomputable def lowMeanSeedRecord0361 : LowMeanDirectSeedInput :=
  { record := 361, positions := [{ j := 7, mode := 0, left := 787, right := 0 }, { j := 8, mode := 0, left := 788, right := 0 }, { j := 13, mode := 0, left := 789, right := 0 }, { j := 14, mode := 0, left := 790, right := 0 }], target := { R := 20, expr := lowMeanSeedTargetExpr0361 } }

noncomputable def lowMeanSeedTargetExpr0362 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (773, 40000)
  let e2 : LowMeanIntegerExpr := .atom (1543, 2500000)
  let e3 : LowMeanIntegerExpr := .atom (21, 1)
  let e4 : LowMeanIntegerExpr := .atom (23, 1)
  let e5 : LowMeanIntegerExpr := .neg (-23, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-2, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-1543, 1250000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (90453, 5000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (81, 625000)
  let e10 : LowMeanIntegerExpr := .pow (4, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (81, 156250) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-81, 156250) e11
  let e13 : LowMeanIntegerExpr := .add (87861, 5000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (32549, 2100000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (3472531, 105000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1129, 125)
  let e33 : LowMeanIntegerExpr := .pow (1000000000000000000000, 5842587018385982521381124421) e21 21
  let e34 : LowMeanIntegerExpr := .mul (9032000000000000000000, 5842587018385982521381124421) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-9032000000000000000000, 5842587018385982521381124421) e34
  let e36 : LowMeanIntegerExpr := .add (966076961025852108140672255560931, 29212935091929912606905622105000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (966369090376771407266741311781981, 29212935091929912606905622105000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-966076961025852108140672255560931, 29212935091929912606905622105000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0362 : LowMeanDirectSeedInput :=
  { record := 362, positions := [{ j := 8, mode := 0, left := 791, right := 0 }, { j := 9, mode := 0, left := 792, right := 0 }, { j := 14, mode := 0, left := 793, right := 0 }, { j := 15, mode := 0, left := 794, right := 0 }], target := { R := 21, expr := lowMeanSeedTargetExpr0362 } }

noncomputable def lowMeanSeedTargetExpr0363 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (773, 40000)
  let e2 : LowMeanIntegerExpr := .atom (1543, 2500000)
  let e3 : LowMeanIntegerExpr := .atom (23, 1)
  let e4 : LowMeanIntegerExpr := .neg (-23, 1) e3
  let e5 : LowMeanIntegerExpr := .add (0, 1) e3 e4
  let e6 : LowMeanIntegerExpr := .mul (0, 1) e2 e5
  let e7 : LowMeanIntegerExpr := .add (773, 40000) e1 e6
  let e8 : LowMeanIntegerExpr := .atom (81, 625000)
  let e9 : LowMeanIntegerExpr := .pow (0, 1) e5 2
  let e10 : LowMeanIntegerExpr := .mul (0, 1) e8 e9
  let e11 : LowMeanIntegerExpr := .neg (0, 1) e10
  let e12 : LowMeanIntegerExpr := .add (773, 40000) e7 e11
  let e13 : LowMeanIntegerExpr := .atom (2959, 1000000)
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
  let e28 : LowMeanIntegerExpr := .mul (32549, 44100000) e13 e27
  let e29 : LowMeanIntegerExpr := .mul (748627, 44100000) e28 e3
  let e30 : LowMeanIntegerExpr := .add (3201719, 88200000) e12 e29
  let e31 : LowMeanIntegerExpr := .atom (1129, 125)
  let e32 : LowMeanIntegerExpr := .pow (100000000000000000000000, 2576580875108218291929075869661) e20 23
  let e33 : LowMeanIntegerExpr := .mul (903200000000000000000000, 2576580875108218291929075869661) e31 e32
  let e34 : LowMeanIntegerExpr := .neg (-903200000000000000000000, 2576580875108218291929075869661) e33
  let e35 : LowMeanIntegerExpr := .add (18706141225919749572373852300079699, 515316175021643658385815173932200000) e30 e34
  let e36 : LowMeanIntegerExpr := .add (18711294387669966008957710451819021, 515316175021643658385815173932200000) e0 e35
  let e37 : LowMeanIntegerExpr := .atom (22, 1)
  let e38 : LowMeanIntegerExpr := .add (-1, 1) e37 e4
  let e39 : LowMeanIntegerExpr := .mul (-1543, 2500000) e2 e38
  let e40 : LowMeanIntegerExpr := .add (93539, 5000000) e1 e39
  let e41 : LowMeanIntegerExpr := .pow (1, 1) e38 2
  let e42 : LowMeanIntegerExpr := .mul (81, 625000) e8 e41
  let e43 : LowMeanIntegerExpr := .neg (-81, 625000) e42
  let e44 : LowMeanIntegerExpr := .add (92891, 5000000) e40 e43
  let e45 : LowMeanIntegerExpr := .mul (358039, 22050000) e28 e37
  let e46 : LowMeanIntegerExpr := .add (76768831, 2205000000) e44 e45
  let e47 : LowMeanIntegerExpr := .pow (10000000000000000000000, 122694327386105632949003612841) e20 22
  let e48 : LowMeanIntegerExpr := .mul (90320000000000000000000, 122694327386105632949003612841) e31 e47
  let e49 : LowMeanIntegerExpr := .neg (-90320000000000000000000, 122694327386105632949003612841) e48
  let e50 : LowMeanIntegerExpr := .add (21358051991298446902517210822177231, 613471636930528164745018064205000000) e46 e49
  let e51 : LowMeanIntegerExpr := .neg (-21358051991298446902517210822177231, 613471636930528164745018064205000000) e50
  let e52 : LowMeanIntegerExpr := .add (9631633937240882635540667014876837, 6441452187770545729822689674152500000) e36 e51
  e52

noncomputable def lowMeanSeedRecord0363 : LowMeanDirectSeedInput :=
  { record := 363, positions := [{ j := 9, mode := 0, left := 795, right := 0 }, { j := 10, mode := 0, left := 796, right := 0 }, { j := 14, mode := 0, left := 797, right := 0 }, { j := 15, mode := 0, left := 798, right := 0 }, { j := 16, mode := 0, left := 799, right := 0 }], target := { R := 23, expr := lowMeanSeedTargetExpr0363 } }

noncomputable def lowMeanSeedTargetExpr0364 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (773, 40000)
  let e2 : LowMeanIntegerExpr := .atom (1543, 2500000)
  let e3 : LowMeanIntegerExpr := .atom (24, 1)
  let e4 : LowMeanIntegerExpr := .atom (23, 1)
  let e5 : LowMeanIntegerExpr := .neg (-23, 1) e4
  let e6 : LowMeanIntegerExpr := .add (1, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (1543, 2500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (99711, 5000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (81, 625000)
  let e10 : LowMeanIntegerExpr := .pow (1, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (81, 625000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-81, 625000) e11
  let e13 : LowMeanIntegerExpr := .add (99063, 5000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (32549, 1837500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (27581861, 735000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1129, 125)
  let e33 : LowMeanIntegerExpr := .pow (1000000000000000000000000, 54108198377272584130510593262881) e21 24
  let e34 : LowMeanIntegerExpr := .mul (9032000000000000000000000, 54108198377272584130510593262881) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-9032000000000000000000000, 54108198377272584130510593262881) e34
  let e36 : LowMeanIntegerExpr := .add (10152368490356176697949313213634831303, 270540991886362920652552966314405000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (10155073900275040327155838743297975353, 270540991886362920652552966314405000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-10152368490356176697949313213634831303, 270540991886362920652552966314405000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0364 : LowMeanDirectSeedInput :=
  { record := 364, positions := [{ j := 10, mode := 0, left := 800, right := 0 }, { j := 11, mode := 0, left := 801, right := 0 }, { j := 15, mode := 0, left := 802, right := 0 }, { j := 16, mode := 0, left := 803, right := 0 }, { j := 17, mode := 0, left := 804, right := 0 }], target := { R := 24, expr := lowMeanSeedTargetExpr0364 } }

noncomputable def lowMeanSeedTargetExpr0365 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (773, 40000)
  let e2 : LowMeanIntegerExpr := .atom (1543, 2500000)
  let e3 : LowMeanIntegerExpr := .atom (28, 1)
  let e4 : LowMeanIntegerExpr := .atom (23, 1)
  let e5 : LowMeanIntegerExpr := .neg (-23, 1) e4
  let e6 : LowMeanIntegerExpr := .add (5, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (1543, 500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (22411, 1000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (81, 625000)
  let e10 : LowMeanIntegerExpr := .pow (25, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (81, 25000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-81, 25000) e11
  let e13 : LowMeanIntegerExpr := .add (19171, 1000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (32549, 1575000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (2509733, 63000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (1129, 125)
  let e33 : LowMeanIntegerExpr := .pow (10000000000000000000000000000, 10523016528610349434285830688358359761) e21 28
  let e34 : LowMeanIntegerExpr := .mul (90320000000000000000000000000, 10523016528610349434285830688358359761) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-90320000000000000000000000000, 10523016528610349434285830688358359761) e34
  let e36 : LowMeanIntegerExpr := .add (419205653194267271694579058904534782826251, 10523016528610349434285830688358359761000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (419310883359553375188921917211418366423861, 10523016528610349434285830688358359761000000) e0 e36
  let e38 : LowMeanIntegerExpr := .atom (25, 1)
  let e39 : LowMeanIntegerExpr := .add (2, 1) e38 e5
  let e40 : LowMeanIntegerExpr := .mul (1543, 1250000) e2 e39
  let e41 : LowMeanIntegerExpr := .add (102797, 5000000) e1 e40
  let e42 : LowMeanIntegerExpr := .pow (4, 1) e39 2
  let e43 : LowMeanIntegerExpr := .mul (81, 156250) e9 e42
  let e44 : LowMeanIntegerExpr := .neg (-81, 156250) e43
  let e45 : LowMeanIntegerExpr := .add (20041, 1000000) e41 e44
  let e46 : LowMeanIntegerExpr := .mul (32549, 1764000) e29 e38
  let e47 : LowMeanIntegerExpr := .add (16975331, 441000000) e45 e46
  let e48 : LowMeanIntegerExpr := .pow (10000000000000000000000000, 1136272165922724266740722458520501) e21 25
  let e49 : LowMeanIntegerExpr := .mul (90320000000000000000000000, 1136272165922724266740722458520501) e32 e48
  let e50 : LowMeanIntegerExpr := .neg (-90320000000000000000000000, 1136272165922724266740722458520501) e49
  let e51 : LowMeanIntegerExpr := .add (43738222883231666325750691411608332791, 1136272165922724266740722458520501000000) e47 e50
  let e52 : LowMeanIntegerExpr := .neg (-43738222883231666325750691411608332791, 1136272165922724266740722458520501000000) e51
  let e53 : LowMeanIntegerExpr := .add (1425120123794491334614476404851359644641, 1052301652861034943428583068835835976100000) e37 e52
  e53

noncomputable def lowMeanSeedRecord0365 : LowMeanDirectSeedInput :=
  { record := 365, positions := [{ j := 11, mode := 0, left := 805, right := 0 }, { j := 12, mode := 0, left := 806, right := 0 }, { j := 15, mode := 0, left := 807, right := 0 }, { j := 16, mode := 0, left := 808, right := 0 }, { j := 17, mode := 0, left := 809, right := 0 }, { j := 18, mode := 0, left := 810, right := 0 }], target := { R := 28, expr := lowMeanSeedTargetExpr0365 } }

noncomputable def lowMeanSeedTargetExpr0366 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (3013, 25000)
  let e2 : LowMeanIntegerExpr := .atom (-24, 15625)
  let e3 : LowMeanIntegerExpr := .atom (0, 1)
  let e4 : LowMeanIntegerExpr := .atom (8, 1)
  let e5 : LowMeanIntegerExpr := .neg (-8, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-8, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (192, 15625) e2 e6
  let e8 : LowMeanIntegerExpr := .add (16601, 125000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1591, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (64, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1591, 15625) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1591, 15625) e11
  let e13 : LowMeanIntegerExpr := .add (3873, 125000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (2473, 50000)
  let e15 : LowMeanIntegerExpr := .atom (13, 23)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (8, 13)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .atom (1, 1)
  let e20 : LowMeanIntegerExpr := .neg (-13, 23) e15
  let e21 : LowMeanIntegerExpr := .add (10, 23) e19 e20
  let e22 : LowMeanIntegerExpr := .mul (130, 529) e15 e21
  let e23 : LowMeanIntegerExpr := .neg (-8, 13) e17
  let e24 : LowMeanIntegerExpr := .add (5, 13) e19 e23
  let e25 : LowMeanIntegerExpr := .mul (40, 169) e17 e24
  let e26 : LowMeanIntegerExpr := .maximum (130, 529) e22 e25
  let e27 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e26
  let e28 : LowMeanIntegerExpr := .selectLE (130, 529) e15 e16 e27 e26
  let e29 : LowMeanIntegerExpr := .mul (32149, 2645000) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (0, 1) e29 e3
  let e31 : LowMeanIntegerExpr := .add (3873, 125000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (8933, 10000)
  let e33 : LowMeanIntegerExpr := .pow (1, 1) e21 0
  let e34 : LowMeanIntegerExpr := .mul (8933, 10000) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-8933, 10000) e34
  let e36 : LowMeanIntegerExpr := .add (-215579, 250000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-431153, 500000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (215579, 250000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0366 : LowMeanDirectSeedInput :=
  { record := 366, positions := [], target := { R := 0, expr := lowMeanSeedTargetExpr0366 } }

noncomputable def lowMeanSeedTargetExpr0367 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (3013, 25000)
  let e2 : LowMeanIntegerExpr := .atom (-24, 15625)
  let e3 : LowMeanIntegerExpr := .atom (1, 1)
  let e4 : LowMeanIntegerExpr := .atom (8, 1)
  let e5 : LowMeanIntegerExpr := .neg (-8, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-7, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (168, 15625) e2 e6
  let e8 : LowMeanIntegerExpr := .add (16409, 125000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1591, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (49, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (77959, 1000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-77959, 1000000) e11
  let e13 : LowMeanIntegerExpr := .add (53313, 1000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (2473, 50000)
  let e15 : LowMeanIntegerExpr := .atom (13, 23)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (8, 13)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .neg (-13, 23) e15
  let e20 : LowMeanIntegerExpr := .add (10, 23) e3 e19
  let e21 : LowMeanIntegerExpr := .mul (130, 529) e15 e20
  let e22 : LowMeanIntegerExpr := .neg (-8, 13) e17
  let e23 : LowMeanIntegerExpr := .add (5, 13) e3 e22
  let e24 : LowMeanIntegerExpr := .mul (40, 169) e17 e23
  let e25 : LowMeanIntegerExpr := .maximum (130, 529) e21 e24
  let e26 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e25
  let e27 : LowMeanIntegerExpr := .selectLE (130, 529) e15 e16 e26 e25
  let e28 : LowMeanIntegerExpr := .mul (32149, 2645000) e14 e27
  let e29 : LowMeanIntegerExpr := .mul (32149, 2645000) e28 e3
  let e30 : LowMeanIntegerExpr := .add (34632377, 529000000) e13 e29
  let e31 : LowMeanIntegerExpr := .atom (8933, 10000)
  let e32 : LowMeanIntegerExpr := .pow (10, 23) e20 1
  let e33 : LowMeanIntegerExpr := .mul (8933, 23000) e31 e32
  let e34 : LowMeanIntegerExpr := .neg (-8933, 23000) e33
  let e35 : LowMeanIntegerExpr := .add (-170826623, 529000000) e30 e34
  let e36 : LowMeanIntegerExpr := .add (-170821333, 529000000) e0 e35
  let e37 : LowMeanIntegerExpr := .neg (170826623, 529000000) e35
  let e38 : LowMeanIntegerExpr := .add (1, 100000) e36 e37
  e38

noncomputable def lowMeanSeedRecord0367 : LowMeanDirectSeedInput :=
  { record := 367, positions := [], target := { R := 1, expr := lowMeanSeedTargetExpr0367 } }

noncomputable def lowMeanSeedGroup0352 : List LowMeanDirectSeedInput := [lowMeanSeedRecord0352, lowMeanSeedRecord0353, lowMeanSeedRecord0354, lowMeanSeedRecord0355, lowMeanSeedRecord0356, lowMeanSeedRecord0357, lowMeanSeedRecord0358, lowMeanSeedRecord0359, lowMeanSeedRecord0360, lowMeanSeedRecord0361, lowMeanSeedRecord0362, lowMeanSeedRecord0363, lowMeanSeedRecord0364, lowMeanSeedRecord0365, lowMeanSeedRecord0366, lowMeanSeedRecord0367]

end Erdos993Lean.Analytic.V213
