module

public import Erdos993Lean.Analytic.V213.LowMeanCoreAll
public import Erdos993Lean.Analytic.V213.LowMeanData.Seed0432
public import Erdos993Lean.Analytic.V213.LowMeanFiberSeed
public import Erdos993Lean.Analytic.V213.LowMeanIntegerExpr
public import Erdos993Lean.Analytic.V213.LowMeanSeedGeometry
public import Erdos993Lean.Analytic.V213.LowMeanWidthData
public import Erdos993Lean.Ceiling.Prefix
public import Erdos993Lean.Ceiling.Statement

/-! Exact core/budget keys and equation-51 targets for the direct fibers. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanSeedTargetExpr0528 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (5559, 25000)
  let e2 : LowMeanIntegerExpr := .atom (7469, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (7, 1)
  let e4 : LowMeanIntegerExpr := .atom (39, 4)
  let e5 : LowMeanIntegerExpr := .neg (-39, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-11, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-82159, 4000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (807281, 4000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (2003, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (121, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (242363, 16000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-242363, 16000000) e11
  let e13 : LowMeanIntegerExpr := .add (2986761, 16000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (159, 3125)
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
  let e29 : LowMeanIntegerExpr := .mul (6042, 525625) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (42294, 525625) e29 e3
  let e31 : LowMeanIntegerExpr := .add (3594592401, 13456000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (8457, 10000)
  let e33 : LowMeanIntegerExpr := .pow (10000000, 17249876309) e21 7
  let e34 : LowMeanIntegerExpr := .mul (8457000, 17249876309) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-8457000, 17249876309) e34
  let e36 : LowMeanIntegerExpr := .add (73593908331178749, 275998020944000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (73596668311388189, 275998020944000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-73593908331178749, 275998020944000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0528 : LowMeanDirectSeedInput :=
  { record := 528, positions := [], target := { R := 7, expr := lowMeanSeedTargetExpr0528 } }

noncomputable def lowMeanSeedTargetExpr0529 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (5559, 25000)
  let e2 : LowMeanIntegerExpr := .atom (7469, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (8, 1)
  let e4 : LowMeanIntegerExpr := .atom (39, 4)
  let e5 : LowMeanIntegerExpr := .neg (-39, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-7, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-52283, 4000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (837157, 4000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (2003, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (49, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (98147, 16000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-98147, 16000000) e11
  let e13 : LowMeanIntegerExpr := .add (3250481, 16000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (159, 3125)
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
  let e29 : LowMeanIntegerExpr := .mul (6042, 525625) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (48336, 525625) e29 e3
  let e31 : LowMeanIntegerExpr := .add (3971056121, 13456000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (8457, 10000)
  let e33 : LowMeanIntegerExpr := .pow (100000000, 500246412961) e21 8
  let e34 : LowMeanIntegerExpr := .mul (84570000, 500246412961) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-84570000, 500246412961) e34
  let e36 : LowMeanIntegerExpr := .add (2360723669770597841, 8003942607376000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (2360803709196671601, 8003942607376000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-2360723669770597841, 8003942607376000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0529 : LowMeanDirectSeedInput :=
  { record := 529, positions := [], target := { R := 8, expr := lowMeanSeedTargetExpr0529 } }

noncomputable def lowMeanSeedTargetExpr0530 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (5559, 25000)
  let e2 : LowMeanIntegerExpr := .atom (7469, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (9, 1)
  let e4 : LowMeanIntegerExpr := .atom (39, 4)
  let e5 : LowMeanIntegerExpr := .neg (-39, 4) e4
  let e6 : LowMeanIntegerExpr := .add (-3, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-22407, 4000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (867033, 4000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (2003, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (9, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (18027, 16000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-18027, 16000000) e11
  let e13 : LowMeanIntegerExpr := .add (690021, 3200000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (159, 3125)
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
  let e29 : LowMeanIntegerExpr := .mul (6042, 525625) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (54378, 525625) e29 e3
  let e31 : LowMeanIntegerExpr := .add (858723021, 2691200000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (8457, 10000)
  let e33 : LowMeanIntegerExpr := .pow (1000000000, 14507145975869) e21 9
  let e34 : LowMeanIntegerExpr := .mul (845700000, 14507145975869) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-845700000, 14507145975869) e34
  let e36 : LowMeanIntegerExpr := .add (14810159655940809489, 46422867122780800000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (14810623884612037297, 46422867122780800000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-14810159655940809489, 46422867122780800000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0530 : LowMeanDirectSeedInput :=
  { record := 530, positions := [{ j := 5, mode := 0, left := 1043, right := 0 }], target := { R := 9, expr := lowMeanSeedTargetExpr0530 } }

noncomputable def lowMeanSeedTargetExpr0531 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (5559, 25000)
  let e2 : LowMeanIntegerExpr := .atom (7469, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (11, 1)
  let e4 : LowMeanIntegerExpr := .atom (39, 4)
  let e5 : LowMeanIntegerExpr := .neg (-39, 4) e4
  let e6 : LowMeanIntegerExpr := .add (5, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (7469, 800000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (185357, 800000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (2003, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (25, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (2003, 640000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-2003, 640000) e11
  let e13 : LowMeanIntegerExpr := .add (731413, 3200000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (159, 3125)
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
  let e29 : LowMeanIntegerExpr := .mul (6042, 525625) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (66462, 525625) e29 e3
  let e31 : LowMeanIntegerExpr := .add (955403773, 2691200000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (8457, 10000)
  let e33 : LowMeanIntegerExpr := .pow (100000000000, 12200509765705829) e21 11
  let e34 : LowMeanIntegerExpr := .mul (84570000000, 12200509765705829) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-84570000000, 12200509765705829) e34
  let e36 : LowMeanIntegerExpr := .add (13859911376807009553737, 39041631250258652800000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (2772060358623902428053, 7808326250051730560000) e0 e36
  let e38 : LowMeanIntegerExpr := .atom (10, 1)
  let e39 : LowMeanIntegerExpr := .add (1, 4) e38 e5
  let e40 : LowMeanIntegerExpr := .mul (7469, 4000000) e2 e39
  let e41 : LowMeanIntegerExpr := .add (896909, 4000000) e1 e40
  let e42 : LowMeanIntegerExpr := .pow (1, 16) e39 2
  let e43 : LowMeanIntegerExpr := .mul (2003, 16000000) e9 e42
  let e44 : LowMeanIntegerExpr := .neg (-2003, 16000000) e43
  let e45 : LowMeanIntegerExpr := .add (3585633, 16000000) e41 e44
  let e46 : LowMeanIntegerExpr := .mul (12084, 105125) e29 e38
  let e47 : LowMeanIntegerExpr := .add (4562269353, 13456000000) e45 e46
  let e48 : LowMeanIntegerExpr := .pow (10000000000, 420707233300201) e21 10
  let e49 : LowMeanIntegerExpr := .mul (8457000000, 420707233300201) e32 e48
  let e50 : LowMeanIntegerExpr := .neg (-8457000000, 420707233300201) e49
  let e51 : LowMeanIntegerExpr := .add (2282123566800152284233, 6731315732803216000000) e47 e50
  let e52 : LowMeanIntegerExpr := .neg (-2282123566800152284233, 6731315732803216000000) e51
  let e53 : LowMeanIntegerExpr := .add (389990691049143057321, 24401019531411658000000) e37 e52
  e53

noncomputable def lowMeanSeedRecord0531 : LowMeanDirectSeedInput :=
  { record := 531, positions := [{ j := 6, mode := 0, left := 1044, right := 0 }, { j := 9, mode := 0, left := 1045, right := 0 }], target := { R := 11, expr := lowMeanSeedTargetExpr0531 } }

noncomputable def lowMeanSeedTargetExpr0532 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (5559, 25000)
  let e2 : LowMeanIntegerExpr := .atom (7469, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (12, 1)
  let e4 : LowMeanIntegerExpr := .atom (39, 4)
  let e5 : LowMeanIntegerExpr := .neg (-39, 4) e4
  let e6 : LowMeanIntegerExpr := .add (9, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (67221, 4000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (956661, 4000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (2003, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (81, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (162243, 16000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-162243, 16000000) e11
  let e13 : LowMeanIntegerExpr := .add (3664401, 16000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (159, 3125)
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
  let e29 : LowMeanIntegerExpr := .mul (6042, 525625) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (72504, 525625) e29 e3
  let e31 : LowMeanIntegerExpr := .add (4937863641, 13456000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (8457, 10000)
  let e33 : LowMeanIntegerExpr := .pow (1000000000000, 353814783205469041) e21 12
  let e34 : LowMeanIntegerExpr := .mul (845700000000, 353814783205469041) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-845700000000, 353814783205469041) e34
  let e36 : LowMeanIntegerExpr := .add (2077381419618766955891841, 5661036531287504656000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (2077438029984079830938401, 5661036531287504656000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-2077381419618766955891841, 5661036531287504656000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0532 : LowMeanDirectSeedInput :=
  { record := 532, positions := [{ j := 7, mode := 0, left := 1046, right := 0 }, { j := 10, mode := 0, left := 1047, right := 0 }], target := { R := 12, expr := lowMeanSeedTargetExpr0532 } }

noncomputable def lowMeanSeedTargetExpr0533 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (5559, 25000)
  let e2 : LowMeanIntegerExpr := .atom (7469, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (13, 1)
  let e4 : LowMeanIntegerExpr := .atom (39, 4)
  let e5 : LowMeanIntegerExpr := .neg (-39, 4) e4
  let e6 : LowMeanIntegerExpr := .add (13, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (97097, 4000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (986537, 4000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (2003, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (169, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (338507, 16000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-338507, 16000000) e11
  let e13 : LowMeanIntegerExpr := .add (3607641, 16000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (159, 3125)
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
  let e29 : LowMeanIntegerExpr := .mul (6042, 525625) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (78546, 525625) e29 e3
  let e31 : LowMeanIntegerExpr := .add (5044803681, 13456000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (8457, 10000)
  let e33 : LowMeanIntegerExpr := .pow (10000000000000, 10260628712958602189) e21 13
  let e34 : LowMeanIntegerExpr := .mul (8457000000000, 10260628712958602189) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-8457000000000, 10260628712958602189) e34
  let e36 : LowMeanIntegerExpr := .add (61549041264109213702356549, 164170059407337635024000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (61550682964703287078706789, 164170059407337635024000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-61549041264109213702356549, 164170059407337635024000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0533 : LowMeanDirectSeedInput :=
  { record := 533, positions := [{ j := 8, mode := 0, left := 1048, right := 0 }, { j := 10, mode := 0, left := 1049, right := 0 }, { j := 11, mode := 0, left := 1050, right := 0 }], target := { R := 13, expr := lowMeanSeedTargetExpr0533 } }

noncomputable def lowMeanSeedTargetExpr0534 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (5559, 25000)
  let e2 : LowMeanIntegerExpr := .atom (7469, 1000000)
  let e3 : LowMeanIntegerExpr := .atom (14, 1)
  let e4 : LowMeanIntegerExpr := .atom (39, 4)
  let e5 : LowMeanIntegerExpr := .neg (-39, 4) e4
  let e6 : LowMeanIntegerExpr := .add (17, 4) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (126973, 4000000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (1016413, 4000000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (2003, 1000000)
  let e10 : LowMeanIntegerExpr := .pow (289, 16) e6 2
  let e11 : LowMeanIntegerExpr := .mul (578867, 16000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-578867, 16000000) e11
  let e13 : LowMeanIntegerExpr := .add (697357, 3200000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (159, 3125)
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
  let e29 : LowMeanIntegerExpr := .mul (6042, 525625) e14 e28
  let e30 : LowMeanIntegerExpr := .mul (84588, 525625) e29 e3
  let e31 : LowMeanIntegerExpr := .add (1019567797, 2691200000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (8457, 10000)
  let e33 : LowMeanIntegerExpr := .pow (100000000000000, 297558232675799463481) e21 14
  let e34 : LowMeanIntegerExpr := .mul (84570000000000, 297558232675799463481) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-84570000000000, 297558232675799463481) e34
  let e36 : LowMeanIntegerExpr := .add (360737888434832668484072677, 952186344562558283139200000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (360747410298278294066904069, 952186344562558283139200000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-360737888434832668484072677, 952186344562558283139200000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0534 : LowMeanDirectSeedInput :=
  { record := 534, positions := [{ j := 9, mode := 0, left := 1051, right := 0 }, { j := 11, mode := 0, left := 1052, right := 0 }, { j := 12, mode := 0, left := 1053, right := 0 }], target := { R := 14, expr := lowMeanSeedTargetExpr0534 } }

noncomputable def lowMeanSeedTargetExpr0535 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (83, 800)
  let e2 : LowMeanIntegerExpr := .atom (883, 500000)
  let e3 : LowMeanIntegerExpr := .atom (0, 1)
  let e4 : LowMeanIntegerExpr := .atom (32, 1)
  let e5 : LowMeanIntegerExpr := .neg (-32, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-32, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-883, 15625) e2 e6
  let e8 : LowMeanIntegerExpr := .add (23619, 500000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1087, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (1024, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (8696, 78125) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-8696, 78125) e11
  let e13 : LowMeanIntegerExpr := .add (-160177, 2500000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (0, 1) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-160177, 2500000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (3743, 1000)
  let e33 : LowMeanIntegerExpr := .pow (1, 1) e21 0
  let e34 : LowMeanIntegerExpr := .mul (3743, 1000) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-3743, 1000) e34
  let e36 : LowMeanIntegerExpr := .add (-9517677, 2500000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-2379413, 625000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (9517677, 2500000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0535 : LowMeanDirectSeedInput :=
  { record := 535, positions := [], target := { R := 0, expr := lowMeanSeedTargetExpr0535 } }

noncomputable def lowMeanSeedTargetExpr0536 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (83, 800)
  let e2 : LowMeanIntegerExpr := .atom (883, 500000)
  let e3 : LowMeanIntegerExpr := .atom (1, 1)
  let e4 : LowMeanIntegerExpr := .atom (32, 1)
  let e5 : LowMeanIntegerExpr := .neg (-32, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-31, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-27373, 500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (12251, 250000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1087, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (961, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1044607, 10000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1044607, 10000000) e11
  let e13 : LowMeanIntegerExpr := .add (-554567, 10000000) e8 e12
  let e14 : LowMeanIntegerExpr := .atom (1009, 200000)
  let e15 : LowMeanIntegerExpr := .atom (19, 29)
  let e16 : LowMeanIntegerExpr := .atom (1, 2)
  let e17 : LowMeanIntegerExpr := .atom (7, 10)
  let e18 : LowMeanIntegerExpr := .atom (1, 4)
  let e19 : LowMeanIntegerExpr := .neg (-19, 29) e15
  let e20 : LowMeanIntegerExpr := .add (10, 29) e3 e19
  let e21 : LowMeanIntegerExpr := .mul (190, 841) e15 e20
  let e22 : LowMeanIntegerExpr := .neg (-7, 10) e17
  let e23 : LowMeanIntegerExpr := .add (3, 10) e3 e22
  let e24 : LowMeanIntegerExpr := .mul (21, 100) e17 e23
  let e25 : LowMeanIntegerExpr := .maximum (190, 841) e21 e24
  let e26 : LowMeanIntegerExpr := .selectLE (1, 4) e16 e17 e18 e25
  let e27 : LowMeanIntegerExpr := .selectLE (190, 841) e15 e16 e26 e25
  let e28 : LowMeanIntegerExpr := .mul (19171, 16820000) e14 e27
  let e29 : LowMeanIntegerExpr := .mul (19171, 16820000) e28 e3
  let e30 : LowMeanIntegerExpr := .add (-456805347, 8410000000) e13 e29
  let e31 : LowMeanIntegerExpr := .atom (3743, 1000)
  let e32 : LowMeanIntegerExpr := .pow (10, 29) e20 1
  let e33 : LowMeanIntegerExpr := .mul (3743, 2900) e31 e32
  let e34 : LowMeanIntegerExpr := .neg (-3743, 2900) e33
  let e35 : LowMeanIntegerExpr := .add (-11311505347, 8410000000) e30 e34
  let e36 : LowMeanIntegerExpr := .add (-11311421247, 8410000000) e0 e35
  let e37 : LowMeanIntegerExpr := .neg (11311505347, 8410000000) e35
  let e38 : LowMeanIntegerExpr := .add (1, 100000) e36 e37
  e38

noncomputable def lowMeanSeedRecord0536 : LowMeanDirectSeedInput :=
  { record := 536, positions := [], target := { R := 1, expr := lowMeanSeedTargetExpr0536 } }

noncomputable def lowMeanSeedTargetExpr0537 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (83, 800)
  let e2 : LowMeanIntegerExpr := .atom (883, 500000)
  let e3 : LowMeanIntegerExpr := .atom (2, 1)
  let e4 : LowMeanIntegerExpr := .atom (32, 1)
  let e5 : LowMeanIntegerExpr := .neg (-32, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-30, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-2649, 50000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (5077, 100000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1087, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (900, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (9783, 100000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-9783, 100000) e11
  let e13 : LowMeanIntegerExpr := .add (-2353, 50000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (19171, 8410000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-941509, 21025000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (3743, 1000)
  let e33 : LowMeanIntegerExpr := .pow (100, 841) e21 2
  let e34 : LowMeanIntegerExpr := .mul (3743, 8410) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-3743, 8410) e34
  let e36 : LowMeanIntegerExpr := .add (-10299009, 21025000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-8239039, 16820000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (10299009, 21025000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0537 : LowMeanDirectSeedInput :=
  { record := 537, positions := [], target := { R := 2, expr := lowMeanSeedTargetExpr0537 } }

noncomputable def lowMeanSeedTargetExpr0538 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (83, 800)
  let e2 : LowMeanIntegerExpr := .atom (883, 500000)
  let e3 : LowMeanIntegerExpr := .atom (3, 1)
  let e4 : LowMeanIntegerExpr := .atom (32, 1)
  let e5 : LowMeanIntegerExpr := .neg (-32, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-29, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-25607, 500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (6567, 125000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1087, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (841, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (914167, 10000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-914167, 10000000) e11
  let e13 : LowMeanIntegerExpr := .add (-388807, 10000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (57513, 16820000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-298230187, 8410000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (3743, 1000)
  let e33 : LowMeanIntegerExpr := .pow (1000, 24389) e21 3
  let e34 : LowMeanIntegerExpr := .mul (3743, 24389) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-3743, 24389) e34
  let e36 : LowMeanIntegerExpr := .add (-46078675423, 243890000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-46076236523, 243890000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (46078675423, 243890000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0538 : LowMeanDirectSeedInput :=
  { record := 538, positions := [], target := { R := 3, expr := lowMeanSeedTargetExpr0538 } }

noncomputable def lowMeanSeedTargetExpr0539 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (83, 800)
  let e2 : LowMeanIntegerExpr := .atom (883, 500000)
  let e3 : LowMeanIntegerExpr := .atom (4, 1)
  let e4 : LowMeanIntegerExpr := .atom (32, 1)
  let e5 : LowMeanIntegerExpr := .neg (-32, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-28, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-6181, 125000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (27151, 500000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1087, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (784, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (53263, 625000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-53263, 625000) e11
  let e13 : LowMeanIntegerExpr := .add (-77297, 2500000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (19171, 4205000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-55421277, 2102500000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (3743, 1000)
  let e33 : LowMeanIntegerExpr := .pow (10000, 707281) e21 4
  let e34 : LowMeanIntegerExpr := .mul (37430, 707281) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-37430, 707281) e34
  let e36 : LowMeanIntegerExpr := .add (-140184293957, 1768202500000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-35041652983, 442050625000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (140184293957, 1768202500000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0539 : LowMeanDirectSeedInput :=
  { record := 539, positions := [{ j := 1, mode := 0, left := 1054, right := 0 }], target := { R := 4, expr := lowMeanSeedTargetExpr0539 } }

noncomputable def lowMeanSeedTargetExpr0540 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (83, 800)
  let e2 : LowMeanIntegerExpr := .atom (883, 500000)
  let e3 : LowMeanIntegerExpr := .atom (5, 1)
  let e4 : LowMeanIntegerExpr := .atom (32, 1)
  let e5 : LowMeanIntegerExpr := .neg (-32, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-27, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-23841, 500000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (14017, 250000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1087, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (729, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (792423, 10000000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-792423, 10000000) e11
  let e13 : LowMeanIntegerExpr := .add (-231743, 10000000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (19171, 3364000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-146968363, 8410000000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (3743, 1000)
  let e33 : LowMeanIntegerExpr := .pow (100000, 20511149) e21 5
  let e34 : LowMeanIntegerExpr := .mul (374300, 20511149) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-374300, 20511149) e34
  let e36 : LowMeanIntegerExpr := .add (-7327411405207, 205111490000000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-7325360290307, 205111490000000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (7327411405207, 205111490000000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0540 : LowMeanDirectSeedInput :=
  { record := 540, positions := [{ j := 1, mode := 0, left := 1055, right := 0 }], target := { R := 5, expr := lowMeanSeedTargetExpr0540 } }

noncomputable def lowMeanSeedTargetExpr0541 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (83, 800)
  let e2 : LowMeanIntegerExpr := .atom (883, 500000)
  let e3 : LowMeanIntegerExpr := .atom (6, 1)
  let e4 : LowMeanIntegerExpr := .atom (32, 1)
  let e5 : LowMeanIntegerExpr := .neg (-32, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-26, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-11479, 250000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (28917, 500000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1087, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (676, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (183703, 2500000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-183703, 2500000) e11
  let e13 : LowMeanIntegerExpr := .add (-19559, 1250000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (57513, 8410000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-4629997, 525625000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (3743, 1000)
  let e33 : LowMeanIntegerExpr := .pow (1000000, 594823321) e21 6
  let e34 : LowMeanIntegerExpr := .mul (3743000, 594823321) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-3743000, 594823321) e34
  let e36 : LowMeanIntegerExpr := .add (-5614083908157, 371764575625000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-22441465049603, 1487058302500000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (5614083908157, 371764575625000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0541 : LowMeanDirectSeedInput :=
  { record := 541, positions := [{ j := 2, mode := 0, left := 1056, right := 0 }], target := { R := 6, expr := lowMeanSeedTargetExpr0541 } }

noncomputable def lowMeanSeedTargetExpr0542 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (83, 800)
  let e2 : LowMeanIntegerExpr := .atom (883, 500000)
  let e3 : LowMeanIntegerExpr := .atom (7, 1)
  let e4 : LowMeanIntegerExpr := .atom (32, 1)
  let e5 : LowMeanIntegerExpr := .neg (-32, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-25, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-883, 20000) e2 e6
  let e8 : LowMeanIntegerExpr := .add (149, 2500) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1087, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (625, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (1087, 16000) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-1087, 16000) e11
  let e13 : LowMeanIntegerExpr := .add (-667, 80000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (134197, 16820000) e29 e3
  let e31 : LowMeanIntegerExpr := .add (-24159, 67280000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (3743, 1000)
  let e33 : LowMeanIntegerExpr := .pow (10000000, 17249876309) e21 7
  let e34 : LowMeanIntegerExpr := .mul (37430000, 17249876309) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-37430000, 17249876309) e34
  let e36 : LowMeanIntegerExpr := .add (-3489928848691, 1379990104720000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (-17380644738219, 6899950523600000) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (3489928848691, 1379990104720000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0542 : LowMeanDirectSeedInput :=
  { record := 542, positions := [], target := { R := 7, expr := lowMeanSeedTargetExpr0542 } }

noncomputable def lowMeanSeedTargetExpr0543 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (1, 100000)
  let e1 : LowMeanIntegerExpr := .atom (83, 800)
  let e2 : LowMeanIntegerExpr := .atom (883, 500000)
  let e3 : LowMeanIntegerExpr := .atom (8, 1)
  let e4 : LowMeanIntegerExpr := .atom (32, 1)
  let e5 : LowMeanIntegerExpr := .neg (-32, 1) e4
  let e6 : LowMeanIntegerExpr := .add (-24, 1) e3 e5
  let e7 : LowMeanIntegerExpr := .mul (-2649, 62500) e2 e6
  let e8 : LowMeanIntegerExpr := .add (30683, 500000) e1 e7
  let e9 : LowMeanIntegerExpr := .atom (1087, 10000000)
  let e10 : LowMeanIntegerExpr := .pow (576, 1) e6 2
  let e11 : LowMeanIntegerExpr := .mul (9783, 156250) e9 e10
  let e12 : LowMeanIntegerExpr := .neg (-9783, 156250) e11
  let e13 : LowMeanIntegerExpr := .add (-3113, 2500000) e8 e12
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
  let e30 : LowMeanIntegerExpr := .mul (19171, 2102500) e29 e3
  let e31 : LowMeanIntegerExpr := .add (16552967, 2102500000) e13 e30
  let e32 : LowMeanIntegerExpr := .atom (3743, 1000)
  let e33 : LowMeanIntegerExpr := .pow (100000000, 500246412961) e21 8
  let e34 : LowMeanIntegerExpr := .mul (374300000, 500246412961) e32 e33
  let e35 : LowMeanIntegerExpr := .neg (-374300000, 500246412961) e34
  let e36 : LowMeanIntegerExpr := .add (8910340803343407, 1250616032402500000) e31 e35
  let e37 : LowMeanIntegerExpr := .add (1115355870458429, 156327004050312500) e0 e36
  let e38 : LowMeanIntegerExpr := .neg (-8910340803343407, 1250616032402500000) e36
  let e39 : LowMeanIntegerExpr := .add (1, 100000) e37 e38
  e39

noncomputable def lowMeanSeedRecord0543 : LowMeanDirectSeedInput :=
  { record := 543, positions := [], target := { R := 8, expr := lowMeanSeedTargetExpr0543 } }

noncomputable def lowMeanSeedGroup0528 : List LowMeanDirectSeedInput := [lowMeanSeedRecord0528, lowMeanSeedRecord0529, lowMeanSeedRecord0530, lowMeanSeedRecord0531, lowMeanSeedRecord0532, lowMeanSeedRecord0533, lowMeanSeedRecord0534, lowMeanSeedRecord0535, lowMeanSeedRecord0536, lowMeanSeedRecord0537, lowMeanSeedRecord0538, lowMeanSeedRecord0539, lowMeanSeedRecord0540, lowMeanSeedRecord0541, lowMeanSeedRecord0542, lowMeanSeedRecord0543]

end Erdos993Lean.Analytic.V213
