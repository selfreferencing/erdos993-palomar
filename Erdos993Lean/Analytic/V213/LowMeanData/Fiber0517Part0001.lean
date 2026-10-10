module

public import Erdos993Lean.Analytic.V213.LowMeanCoreChecker
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0513
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0517Part0000
public import Erdos993Lean.Analytic.V213.LowMeanIntegerExpr
public import Erdos993Lean.Ceiling.Prefix
public import Erdos993Lean.Ceiling.Statement


/-! Direct-fiber core witnesses with explicit complete integer windows. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanRankExpr0517_145_a : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e1 : LowMeanIntegerExpr := .atom (26, 78125)
  let e2 : LowMeanIntegerExpr := .atom (42, 1)
  let e3 : LowMeanIntegerExpr := .atom (189, 4)
  let e4 : LowMeanIntegerExpr := .neg (-189, 4) e3
  let e5 : LowMeanIntegerExpr := .add (-21, 4) e2 e4
  let e6 : LowMeanIntegerExpr := .mul (-273, 156250) e1 e5
  let e7 : LowMeanIntegerExpr := .add (16333, 2000000) e0 e6
  let e8 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e9 : LowMeanIntegerExpr := .pow (441, 16) e5 2
  let e10 : LowMeanIntegerExpr := .mul (570213, 1600000000) e8 e9
  let e11 : LowMeanIntegerExpr := .neg (-570213, 1600000000) e10
  let e12 : LowMeanIntegerExpr := .add (12496187, 1600000000) e7 e11
  let e13 : LowMeanIntegerExpr := .atom (-4189, 5000000)
  let e14 : LowMeanIntegerExpr := .pow (17547721, 25000000000000) e13 2
  let e15 : LowMeanIntegerExpr := .atom (4, 1)
  let e16 : LowMeanIntegerExpr := .atom (2063, 10000000)
  let e17 : LowMeanIntegerExpr := .mul (2063, 2500000) e15 e16
  let e18 : LowMeanIntegerExpr := .div (17547721, 20630000000) e14 e17
  let e19 : LowMeanIntegerExpr := .add (28587269141, 3300800000000) e12 e18
  let e20 : LowMeanIntegerExpr := .atom (328000, 1)
  let e21 : LowMeanIntegerExpr := .atom (1, 1)
  let e22 : LowMeanIntegerExpr := .atom (19, 29)
  let e23 : LowMeanIntegerExpr := .neg (-19, 29) e22
  let e24 : LowMeanIntegerExpr := .add (10, 29) e21 e23
  let e25 : LowMeanIntegerExpr := .pow (1000000000000000000000000000000000000000000, 26346074268992142099064516382762907506814419719803282255713641) e24 42
  let e26 : LowMeanIntegerExpr := .mul (328000000000000000000000000000000000000000000000, 26346074268992142099064516382762907506814419719803282255713641) e20 e25
  let e27 : LowMeanIntegerExpr := .neg (-328000000000000000000000000000000000000000000000, 26346074268992142099064516382762907506814419719803282255713641) e26
  let e28 : LowMeanIntegerExpr := .add (753162315935370534600074014157047010088993108069754237419275440292052381, 86963121947089262640592155676223805098493036611126674069659586212800000000) e19 e27
  let e29 : LowMeanIntegerExpr := .atom (1, 100000)
  let e30 : LowMeanIntegerExpr := .add (754031947154841427226479935713809248139978038435865504159972036154180381, 86963121947089262640592155676223805098493036611126674069659586212800000000) e28 e29
  let e31 : LowMeanIntegerExpr := .atom (0, 1)
  let e32 : LowMeanIntegerExpr := .add (754031947154841427226479935713809248139978038435865504159972036154180381, 86963121947089262640592155676223805098493036611126674069659586212800000000) e30 e31
  let e33 : LowMeanIntegerExpr := .atom (8, 13)
  let e34 : LowMeanIntegerExpr := .mul (336, 13) e2 e33
  let e35 : LowMeanIntegerExpr := .atom (100, 1)
  let e36 : LowMeanIntegerExpr := .atom (2, 1)
  let e37 : LowMeanIntegerExpr := .mul (2063, 5000000) e36 e16
  let e38 : LowMeanIntegerExpr := .div (-4189, 2063) e13 e37
  let e39 : LowMeanIntegerExpr := .add (202111, 2063) e35 e38
  let e40 : LowMeanIntegerExpr := .neg (-202111, 2063) e39
  let e41 : LowMeanIntegerExpr := .add (-1934275, 26819) e34 e40
  let e42 : LowMeanIntegerExpr := .mul (798, 29) e2 e22
  let e43 : LowMeanIntegerExpr := .neg (-798, 29) e42
  let e44 : LowMeanIntegerExpr := .add (4214945, 59827) e39 e43
  let e45 : LowMeanIntegerExpr := .maximum (4214945, 59827) e41 e44
  let e46 : LowMeanIntegerExpr := .maximum (4214945, 59827) e31 e45
  let e47 : LowMeanIntegerExpr := .pow (17765761353025, 3579269929) e46 2
  let e48 : LowMeanIntegerExpr := .mul (710630454121, 693993200000) e16 e47
  let e49 : LowMeanIntegerExpr := .neg (-710630454121, 693993200000) e48
  let e50 : LowMeanIntegerExpr := .add (-42798776714677143554177561485907863820730048893790344513841327160353613, 42153718830387427358503226212420652010903071551685251609141825600000000) e32 e49
  let e51 : LowMeanIntegerExpr := .neg (42798776714677143554177561485907863820730048893790344513841327160353613, 42153718830387427358503226212420652010903071551685251609141825600000000) e50
  e51

noncomputable def lowMeanRankExpr0517_145_b : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (0, 1)
  e0

noncomputable def lowMeanRankExpr0517_146_a : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e1 : LowMeanIntegerExpr := .atom (26, 78125)
  let e2 : LowMeanIntegerExpr := .atom (42, 1)
  let e3 : LowMeanIntegerExpr := .atom (189, 4)
  let e4 : LowMeanIntegerExpr := .neg (-189, 4) e3
  let e5 : LowMeanIntegerExpr := .add (-21, 4) e2 e4
  let e6 : LowMeanIntegerExpr := .mul (-273, 156250) e1 e5
  let e7 : LowMeanIntegerExpr := .add (16333, 2000000) e0 e6
  let e8 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e9 : LowMeanIntegerExpr := .pow (441, 16) e5 2
  let e10 : LowMeanIntegerExpr := .mul (570213, 1600000000) e8 e9
  let e11 : LowMeanIntegerExpr := .neg (-570213, 1600000000) e10
  let e12 : LowMeanIntegerExpr := .add (12496187, 1600000000) e7 e11
  let e13 : LowMeanIntegerExpr := .atom (-4189, 5000000)
  let e14 : LowMeanIntegerExpr := .pow (17547721, 25000000000000) e13 2
  let e15 : LowMeanIntegerExpr := .atom (4, 1)
  let e16 : LowMeanIntegerExpr := .atom (2063, 10000000)
  let e17 : LowMeanIntegerExpr := .mul (2063, 2500000) e15 e16
  let e18 : LowMeanIntegerExpr := .div (17547721, 20630000000) e14 e17
  let e19 : LowMeanIntegerExpr := .add (28587269141, 3300800000000) e12 e18
  let e20 : LowMeanIntegerExpr := .atom (328000, 1)
  let e21 : LowMeanIntegerExpr := .atom (1, 1)
  let e22 : LowMeanIntegerExpr := .atom (19, 29)
  let e23 : LowMeanIntegerExpr := .neg (-19, 29) e22
  let e24 : LowMeanIntegerExpr := .add (10, 29) e21 e23
  let e25 : LowMeanIntegerExpr := .pow (1000000000000000000000000000000000000000000, 26346074268992142099064516382762907506814419719803282255713641) e24 42
  let e26 : LowMeanIntegerExpr := .mul (328000000000000000000000000000000000000000000000, 26346074268992142099064516382762907506814419719803282255713641) e20 e25
  let e27 : LowMeanIntegerExpr := .neg (-328000000000000000000000000000000000000000000000, 26346074268992142099064516382762907506814419719803282255713641) e26
  let e28 : LowMeanIntegerExpr := .add (753162315935370534600074014157047010088993108069754237419275440292052381, 86963121947089262640592155676223805098493036611126674069659586212800000000) e19 e27
  let e29 : LowMeanIntegerExpr := .atom (1, 100000)
  let e30 : LowMeanIntegerExpr := .add (754031947154841427226479935713809248139978038435865504159972036154180381, 86963121947089262640592155676223805098493036611126674069659586212800000000) e28 e29
  let e31 : LowMeanIntegerExpr := .atom (0, 1)
  let e32 : LowMeanIntegerExpr := .add (754031947154841427226479935713809248139978038435865504159972036154180381, 86963121947089262640592155676223805098493036611126674069659586212800000000) e30 e31
  let e33 : LowMeanIntegerExpr := .atom (8, 13)
  let e34 : LowMeanIntegerExpr := .mul (336, 13) e2 e33
  let e35 : LowMeanIntegerExpr := .atom (101, 1)
  let e36 : LowMeanIntegerExpr := .atom (2, 1)
  let e37 : LowMeanIntegerExpr := .mul (2063, 5000000) e36 e16
  let e38 : LowMeanIntegerExpr := .div (-4189, 2063) e13 e37
  let e39 : LowMeanIntegerExpr := .add (204174, 2063) e35 e38
  let e40 : LowMeanIntegerExpr := .neg (-204174, 2063) e39
  let e41 : LowMeanIntegerExpr := .add (-1961094, 26819) e34 e40
  let e42 : LowMeanIntegerExpr := .mul (798, 29) e2 e22
  let e43 : LowMeanIntegerExpr := .neg (-798, 29) e42
  let e44 : LowMeanIntegerExpr := .add (4274772, 59827) e39 e43
  let e45 : LowMeanIntegerExpr := .maximum (4274772, 59827) e41 e44
  let e46 : LowMeanIntegerExpr := .maximum (4274772, 59827) e31 e45
  let e47 : LowMeanIntegerExpr := .pow (18273675651984, 3579269929) e46 2
  let e48 : LowMeanIntegerExpr := .mul (1142104728249, 1084364375000) e16 e47
  let e49 : LowMeanIntegerExpr := .neg (-1142104728249, 1084364375000) e48
  let e50 : LowMeanIntegerExpr := .add (-44032822036634247894287044017392116305309524727943995062928943409344493, 42153718830387427358503226212420652010903071551685251609141825600000000) e32 e49
  let e51 : LowMeanIntegerExpr := .neg (44032822036634247894287044017392116305309524727943995062928943409344493, 42153718830387427358503226212420652010903071551685251609141825600000000) e50
  e51

noncomputable def lowMeanRankExpr0517_146_b : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (0, 1)
  e0

noncomputable def lowMeanRankExpr0517_147_a : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e1 : LowMeanIntegerExpr := .atom (26, 78125)
  let e2 : LowMeanIntegerExpr := .atom (42, 1)
  let e3 : LowMeanIntegerExpr := .atom (189, 4)
  let e4 : LowMeanIntegerExpr := .neg (-189, 4) e3
  let e5 : LowMeanIntegerExpr := .add (-21, 4) e2 e4
  let e6 : LowMeanIntegerExpr := .mul (-273, 156250) e1 e5
  let e7 : LowMeanIntegerExpr := .add (16333, 2000000) e0 e6
  let e8 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e9 : LowMeanIntegerExpr := .pow (441, 16) e5 2
  let e10 : LowMeanIntegerExpr := .mul (570213, 1600000000) e8 e9
  let e11 : LowMeanIntegerExpr := .neg (-570213, 1600000000) e10
  let e12 : LowMeanIntegerExpr := .add (12496187, 1600000000) e7 e11
  let e13 : LowMeanIntegerExpr := .atom (-4189, 5000000)
  let e14 : LowMeanIntegerExpr := .pow (17547721, 25000000000000) e13 2
  let e15 : LowMeanIntegerExpr := .atom (4, 1)
  let e16 : LowMeanIntegerExpr := .atom (2063, 10000000)
  let e17 : LowMeanIntegerExpr := .mul (2063, 2500000) e15 e16
  let e18 : LowMeanIntegerExpr := .div (17547721, 20630000000) e14 e17
  let e19 : LowMeanIntegerExpr := .add (28587269141, 3300800000000) e12 e18
  let e20 : LowMeanIntegerExpr := .atom (328000, 1)
  let e21 : LowMeanIntegerExpr := .atom (1, 1)
  let e22 : LowMeanIntegerExpr := .atom (19, 29)
  let e23 : LowMeanIntegerExpr := .neg (-19, 29) e22
  let e24 : LowMeanIntegerExpr := .add (10, 29) e21 e23
  let e25 : LowMeanIntegerExpr := .pow (1000000000000000000000000000000000000000000, 26346074268992142099064516382762907506814419719803282255713641) e24 42
  let e26 : LowMeanIntegerExpr := .mul (328000000000000000000000000000000000000000000000, 26346074268992142099064516382762907506814419719803282255713641) e20 e25
  let e27 : LowMeanIntegerExpr := .neg (-328000000000000000000000000000000000000000000000, 26346074268992142099064516382762907506814419719803282255713641) e26
  let e28 : LowMeanIntegerExpr := .add (753162315935370534600074014157047010088993108069754237419275440292052381, 86963121947089262640592155676223805098493036611126674069659586212800000000) e19 e27
  let e29 : LowMeanIntegerExpr := .atom (1, 100000)
  let e30 : LowMeanIntegerExpr := .add (754031947154841427226479935713809248139978038435865504159972036154180381, 86963121947089262640592155676223805098493036611126674069659586212800000000) e28 e29
  let e31 : LowMeanIntegerExpr := .atom (0, 1)
  let e32 : LowMeanIntegerExpr := .add (754031947154841427226479935713809248139978038435865504159972036154180381, 86963121947089262640592155676223805098493036611126674069659586212800000000) e30 e31
  let e33 : LowMeanIntegerExpr := .atom (8, 13)
  let e34 : LowMeanIntegerExpr := .mul (336, 13) e2 e33
  let e35 : LowMeanIntegerExpr := .atom (102, 1)
  let e36 : LowMeanIntegerExpr := .atom (2, 1)
  let e37 : LowMeanIntegerExpr := .mul (2063, 5000000) e36 e16
  let e38 : LowMeanIntegerExpr := .div (-4189, 2063) e13 e37
  let e39 : LowMeanIntegerExpr := .add (206237, 2063) e35 e38
  let e40 : LowMeanIntegerExpr := .neg (-206237, 2063) e39
  let e41 : LowMeanIntegerExpr := .add (-1987913, 26819) e34 e40
  let e42 : LowMeanIntegerExpr := .mul (798, 29) e2 e22
  let e43 : LowMeanIntegerExpr := .neg (-798, 29) e42
  let e44 : LowMeanIntegerExpr := .add (4334599, 59827) e39 e43
  let e45 : LowMeanIntegerExpr := .maximum (4334599, 59827) e41 e44
  let e46 : LowMeanIntegerExpr := .maximum (4334599, 59827) e31 e45
  let e47 : LowMeanIntegerExpr := .pow (18788748490801, 3579269929) e46 2
  let e48 : LowMeanIntegerExpr := .mul (18788748490801, 17349830000000) e16 e47
  let e49 : LowMeanIntegerExpr := .neg (-18788748490801, 17349830000000) e48
  let e50 : LowMeanIntegerExpr := .add (-45284259982980770086924644980011613550908699169419870946830491575577933, 42153718830387427358503226212420652010903071551685251609141825600000000) e32 e49
  let e51 : LowMeanIntegerExpr := .neg (45284259982980770086924644980011613550908699169419870946830491575577933, 42153718830387427358503226212420652010903071551685251609141825600000000) e50
  e51

noncomputable def lowMeanRankExpr0517_147_b : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (0, 1)
  e0

noncomputable def lowMeanFiber0517 : LowMeanFiberInput :=
{ record := 517, certificate := 26, M := 42, zeta := (1, 100000), lo := -45, hi := 102,
  gL := (14170230266187585945600000000000000000000000, 4695452425098908797088971409337422035076128813), gR := (1754046785073550475326647311207601196182346961680000000000000, 26346074268992142099064516382762907506814419719803282255713641), core := [35],
  gLExpr := lowMeanFiberExpr0517_0, gRExpr := lowMeanFiberExpr0517_1,
  leftSide := lowMeanFiberExpr0517_2, rightSide := lowMeanFiberExpr0517_3,
  leftTail := lowMeanFiberExpr0517_4, rightTail := lowMeanFiberExpr0517_5,
  ranks := [{ j := -45, state := 0, first := lowMeanRankExpr0517_0_a, second := lowMeanRankExpr0517_0_b }, { j := -44, state := 0, first := lowMeanRankExpr0517_1_a, second := lowMeanRankExpr0517_1_b }, { j := -43, state := 0, first := lowMeanRankExpr0517_2_a, second := lowMeanRankExpr0517_2_b }, { j := -42, state := 0, first := lowMeanRankExpr0517_3_a, second := lowMeanRankExpr0517_3_b }, { j := -41, state := 0, first := lowMeanRankExpr0517_4_a, second := lowMeanRankExpr0517_4_b }, { j := -40, state := 0, first := lowMeanRankExpr0517_5_a, second := lowMeanRankExpr0517_5_b }, { j := -39, state := 0, first := lowMeanRankExpr0517_6_a, second := lowMeanRankExpr0517_6_b }, { j := -38, state := 0, first := lowMeanRankExpr0517_7_a, second := lowMeanRankExpr0517_7_b }, { j := -37, state := 0, first := lowMeanRankExpr0517_8_a, second := lowMeanRankExpr0517_8_b }, { j := -36, state := 0, first := lowMeanRankExpr0517_9_a, second := lowMeanRankExpr0517_9_b }, { j := -35, state := 0, first := lowMeanRankExpr0517_10_a, second := lowMeanRankExpr0517_10_b }, { j := -34, state := 0, first := lowMeanRankExpr0517_11_a, second := lowMeanRankExpr0517_11_b }, { j := -33, state := 0, first := lowMeanRankExpr0517_12_a, second := lowMeanRankExpr0517_12_b }, { j := -32, state := 0, first := lowMeanRankExpr0517_13_a, second := lowMeanRankExpr0517_13_b }, { j := -31, state := 0, first := lowMeanRankExpr0517_14_a, second := lowMeanRankExpr0517_14_b }, { j := -30, state := 0, first := lowMeanRankExpr0517_15_a, second := lowMeanRankExpr0517_15_b }, { j := -29, state := 0, first := lowMeanRankExpr0517_16_a, second := lowMeanRankExpr0517_16_b }, { j := -28, state := 0, first := lowMeanRankExpr0517_17_a, second := lowMeanRankExpr0517_17_b }, { j := -27, state := 0, first := lowMeanRankExpr0517_18_a, second := lowMeanRankExpr0517_18_b }, { j := -26, state := 0, first := lowMeanRankExpr0517_19_a, second := lowMeanRankExpr0517_19_b }, { j := -25, state := 0, first := lowMeanRankExpr0517_20_a, second := lowMeanRankExpr0517_20_b }, { j := -24, state := 0, first := lowMeanRankExpr0517_21_a, second := lowMeanRankExpr0517_21_b }, { j := -23, state := 0, first := lowMeanRankExpr0517_22_a, second := lowMeanRankExpr0517_22_b }, { j := -22, state := 0, first := lowMeanRankExpr0517_23_a, second := lowMeanRankExpr0517_23_b }, { j := -21, state := 0, first := lowMeanRankExpr0517_24_a, second := lowMeanRankExpr0517_24_b }, { j := -20, state := 0, first := lowMeanRankExpr0517_25_a, second := lowMeanRankExpr0517_25_b }, { j := -19, state := 0, first := lowMeanRankExpr0517_26_a, second := lowMeanRankExpr0517_26_b }, { j := -18, state := 0, first := lowMeanRankExpr0517_27_a, second := lowMeanRankExpr0517_27_b }, { j := -17, state := 0, first := lowMeanRankExpr0517_28_a, second := lowMeanRankExpr0517_28_b }, { j := -16, state := 0, first := lowMeanRankExpr0517_29_a, second := lowMeanRankExpr0517_29_b }, { j := -15, state := 0, first := lowMeanRankExpr0517_30_a, second := lowMeanRankExpr0517_30_b }, { j := -14, state := 0, first := lowMeanRankExpr0517_31_a, second := lowMeanRankExpr0517_31_b }, { j := -13, state := 0, first := lowMeanRankExpr0517_32_a, second := lowMeanRankExpr0517_32_b }, { j := -12, state := 0, first := lowMeanRankExpr0517_33_a, second := lowMeanRankExpr0517_33_b }, { j := -11, state := 0, first := lowMeanRankExpr0517_34_a, second := lowMeanRankExpr0517_34_b }, { j := -10, state := 0, first := lowMeanRankExpr0517_35_a, second := lowMeanRankExpr0517_35_b }, { j := -9, state := 0, first := lowMeanRankExpr0517_36_a, second := lowMeanRankExpr0517_36_b }, { j := -8, state := 0, first := lowMeanRankExpr0517_37_a, second := lowMeanRankExpr0517_37_b }, { j := -7, state := 0, first := lowMeanRankExpr0517_38_a, second := lowMeanRankExpr0517_38_b }, { j := -6, state := 0, first := lowMeanRankExpr0517_39_a, second := lowMeanRankExpr0517_39_b }, { j := -5, state := 0, first := lowMeanRankExpr0517_40_a, second := lowMeanRankExpr0517_40_b }, { j := -4, state := 0, first := lowMeanRankExpr0517_41_a, second := lowMeanRankExpr0517_41_b }, { j := -3, state := 0, first := lowMeanRankExpr0517_42_a, second := lowMeanRankExpr0517_42_b }, { j := -2, state := 0, first := lowMeanRankExpr0517_43_a, second := lowMeanRankExpr0517_43_b }, { j := -1, state := 0, first := lowMeanRankExpr0517_44_a, second := lowMeanRankExpr0517_44_b }, { j := 0, state := 0, first := lowMeanRankExpr0517_45_a, second := lowMeanRankExpr0517_45_b }, { j := 1, state := 0, first := lowMeanRankExpr0517_46_a, second := lowMeanRankExpr0517_46_b }, { j := 2, state := 0, first := lowMeanRankExpr0517_47_a, second := lowMeanRankExpr0517_47_b }, { j := 3, state := 0, first := lowMeanRankExpr0517_48_a, second := lowMeanRankExpr0517_48_b }, { j := 4, state := 0, first := lowMeanRankExpr0517_49_a, second := lowMeanRankExpr0517_49_b }, { j := 5, state := 0, first := lowMeanRankExpr0517_50_a, second := lowMeanRankExpr0517_50_b }, { j := 6, state := 0, first := lowMeanRankExpr0517_51_a, second := lowMeanRankExpr0517_51_b }, { j := 7, state := 0, first := lowMeanRankExpr0517_52_a, second := lowMeanRankExpr0517_52_b }, { j := 8, state := 0, first := lowMeanRankExpr0517_53_a, second := lowMeanRankExpr0517_53_b }, { j := 9, state := 0, first := lowMeanRankExpr0517_54_a, second := lowMeanRankExpr0517_54_b }, { j := 10, state := 0, first := lowMeanRankExpr0517_55_a, second := lowMeanRankExpr0517_55_b }, { j := 11, state := 0, first := lowMeanRankExpr0517_56_a, second := lowMeanRankExpr0517_56_b }, { j := 12, state := 0, first := lowMeanRankExpr0517_57_a, second := lowMeanRankExpr0517_57_b }, { j := 13, state := 0, first := lowMeanRankExpr0517_58_a, second := lowMeanRankExpr0517_58_b }, { j := 14, state := 0, first := lowMeanRankExpr0517_59_a, second := lowMeanRankExpr0517_59_b }, { j := 15, state := 0, first := lowMeanRankExpr0517_60_a, second := lowMeanRankExpr0517_60_b }, { j := 16, state := 0, first := lowMeanRankExpr0517_61_a, second := lowMeanRankExpr0517_61_b }, { j := 17, state := 0, first := lowMeanRankExpr0517_62_a, second := lowMeanRankExpr0517_62_b }, { j := 18, state := 0, first := lowMeanRankExpr0517_63_a, second := lowMeanRankExpr0517_63_b }, { j := 19, state := 0, first := lowMeanRankExpr0517_64_a, second := lowMeanRankExpr0517_64_b }, { j := 20, state := 0, first := lowMeanRankExpr0517_65_a, second := lowMeanRankExpr0517_65_b }, { j := 21, state := 0, first := lowMeanRankExpr0517_66_a, second := lowMeanRankExpr0517_66_b }, { j := 22, state := 1, first := lowMeanRankExpr0517_67_a, second := lowMeanRankExpr0517_67_b }, { j := 23, state := 1, first := lowMeanRankExpr0517_68_a, second := lowMeanRankExpr0517_68_b }, { j := 24, state := 1, first := lowMeanRankExpr0517_69_a, second := lowMeanRankExpr0517_69_b }, { j := 25, state := 1, first := lowMeanRankExpr0517_70_a, second := lowMeanRankExpr0517_70_b }, { j := 26, state := 1, first := lowMeanRankExpr0517_71_a, second := lowMeanRankExpr0517_71_b }, { j := 27, state := 1, first := lowMeanRankExpr0517_72_a, second := lowMeanRankExpr0517_72_b }, { j := 28, state := 1, first := lowMeanRankExpr0517_73_a, second := lowMeanRankExpr0517_73_b }, { j := 29, state := 1, first := lowMeanRankExpr0517_74_a, second := lowMeanRankExpr0517_74_b }, { j := 30, state := 1, first := lowMeanRankExpr0517_75_a, second := lowMeanRankExpr0517_75_b }, { j := 31, state := 1, first := lowMeanRankExpr0517_76_a, second := lowMeanRankExpr0517_76_b }, { j := 32, state := 1, first := lowMeanRankExpr0517_77_a, second := lowMeanRankExpr0517_77_b }, { j := 33, state := 1, first := lowMeanRankExpr0517_78_a, second := lowMeanRankExpr0517_78_b }, { j := 34, state := 1, first := lowMeanRankExpr0517_79_a, second := lowMeanRankExpr0517_79_b }, { j := 35, state := 2, first := lowMeanRankExpr0517_80_a, second := lowMeanRankExpr0517_80_b }, { j := 36, state := 1, first := lowMeanRankExpr0517_81_a, second := lowMeanRankExpr0517_81_b }, { j := 37, state := 0, first := lowMeanRankExpr0517_82_a, second := lowMeanRankExpr0517_82_b }, { j := 38, state := 0, first := lowMeanRankExpr0517_83_a, second := lowMeanRankExpr0517_83_b }, { j := 39, state := 0, first := lowMeanRankExpr0517_84_a, second := lowMeanRankExpr0517_84_b }, { j := 40, state := 0, first := lowMeanRankExpr0517_85_a, second := lowMeanRankExpr0517_85_b }, { j := 41, state := 0, first := lowMeanRankExpr0517_86_a, second := lowMeanRankExpr0517_86_b }, { j := 42, state := 0, first := lowMeanRankExpr0517_87_a, second := lowMeanRankExpr0517_87_b }, { j := 43, state := 0, first := lowMeanRankExpr0517_88_a, second := lowMeanRankExpr0517_88_b }, { j := 44, state := 0, first := lowMeanRankExpr0517_89_a, second := lowMeanRankExpr0517_89_b }, { j := 45, state := 0, first := lowMeanRankExpr0517_90_a, second := lowMeanRankExpr0517_90_b }, { j := 46, state := 0, first := lowMeanRankExpr0517_91_a, second := lowMeanRankExpr0517_91_b }, { j := 47, state := 0, first := lowMeanRankExpr0517_92_a, second := lowMeanRankExpr0517_92_b }, { j := 48, state := 0, first := lowMeanRankExpr0517_93_a, second := lowMeanRankExpr0517_93_b }, { j := 49, state := 0, first := lowMeanRankExpr0517_94_a, second := lowMeanRankExpr0517_94_b }, { j := 50, state := 0, first := lowMeanRankExpr0517_95_a, second := lowMeanRankExpr0517_95_b }, { j := 51, state := 0, first := lowMeanRankExpr0517_96_a, second := lowMeanRankExpr0517_96_b }, { j := 52, state := 0, first := lowMeanRankExpr0517_97_a, second := lowMeanRankExpr0517_97_b }, { j := 53, state := 0, first := lowMeanRankExpr0517_98_a, second := lowMeanRankExpr0517_98_b }, { j := 54, state := 0, first := lowMeanRankExpr0517_99_a, second := lowMeanRankExpr0517_99_b }, { j := 55, state := 0, first := lowMeanRankExpr0517_100_a, second := lowMeanRankExpr0517_100_b }, { j := 56, state := 0, first := lowMeanRankExpr0517_101_a, second := lowMeanRankExpr0517_101_b }, { j := 57, state := 0, first := lowMeanRankExpr0517_102_a, second := lowMeanRankExpr0517_102_b }, { j := 58, state := 0, first := lowMeanRankExpr0517_103_a, second := lowMeanRankExpr0517_103_b }, { j := 59, state := 0, first := lowMeanRankExpr0517_104_a, second := lowMeanRankExpr0517_104_b }, { j := 60, state := 0, first := lowMeanRankExpr0517_105_a, second := lowMeanRankExpr0517_105_b }, { j := 61, state := 0, first := lowMeanRankExpr0517_106_a, second := lowMeanRankExpr0517_106_b }, { j := 62, state := 0, first := lowMeanRankExpr0517_107_a, second := lowMeanRankExpr0517_107_b }, { j := 63, state := 0, first := lowMeanRankExpr0517_108_a, second := lowMeanRankExpr0517_108_b }, { j := 64, state := 0, first := lowMeanRankExpr0517_109_a, second := lowMeanRankExpr0517_109_b }, { j := 65, state := 0, first := lowMeanRankExpr0517_110_a, second := lowMeanRankExpr0517_110_b }, { j := 66, state := 0, first := lowMeanRankExpr0517_111_a, second := lowMeanRankExpr0517_111_b }, { j := 67, state := 0, first := lowMeanRankExpr0517_112_a, second := lowMeanRankExpr0517_112_b }, { j := 68, state := 0, first := lowMeanRankExpr0517_113_a, second := lowMeanRankExpr0517_113_b }, { j := 69, state := 0, first := lowMeanRankExpr0517_114_a, second := lowMeanRankExpr0517_114_b }, { j := 70, state := 0, first := lowMeanRankExpr0517_115_a, second := lowMeanRankExpr0517_115_b }, { j := 71, state := 0, first := lowMeanRankExpr0517_116_a, second := lowMeanRankExpr0517_116_b }, { j := 72, state := 0, first := lowMeanRankExpr0517_117_a, second := lowMeanRankExpr0517_117_b }, { j := 73, state := 0, first := lowMeanRankExpr0517_118_a, second := lowMeanRankExpr0517_118_b }, { j := 74, state := 0, first := lowMeanRankExpr0517_119_a, second := lowMeanRankExpr0517_119_b }, { j := 75, state := 0, first := lowMeanRankExpr0517_120_a, second := lowMeanRankExpr0517_120_b }, { j := 76, state := 0, first := lowMeanRankExpr0517_121_a, second := lowMeanRankExpr0517_121_b }, { j := 77, state := 0, first := lowMeanRankExpr0517_122_a, second := lowMeanRankExpr0517_122_b }, { j := 78, state := 0, first := lowMeanRankExpr0517_123_a, second := lowMeanRankExpr0517_123_b }, { j := 79, state := 0, first := lowMeanRankExpr0517_124_a, second := lowMeanRankExpr0517_124_b }, { j := 80, state := 0, first := lowMeanRankExpr0517_125_a, second := lowMeanRankExpr0517_125_b }, { j := 81, state := 0, first := lowMeanRankExpr0517_126_a, second := lowMeanRankExpr0517_126_b }, { j := 82, state := 0, first := lowMeanRankExpr0517_127_a, second := lowMeanRankExpr0517_127_b }, { j := 83, state := 0, first := lowMeanRankExpr0517_128_a, second := lowMeanRankExpr0517_128_b }, { j := 84, state := 0, first := lowMeanRankExpr0517_129_a, second := lowMeanRankExpr0517_129_b }, { j := 85, state := 0, first := lowMeanRankExpr0517_130_a, second := lowMeanRankExpr0517_130_b }, { j := 86, state := 0, first := lowMeanRankExpr0517_131_a, second := lowMeanRankExpr0517_131_b }, { j := 87, state := 0, first := lowMeanRankExpr0517_132_a, second := lowMeanRankExpr0517_132_b }, { j := 88, state := 0, first := lowMeanRankExpr0517_133_a, second := lowMeanRankExpr0517_133_b }, { j := 89, state := 0, first := lowMeanRankExpr0517_134_a, second := lowMeanRankExpr0517_134_b }, { j := 90, state := 0, first := lowMeanRankExpr0517_135_a, second := lowMeanRankExpr0517_135_b }, { j := 91, state := 0, first := lowMeanRankExpr0517_136_a, second := lowMeanRankExpr0517_136_b }, { j := 92, state := 0, first := lowMeanRankExpr0517_137_a, second := lowMeanRankExpr0517_137_b }, { j := 93, state := 0, first := lowMeanRankExpr0517_138_a, second := lowMeanRankExpr0517_138_b }, { j := 94, state := 0, first := lowMeanRankExpr0517_139_a, second := lowMeanRankExpr0517_139_b }, { j := 95, state := 0, first := lowMeanRankExpr0517_140_a, second := lowMeanRankExpr0517_140_b }, { j := 96, state := 0, first := lowMeanRankExpr0517_141_a, second := lowMeanRankExpr0517_141_b }, { j := 97, state := 0, first := lowMeanRankExpr0517_142_a, second := lowMeanRankExpr0517_142_b }, { j := 98, state := 0, first := lowMeanRankExpr0517_143_a, second := lowMeanRankExpr0517_143_b }, { j := 99, state := 0, first := lowMeanRankExpr0517_144_a, second := lowMeanRankExpr0517_144_b }, { j := 100, state := 0, first := lowMeanRankExpr0517_145_a, second := lowMeanRankExpr0517_145_b }, { j := 101, state := 0, first := lowMeanRankExpr0517_146_a, second := lowMeanRankExpr0517_146_b }, { j := 102, state := 0, first := lowMeanRankExpr0517_147_a, second := lowMeanRankExpr0517_147_b }] }

noncomputable def lowMeanFiberGroup0517 : List LowMeanFiberInput := [lowMeanFiber0517]

end Erdos993Lean.Analytic.V213
