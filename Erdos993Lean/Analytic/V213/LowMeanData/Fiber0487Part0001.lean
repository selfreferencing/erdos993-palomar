module

public import Erdos993Lean.Analytic.V213.LowMeanCoreChecker
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0473
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0487Part0000
public import Erdos993Lean.Analytic.V213.LowMeanIntegerExpr
public import Erdos993Lean.Ceiling.Prefix
public import Erdos993Lean.Ceiling.Statement


/-! Direct-fiber core witnesses with explicit complete integer windows. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanRankExpr0488_119_a : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e1 : LowMeanIntegerExpr := .atom (26, 78125)
  let e2 : LowMeanIntegerExpr := .atom (13, 1)
  let e3 : LowMeanIntegerExpr := .atom (189, 4)
  let e4 : LowMeanIntegerExpr := .neg (-189, 4) e3
  let e5 : LowMeanIntegerExpr := .add (-137, 4) e2 e4
  let e6 : LowMeanIntegerExpr := .mul (-1781, 156250) e1 e5
  let e7 : LowMeanIntegerExpr := .add (-14847, 10000000) e0 e6
  let e8 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e9 : LowMeanIntegerExpr := .pow (18769, 16) e5 2
  let e10 : LowMeanIntegerExpr := .mul (24268317, 1600000000) e8 e9
  let e11 : LowMeanIntegerExpr := .neg (-24268317, 1600000000) e10
  let e12 : LowMeanIntegerExpr := .add (-26643837, 1600000000) e7 e11
  let e13 : LowMeanIntegerExpr := .atom (-4189, 5000000)
  let e14 : LowMeanIntegerExpr := .pow (17547721, 25000000000000) e13 2
  let e15 : LowMeanIntegerExpr := .atom (4, 1)
  let e16 : LowMeanIntegerExpr := .atom (2063, 10000000)
  let e17 : LowMeanIntegerExpr := .mul (2063, 2500000) e15 e16
  let e18 : LowMeanIntegerExpr := .div (17547721, 20630000000) e14 e17
  let e19 : LowMeanIntegerExpr := .add (-52158600371, 3300800000000) e12 e18
  let e20 : LowMeanIntegerExpr := .atom (328000, 1)
  let e21 : LowMeanIntegerExpr := .atom (1, 1)
  let e22 : LowMeanIntegerExpr := .atom (19, 29)
  let e23 : LowMeanIntegerExpr := .neg (-19, 29) e22
  let e24 : LowMeanIntegerExpr := .add (10, 29) e21 e23
  let e25 : LowMeanIntegerExpr := .pow (10000000000000, 10260628712958602189) e24 13
  let e26 : LowMeanIntegerExpr := .mul (3280000000000000000, 10260628712958602189) e20 e25
  let e27 : LowMeanIntegerExpr := .neg (-3280000000000000000, 10260628712958602189) e26
  let e28 : LowMeanIntegerExpr := .add (-11361804032594415800642816812119, 33868283255733754105451200000000) e19 e27
  let e29 : LowMeanIntegerExpr := .atom (1, 100000)
  let e30 : LowMeanIntegerExpr := .add (-11361465349761858463101762300119, 33868283255733754105451200000000) e28 e29
  let e31 : LowMeanIntegerExpr := .atom (0, 1)
  let e32 : LowMeanIntegerExpr := .add (-11361465349761858463101762300119, 33868283255733754105451200000000) e30 e31
  let e33 : LowMeanIntegerExpr := .atom (8, 13)
  let e34 : LowMeanIntegerExpr := .mul (8, 1) e2 e33
  let e35 : LowMeanIntegerExpr := .atom (70, 1)
  let e36 : LowMeanIntegerExpr := .atom (2, 1)
  let e37 : LowMeanIntegerExpr := .mul (2063, 5000000) e36 e16
  let e38 : LowMeanIntegerExpr := .div (-4189, 2063) e13 e37
  let e39 : LowMeanIntegerExpr := .add (140221, 2063) e35 e38
  let e40 : LowMeanIntegerExpr := .neg (-140221, 2063) e39
  let e41 : LowMeanIntegerExpr := .add (-123717, 2063) e34 e40
  let e42 : LowMeanIntegerExpr := .mul (247, 29) e2 e22
  let e43 : LowMeanIntegerExpr := .neg (-247, 29) e42
  let e44 : LowMeanIntegerExpr := .add (3556848, 59827) e39 e43
  let e45 : LowMeanIntegerExpr := .maximum (3556848, 59827) e41 e44
  let e46 : LowMeanIntegerExpr := .maximum (3556848, 59827) e31 e45
  let e47 : LowMeanIntegerExpr := .pow (12651167695104, 3579269929) e46 2
  let e48 : LowMeanIntegerExpr := .mul (98837247618, 135545546875) e16 e47
  let e49 : LowMeanIntegerExpr := .neg (-98837247618, 135545546875) e48
  let e50 : LowMeanIntegerExpr := .add (-17478224213104028783558978233, 16417005940733763502400000000) e32 e49
  let e51 : LowMeanIntegerExpr := .neg (17478224213104028783558978233, 16417005940733763502400000000) e50
  e51

noncomputable def lowMeanRankExpr0488_119_b : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (0, 1)
  e0

noncomputable def lowMeanFiber0488 : LowMeanFiberInput :=
{ record := 488, certificate := 26, M := 13, zeta := (1, 100000), lo := -49, hi := 70,
  gL := (675840000000, 23298085122481), gR := (1384330223471910000, 10260628712958602189), core := [],
  gLExpr := lowMeanFiberExpr0488_0, gRExpr := lowMeanFiberExpr0488_1,
  leftSide := lowMeanFiberExpr0488_2, rightSide := lowMeanFiberExpr0488_3,
  leftTail := lowMeanFiberExpr0488_4, rightTail := lowMeanFiberExpr0488_5,
  ranks := [{ j := -49, state := 0, first := lowMeanRankExpr0488_0_a, second := lowMeanRankExpr0488_0_b }, { j := -48, state := 0, first := lowMeanRankExpr0488_1_a, second := lowMeanRankExpr0488_1_b }, { j := -47, state := 0, first := lowMeanRankExpr0488_2_a, second := lowMeanRankExpr0488_2_b }, { j := -46, state := 0, first := lowMeanRankExpr0488_3_a, second := lowMeanRankExpr0488_3_b }, { j := -45, state := 0, first := lowMeanRankExpr0488_4_a, second := lowMeanRankExpr0488_4_b }, { j := -44, state := 0, first := lowMeanRankExpr0488_5_a, second := lowMeanRankExpr0488_5_b }, { j := -43, state := 0, first := lowMeanRankExpr0488_6_a, second := lowMeanRankExpr0488_6_b }, { j := -42, state := 0, first := lowMeanRankExpr0488_7_a, second := lowMeanRankExpr0488_7_b }, { j := -41, state := 0, first := lowMeanRankExpr0488_8_a, second := lowMeanRankExpr0488_8_b }, { j := -40, state := 0, first := lowMeanRankExpr0488_9_a, second := lowMeanRankExpr0488_9_b }, { j := -39, state := 0, first := lowMeanRankExpr0488_10_a, second := lowMeanRankExpr0488_10_b }, { j := -38, state := 0, first := lowMeanRankExpr0488_11_a, second := lowMeanRankExpr0488_11_b }, { j := -37, state := 0, first := lowMeanRankExpr0488_12_a, second := lowMeanRankExpr0488_12_b }, { j := -36, state := 0, first := lowMeanRankExpr0488_13_a, second := lowMeanRankExpr0488_13_b }, { j := -35, state := 0, first := lowMeanRankExpr0488_14_a, second := lowMeanRankExpr0488_14_b }, { j := -34, state := 0, first := lowMeanRankExpr0488_15_a, second := lowMeanRankExpr0488_15_b }, { j := -33, state := 0, first := lowMeanRankExpr0488_16_a, second := lowMeanRankExpr0488_16_b }, { j := -32, state := 0, first := lowMeanRankExpr0488_17_a, second := lowMeanRankExpr0488_17_b }, { j := -31, state := 0, first := lowMeanRankExpr0488_18_a, second := lowMeanRankExpr0488_18_b }, { j := -30, state := 0, first := lowMeanRankExpr0488_19_a, second := lowMeanRankExpr0488_19_b }, { j := -29, state := 0, first := lowMeanRankExpr0488_20_a, second := lowMeanRankExpr0488_20_b }, { j := -28, state := 0, first := lowMeanRankExpr0488_21_a, second := lowMeanRankExpr0488_21_b }, { j := -27, state := 0, first := lowMeanRankExpr0488_22_a, second := lowMeanRankExpr0488_22_b }, { j := -26, state := 0, first := lowMeanRankExpr0488_23_a, second := lowMeanRankExpr0488_23_b }, { j := -25, state := 0, first := lowMeanRankExpr0488_24_a, second := lowMeanRankExpr0488_24_b }, { j := -24, state := 0, first := lowMeanRankExpr0488_25_a, second := lowMeanRankExpr0488_25_b }, { j := -23, state := 0, first := lowMeanRankExpr0488_26_a, second := lowMeanRankExpr0488_26_b }, { j := -22, state := 0, first := lowMeanRankExpr0488_27_a, second := lowMeanRankExpr0488_27_b }, { j := -21, state := 0, first := lowMeanRankExpr0488_28_a, second := lowMeanRankExpr0488_28_b }, { j := -20, state := 0, first := lowMeanRankExpr0488_29_a, second := lowMeanRankExpr0488_29_b }, { j := -19, state := 0, first := lowMeanRankExpr0488_30_a, second := lowMeanRankExpr0488_30_b }, { j := -18, state := 0, first := lowMeanRankExpr0488_31_a, second := lowMeanRankExpr0488_31_b }, { j := -17, state := 0, first := lowMeanRankExpr0488_32_a, second := lowMeanRankExpr0488_32_b }, { j := -16, state := 0, first := lowMeanRankExpr0488_33_a, second := lowMeanRankExpr0488_33_b }, { j := -15, state := 0, first := lowMeanRankExpr0488_34_a, second := lowMeanRankExpr0488_34_b }, { j := -14, state := 0, first := lowMeanRankExpr0488_35_a, second := lowMeanRankExpr0488_35_b }, { j := -13, state := 0, first := lowMeanRankExpr0488_36_a, second := lowMeanRankExpr0488_36_b }, { j := -12, state := 0, first := lowMeanRankExpr0488_37_a, second := lowMeanRankExpr0488_37_b }, { j := -11, state := 0, first := lowMeanRankExpr0488_38_a, second := lowMeanRankExpr0488_38_b }, { j := -10, state := 0, first := lowMeanRankExpr0488_39_a, second := lowMeanRankExpr0488_39_b }, { j := -9, state := 0, first := lowMeanRankExpr0488_40_a, second := lowMeanRankExpr0488_40_b }, { j := -8, state := 0, first := lowMeanRankExpr0488_41_a, second := lowMeanRankExpr0488_41_b }, { j := -7, state := 0, first := lowMeanRankExpr0488_42_a, second := lowMeanRankExpr0488_42_b }, { j := -6, state := 0, first := lowMeanRankExpr0488_43_a, second := lowMeanRankExpr0488_43_b }, { j := -5, state := 0, first := lowMeanRankExpr0488_44_a, second := lowMeanRankExpr0488_44_b }, { j := -4, state := 0, first := lowMeanRankExpr0488_45_a, second := lowMeanRankExpr0488_45_b }, { j := -3, state := 0, first := lowMeanRankExpr0488_46_a, second := lowMeanRankExpr0488_46_b }, { j := -2, state := 0, first := lowMeanRankExpr0488_47_a, second := lowMeanRankExpr0488_47_b }, { j := -1, state := 0, first := lowMeanRankExpr0488_48_a, second := lowMeanRankExpr0488_48_b }, { j := 0, state := 0, first := lowMeanRankExpr0488_49_a, second := lowMeanRankExpr0488_49_b }, { j := 1, state := 0, first := lowMeanRankExpr0488_50_a, second := lowMeanRankExpr0488_50_b }, { j := 2, state := 0, first := lowMeanRankExpr0488_51_a, second := lowMeanRankExpr0488_51_b }, { j := 3, state := 0, first := lowMeanRankExpr0488_52_a, second := lowMeanRankExpr0488_52_b }, { j := 4, state := 0, first := lowMeanRankExpr0488_53_a, second := lowMeanRankExpr0488_53_b }, { j := 5, state := 0, first := lowMeanRankExpr0488_54_a, second := lowMeanRankExpr0488_54_b }, { j := 6, state := 0, first := lowMeanRankExpr0488_55_a, second := lowMeanRankExpr0488_55_b }, { j := 7, state := 0, first := lowMeanRankExpr0488_56_a, second := lowMeanRankExpr0488_56_b }, { j := 8, state := 0, first := lowMeanRankExpr0488_57_a, second := lowMeanRankExpr0488_57_b }, { j := 9, state := 0, first := lowMeanRankExpr0488_58_a, second := lowMeanRankExpr0488_58_b }, { j := 10, state := 0, first := lowMeanRankExpr0488_59_a, second := lowMeanRankExpr0488_59_b }, { j := 11, state := 0, first := lowMeanRankExpr0488_60_a, second := lowMeanRankExpr0488_60_b }, { j := 12, state := 0, first := lowMeanRankExpr0488_61_a, second := lowMeanRankExpr0488_61_b }, { j := 13, state := 0, first := lowMeanRankExpr0488_62_a, second := lowMeanRankExpr0488_62_b }, { j := 14, state := 0, first := lowMeanRankExpr0488_63_a, second := lowMeanRankExpr0488_63_b }, { j := 15, state := 0, first := lowMeanRankExpr0488_64_a, second := lowMeanRankExpr0488_64_b }, { j := 16, state := 0, first := lowMeanRankExpr0488_65_a, second := lowMeanRankExpr0488_65_b }, { j := 17, state := 0, first := lowMeanRankExpr0488_66_a, second := lowMeanRankExpr0488_66_b }, { j := 18, state := 0, first := lowMeanRankExpr0488_67_a, second := lowMeanRankExpr0488_67_b }, { j := 19, state := 0, first := lowMeanRankExpr0488_68_a, second := lowMeanRankExpr0488_68_b }, { j := 20, state := 0, first := lowMeanRankExpr0488_69_a, second := lowMeanRankExpr0488_69_b }, { j := 21, state := 0, first := lowMeanRankExpr0488_70_a, second := lowMeanRankExpr0488_70_b }, { j := 22, state := 0, first := lowMeanRankExpr0488_71_a, second := lowMeanRankExpr0488_71_b }, { j := 23, state := 0, first := lowMeanRankExpr0488_72_a, second := lowMeanRankExpr0488_72_b }, { j := 24, state := 0, first := lowMeanRankExpr0488_73_a, second := lowMeanRankExpr0488_73_b }, { j := 25, state := 0, first := lowMeanRankExpr0488_74_a, second := lowMeanRankExpr0488_74_b }, { j := 26, state := 0, first := lowMeanRankExpr0488_75_a, second := lowMeanRankExpr0488_75_b }, { j := 27, state := 0, first := lowMeanRankExpr0488_76_a, second := lowMeanRankExpr0488_76_b }, { j := 28, state := 0, first := lowMeanRankExpr0488_77_a, second := lowMeanRankExpr0488_77_b }, { j := 29, state := 0, first := lowMeanRankExpr0488_78_a, second := lowMeanRankExpr0488_78_b }, { j := 30, state := 0, first := lowMeanRankExpr0488_79_a, second := lowMeanRankExpr0488_79_b }, { j := 31, state := 0, first := lowMeanRankExpr0488_80_a, second := lowMeanRankExpr0488_80_b }, { j := 32, state := 0, first := lowMeanRankExpr0488_81_a, second := lowMeanRankExpr0488_81_b }, { j := 33, state := 0, first := lowMeanRankExpr0488_82_a, second := lowMeanRankExpr0488_82_b }, { j := 34, state := 0, first := lowMeanRankExpr0488_83_a, second := lowMeanRankExpr0488_83_b }, { j := 35, state := 0, first := lowMeanRankExpr0488_84_a, second := lowMeanRankExpr0488_84_b }, { j := 36, state := 0, first := lowMeanRankExpr0488_85_a, second := lowMeanRankExpr0488_85_b }, { j := 37, state := 0, first := lowMeanRankExpr0488_86_a, second := lowMeanRankExpr0488_86_b }, { j := 38, state := 0, first := lowMeanRankExpr0488_87_a, second := lowMeanRankExpr0488_87_b }, { j := 39, state := 0, first := lowMeanRankExpr0488_88_a, second := lowMeanRankExpr0488_88_b }, { j := 40, state := 0, first := lowMeanRankExpr0488_89_a, second := lowMeanRankExpr0488_89_b }, { j := 41, state := 0, first := lowMeanRankExpr0488_90_a, second := lowMeanRankExpr0488_90_b }, { j := 42, state := 0, first := lowMeanRankExpr0488_91_a, second := lowMeanRankExpr0488_91_b }, { j := 43, state := 0, first := lowMeanRankExpr0488_92_a, second := lowMeanRankExpr0488_92_b }, { j := 44, state := 0, first := lowMeanRankExpr0488_93_a, second := lowMeanRankExpr0488_93_b }, { j := 45, state := 0, first := lowMeanRankExpr0488_94_a, second := lowMeanRankExpr0488_94_b }, { j := 46, state := 0, first := lowMeanRankExpr0488_95_a, second := lowMeanRankExpr0488_95_b }, { j := 47, state := 0, first := lowMeanRankExpr0488_96_a, second := lowMeanRankExpr0488_96_b }, { j := 48, state := 0, first := lowMeanRankExpr0488_97_a, second := lowMeanRankExpr0488_97_b }, { j := 49, state := 0, first := lowMeanRankExpr0488_98_a, second := lowMeanRankExpr0488_98_b }, { j := 50, state := 0, first := lowMeanRankExpr0488_99_a, second := lowMeanRankExpr0488_99_b }, { j := 51, state := 0, first := lowMeanRankExpr0488_100_a, second := lowMeanRankExpr0488_100_b }, { j := 52, state := 0, first := lowMeanRankExpr0488_101_a, second := lowMeanRankExpr0488_101_b }, { j := 53, state := 0, first := lowMeanRankExpr0488_102_a, second := lowMeanRankExpr0488_102_b }, { j := 54, state := 0, first := lowMeanRankExpr0488_103_a, second := lowMeanRankExpr0488_103_b }, { j := 55, state := 0, first := lowMeanRankExpr0488_104_a, second := lowMeanRankExpr0488_104_b }, { j := 56, state := 0, first := lowMeanRankExpr0488_105_a, second := lowMeanRankExpr0488_105_b }, { j := 57, state := 0, first := lowMeanRankExpr0488_106_a, second := lowMeanRankExpr0488_106_b }, { j := 58, state := 0, first := lowMeanRankExpr0488_107_a, second := lowMeanRankExpr0488_107_b }, { j := 59, state := 0, first := lowMeanRankExpr0488_108_a, second := lowMeanRankExpr0488_108_b }, { j := 60, state := 0, first := lowMeanRankExpr0488_109_a, second := lowMeanRankExpr0488_109_b }, { j := 61, state := 0, first := lowMeanRankExpr0488_110_a, second := lowMeanRankExpr0488_110_b }, { j := 62, state := 0, first := lowMeanRankExpr0488_111_a, second := lowMeanRankExpr0488_111_b }, { j := 63, state := 0, first := lowMeanRankExpr0488_112_a, second := lowMeanRankExpr0488_112_b }, { j := 64, state := 0, first := lowMeanRankExpr0488_113_a, second := lowMeanRankExpr0488_113_b }, { j := 65, state := 0, first := lowMeanRankExpr0488_114_a, second := lowMeanRankExpr0488_114_b }, { j := 66, state := 0, first := lowMeanRankExpr0488_115_a, second := lowMeanRankExpr0488_115_b }, { j := 67, state := 0, first := lowMeanRankExpr0488_116_a, second := lowMeanRankExpr0488_116_b }, { j := 68, state := 0, first := lowMeanRankExpr0488_117_a, second := lowMeanRankExpr0488_117_b }, { j := 69, state := 0, first := lowMeanRankExpr0488_118_a, second := lowMeanRankExpr0488_118_b }, { j := 70, state := 0, first := lowMeanRankExpr0488_119_a, second := lowMeanRankExpr0488_119_b }] }

noncomputable def lowMeanFiberGroup0487 : List LowMeanFiberInput := [lowMeanFiber0487, lowMeanFiber0488]

end Erdos993Lean.Analytic.V213
