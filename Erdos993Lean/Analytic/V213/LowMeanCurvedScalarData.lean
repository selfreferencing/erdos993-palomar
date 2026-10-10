module

public import Erdos993Lean.Analytic.V213.LowMeanScalarData
public import Erdos993Lean.Analytic.V213.LowMeanCurvedScalarShape

/-! Reviewed curved sign and ratio-floor Int/Nat witness data. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

def lowMeanCurvedExpr0 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (4, 1)
  let e1 : LowMeanIntegerExpr := .atom (5511, 1000000)
  let e2 : LowMeanIntegerExpr := .mul (5511, 250000) e0 e1
  let e3 : LowMeanIntegerExpr := .atom (1, 1)
  let e4 : LowMeanIntegerExpr := .mul (5511, 250000) e2 e3
  let e5 : LowMeanIntegerExpr := .atom (1, 4)
  let e6 : LowMeanIntegerExpr := .pow (1, 64) e5 3
  let e7 : LowMeanIntegerExpr := .mul (5511, 16000000) e4 e6
  let e8 : LowMeanIntegerExpr := .atom (4183, 5000000)
  let e9 : LowMeanIntegerExpr := .mul (4183, 1250000) e0 e8
  let e10 : LowMeanIntegerExpr := .atom (8, 1)
  let e11 : LowMeanIntegerExpr := .atom (327, 6250000)
  let e12 : LowMeanIntegerExpr := .mul (327, 781250) e10 e11
  let e13 : LowMeanIntegerExpr := .atom (121, 4)
  let e14 : LowMeanIntegerExpr := .mul (39567, 3125000) e12 e13
  let e15 : LowMeanIntegerExpr := .add (100049, 6250000) e9 e14
  let e16 : LowMeanIntegerExpr := .mul (327, 1562500) e0 e11
  let e17 : LowMeanIntegerExpr := .atom (6, 5)
  let e18 : LowMeanIntegerExpr := .mul (981, 3906250) e16 e17
  let e19 : LowMeanIntegerExpr := .neg (-981, 3906250) e18
  let e20 : LowMeanIntegerExpr := .add (492397, 31250000) e15 e19
  let e21 : LowMeanIntegerExpr := .mul (492397, 125000000) e20 e5
  let e22 : LowMeanIntegerExpr := .neg (-492397, 125000000) e21
  let e23 : LowMeanIntegerExpr := .add (-7189477, 2000000000) e7 e22
  let e24 : LowMeanIntegerExpr := .atom (32, 1)
  let e25 : LowMeanIntegerExpr := .mul (654, 390625) e24 e11
  let e26 : LowMeanIntegerExpr := .add (-3840997, 2000000000) e23 e25
  e26

def lowMeanCurvedExpr1 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (4, 1)
  let e1 : LowMeanIntegerExpr := .atom (5511, 1000000)
  let e2 : LowMeanIntegerExpr := .mul (5511, 250000) e0 e1
  let e3 : LowMeanIntegerExpr := .atom (1, 1)
  let e4 : LowMeanIntegerExpr := .mul (5511, 250000) e2 e3
  let e5 : LowMeanIntegerExpr := .atom (3, 8)
  let e6 : LowMeanIntegerExpr := .pow (27, 512) e5 3
  let e7 : LowMeanIntegerExpr := .mul (148797, 128000000) e4 e6
  let e8 : LowMeanIntegerExpr := .atom (4183, 5000000)
  let e9 : LowMeanIntegerExpr := .mul (4183, 1250000) e0 e8
  let e10 : LowMeanIntegerExpr := .atom (8, 1)
  let e11 : LowMeanIntegerExpr := .atom (327, 6250000)
  let e12 : LowMeanIntegerExpr := .mul (327, 781250) e10 e11
  let e13 : LowMeanIntegerExpr := .atom (121, 4)
  let e14 : LowMeanIntegerExpr := .mul (39567, 3125000) e12 e13
  let e15 : LowMeanIntegerExpr := .add (100049, 6250000) e9 e14
  let e16 : LowMeanIntegerExpr := .mul (327, 1562500) e0 e11
  let e17 : LowMeanIntegerExpr := .atom (6, 5)
  let e18 : LowMeanIntegerExpr := .mul (981, 3906250) e16 e17
  let e19 : LowMeanIntegerExpr := .neg (-981, 3906250) e18
  let e20 : LowMeanIntegerExpr := .add (492397, 31250000) e15 e19
  let e21 : LowMeanIntegerExpr := .mul (1477191, 250000000) e20 e5
  let e22 : LowMeanIntegerExpr := .neg (-1477191, 250000000) e21
  let e23 : LowMeanIntegerExpr := .add (-75940599, 16000000000) e7 e22
  let e24 : LowMeanIntegerExpr := .atom (32, 1)
  let e25 : LowMeanIntegerExpr := .mul (654, 390625) e24 e11
  let e26 : LowMeanIntegerExpr := .add (-49152759, 16000000000) e23 e25
  e26

def lowMeanCurvedExpr2 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (4, 1)
  let e1 : LowMeanIntegerExpr := .atom (973, 12500)
  let e2 : LowMeanIntegerExpr := .mul (973, 3125) e0 e1
  let e3 : LowMeanIntegerExpr := .atom (7, 10)
  let e4 : LowMeanIntegerExpr := .mul (6811, 31250) e2 e3
  let e5 : LowMeanIntegerExpr := .atom (3, 8)
  let e6 : LowMeanIntegerExpr := .pow (27, 512) e5 3
  let e7 : LowMeanIntegerExpr := .mul (183897, 16000000) e4 e6
  let e8 : LowMeanIntegerExpr := .atom (1837, 1000000)
  let e9 : LowMeanIntegerExpr := .mul (1837, 250000) e0 e8
  let e10 : LowMeanIntegerExpr := .atom (8, 1)
  let e11 : LowMeanIntegerExpr := .atom (691, 500000)
  let e12 : LowMeanIntegerExpr := .mul (691, 62500) e10 e11
  let e13 : LowMeanIntegerExpr := .atom (15, 1)
  let e14 : LowMeanIntegerExpr := .mul (2073, 12500) e12 e13
  let e15 : LowMeanIntegerExpr := .add (43297, 250000) e9 e14
  let e16 : LowMeanIntegerExpr := .mul (691, 125000) e0 e11
  let e17 : LowMeanIntegerExpr := .atom (6, 5)
  let e18 : LowMeanIntegerExpr := .mul (2073, 312500) e16 e17
  let e19 : LowMeanIntegerExpr := .neg (-2073, 312500) e18
  let e20 : LowMeanIntegerExpr := .add (208193, 1250000) e15 e19
  let e21 : LowMeanIntegerExpr := .mul (624579, 10000000) e20 e5
  let e22 : LowMeanIntegerExpr := .neg (-624579, 10000000) e21
  let e23 : LowMeanIntegerExpr := .add (-4077147, 80000000) e7 e22
  let e24 : LowMeanIntegerExpr := .atom (32, 1)
  let e25 : LowMeanIntegerExpr := .mul (691, 15625) e24 e11
  let e26 : LowMeanIntegerExpr := .add (-539227, 80000000) e23 e25
  e26

def lowMeanCurvedExpr3 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (4, 1)
  let e1 : LowMeanIntegerExpr := .atom (973, 12500)
  let e2 : LowMeanIntegerExpr := .mul (973, 3125) e0 e1
  let e3 : LowMeanIntegerExpr := .atom (7, 10)
  let e4 : LowMeanIntegerExpr := .mul (6811, 31250) e2 e3
  let e5 : LowMeanIntegerExpr := .atom (39, 89)
  let e6 : LowMeanIntegerExpr := .pow (59319, 704969) e5 3
  let e7 : LowMeanIntegerExpr := .mul (404021709, 22030281250) e4 e6
  let e8 : LowMeanIntegerExpr := .atom (1837, 1000000)
  let e9 : LowMeanIntegerExpr := .mul (1837, 250000) e0 e8
  let e10 : LowMeanIntegerExpr := .atom (8, 1)
  let e11 : LowMeanIntegerExpr := .atom (691, 500000)
  let e12 : LowMeanIntegerExpr := .mul (691, 62500) e10 e11
  let e13 : LowMeanIntegerExpr := .atom (15, 1)
  let e14 : LowMeanIntegerExpr := .mul (2073, 12500) e12 e13
  let e15 : LowMeanIntegerExpr := .add (43297, 250000) e9 e14
  let e16 : LowMeanIntegerExpr := .mul (691, 125000) e0 e11
  let e17 : LowMeanIntegerExpr := .atom (6, 5)
  let e18 : LowMeanIntegerExpr := .mul (2073, 312500) e16 e17
  let e19 : LowMeanIntegerExpr := .neg (-2073, 312500) e18
  let e20 : LowMeanIntegerExpr := .add (208193, 1250000) e15 e19
  let e21 : LowMeanIntegerExpr := .mul (8119527, 111250000) e20 e5
  let e22 : LowMeanIntegerExpr := .neg (-8119527, 111250000) e21
  let e23 : LowMeanIntegerExpr := .add (-48153905007, 881211250000) e7 e22
  let e24 : LowMeanIntegerExpr := .atom (32, 1)
  let e25 : LowMeanIntegerExpr := .mul (691, 15625) e24 e11
  let e26 : LowMeanIntegerExpr := .add (-9183218687, 881211250000) e23 e25
  e26

def lowMeanCurvedExpr4 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (4, 1)
  let e1 : LowMeanIntegerExpr := .atom (3781, 100000)
  let e2 : LowMeanIntegerExpr := .mul (3781, 25000) e0 e1
  let e3 : LowMeanIntegerExpr := .atom (1, 1)
  let e4 : LowMeanIntegerExpr := .mul (3781, 25000) e2 e3
  let e5 : LowMeanIntegerExpr := .atom (8, 13)
  let e6 : LowMeanIntegerExpr := .pow (512, 2197) e5 3
  let e7 : LowMeanIntegerExpr := .mul (241984, 6865625) e4 e6
  let e8 : LowMeanIntegerExpr := .atom (2637, 500000)
  let e9 : LowMeanIntegerExpr := .mul (2637, 125000) e0 e8
  let e10 : LowMeanIntegerExpr := .atom (8, 1)
  let e11 : LowMeanIntegerExpr := .atom (1783, 1000000)
  let e12 : LowMeanIntegerExpr := .mul (1783, 125000) e10 e11
  let e13 : LowMeanIntegerExpr := .atom (19, 2)
  let e14 : LowMeanIntegerExpr := .mul (33877, 250000) e12 e13
  let e15 : LowMeanIntegerExpr := .add (39151, 250000) e9 e14
  let e16 : LowMeanIntegerExpr := .mul (1783, 250000) e0 e11
  let e17 : LowMeanIntegerExpr := .atom (9, 5)
  let e18 : LowMeanIntegerExpr := .mul (16047, 1250000) e16 e17
  let e19 : LowMeanIntegerExpr := .neg (-16047, 1250000) e18
  let e20 : LowMeanIntegerExpr := .add (44927, 312500) e15 e19
  let e21 : LowMeanIntegerExpr := .mul (89854, 1015625) e20 e5
  let e22 : LowMeanIntegerExpr := .neg (-89854, 1015625) e21
  let e23 : LowMeanIntegerExpr := .add (-9135726, 171640625) e7 e22
  let e24 : LowMeanIntegerExpr := .atom (32, 1)
  let e25 : LowMeanIntegerExpr := .mul (1783, 31250) e24 e11
  let e26 : LowMeanIntegerExpr := .add (1314803, 343281250) e23 e25
  e26

def lowMeanCurvedExpr5 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (12, 1)
  let e1 : LowMeanIntegerExpr := .atom (3781, 100000)
  let e2 : LowMeanIntegerExpr := .mul (11343, 25000) e0 e1
  let e3 : LowMeanIntegerExpr := .atom (1, 1)
  let e4 : LowMeanIntegerExpr := .mul (11343, 25000) e2 e3
  let e5 : LowMeanIntegerExpr := .atom (8, 13)
  let e6 : LowMeanIntegerExpr := .pow (64, 169) e5 2
  let e7 : LowMeanIntegerExpr := .mul (90744, 528125) e4 e6
  let e8 : LowMeanIntegerExpr := .atom (4, 1)
  let e9 : LowMeanIntegerExpr := .atom (2637, 500000)
  let e10 : LowMeanIntegerExpr := .mul (2637, 125000) e8 e9
  let e11 : LowMeanIntegerExpr := .atom (8, 1)
  let e12 : LowMeanIntegerExpr := .atom (1783, 1000000)
  let e13 : LowMeanIntegerExpr := .mul (1783, 125000) e11 e12
  let e14 : LowMeanIntegerExpr := .atom (19, 2)
  let e15 : LowMeanIntegerExpr := .mul (33877, 250000) e13 e14
  let e16 : LowMeanIntegerExpr := .add (39151, 250000) e10 e15
  let e17 : LowMeanIntegerExpr := .mul (1783, 250000) e8 e12
  let e18 : LowMeanIntegerExpr := .atom (9, 5)
  let e19 : LowMeanIntegerExpr := .mul (16047, 1250000) e17 e18
  let e20 : LowMeanIntegerExpr := .neg (-16047, 1250000) e19
  let e21 : LowMeanIntegerExpr := .add (44927, 312500) e16 e20
  let e22 : LowMeanIntegerExpr := .neg (-44927, 312500) e21
  let e23 : LowMeanIntegerExpr := .add (1481737, 52812500) e7 e22
  e23

def lowMeanCurvedRecords : List (LowMeanCertificateInput × LowMeanIntegerExpr × lowMeanFraction × ℕ) :=
  [ (lowMeanCertificate01, lowMeanCurvedExpr0, (-3840997, 2000000000), 0),
    (lowMeanCertificate01, lowMeanCurvedExpr1, (-49152759, 16000000000), 1),
    (lowMeanCertificate02, lowMeanCurvedExpr2, (-539227, 80000000), 0),
    (lowMeanCertificate02, lowMeanCurvedExpr3, (-9183218687, 881211250000), 1),
    (lowMeanCertificate24, lowMeanCurvedExpr4, (1314803, 343281250), 0),
    (lowMeanCertificate24, lowMeanCurvedExpr5, (1481737, 52812500), 2) ]

def lowMeanRatioHighExpr0 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (2, 1)
  let e1 : LowMeanIntegerExpr := .atom (3, 8)
  let e2 : LowMeanIntegerExpr := .mul (3, 4) e0 e1
  let e3 : LowMeanIntegerExpr := .atom (1, 1)
  let e4 : LowMeanIntegerExpr := .add (7, 4) e3 e2
  let e5 : LowMeanIntegerExpr := .mul (21, 16) e2 e4
  let e6 : LowMeanIntegerExpr := .neg (-3, 8) e1
  let e7 : LowMeanIntegerExpr := .add (5, 8) e3 e6
  let e8 : LowMeanIntegerExpr := .mul (105, 128) e5 e7
  let e9 : LowMeanIntegerExpr := .add (11, 8) e3 e1
  let e10 : LowMeanIntegerExpr := .add (13, 8) e0 e6
  let e11 : LowMeanIntegerExpr := .mul (143, 64) e9 e10
  let e12 : LowMeanIntegerExpr := .div (105, 286) e8 e11
  let e13 : LowMeanIntegerExpr := .atom (3, 7)
  let e14 : LowMeanIntegerExpr := .atom (-1, 125)
  let e15 : LowMeanIntegerExpr := .atom (3, 1250)
  let e16 : LowMeanIntegerExpr := .selectLT (-1, 125) e1 e13 e14 e15
  let e17 : LowMeanIntegerExpr := .add (12839, 35750) e12 e16
  let e18 : LowMeanIntegerExpr := .div (51356, 53625) e17 e1
  let e19 : LowMeanIntegerExpr := .atom (51356, 53625)
  let e20 : LowMeanIntegerExpr := .neg (-51356, 53625) e19
  let e21 : LowMeanIntegerExpr := .add (0, 1) e18 e20
  e21

def lowMeanRatioSwitchExpr0 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (2, 1)
  let e1 : LowMeanIntegerExpr := .atom (3, 7)
  let e2 : LowMeanIntegerExpr := .mul (6, 7) e0 e1
  let e3 : LowMeanIntegerExpr := .atom (1, 1)
  let e4 : LowMeanIntegerExpr := .add (13, 7) e3 e2
  let e5 : LowMeanIntegerExpr := .mul (78, 49) e2 e4
  let e6 : LowMeanIntegerExpr := .neg (-3, 7) e1
  let e7 : LowMeanIntegerExpr := .add (4, 7) e3 e6
  let e8 : LowMeanIntegerExpr := .mul (312, 343) e5 e7
  let e9 : LowMeanIntegerExpr := .add (10, 7) e3 e1
  let e10 : LowMeanIntegerExpr := .add (11, 7) e0 e6
  let e11 : LowMeanIntegerExpr := .mul (110, 49) e9 e10
  let e12 : LowMeanIntegerExpr := .div (156, 385) e8 e11
  let e13 : LowMeanIntegerExpr := .div (52, 55) e12 e1
  let e14 : LowMeanIntegerExpr := .atom (-1, 125)
  let e15 : LowMeanIntegerExpr := .div (-7, 375) e14 e1
  let e16 : LowMeanIntegerExpr := .add (3823, 4125) e13 e15
  let e17 : LowMeanIntegerExpr := .atom (51356, 53625)
  let e18 : LowMeanIntegerExpr := .neg (-51356, 53625) e17
  let e19 : LowMeanIntegerExpr := .add (-1657, 53625) e16 e18
  e19

def lowMeanRatioHighExpr1 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (2, 1)
  let e1 : LowMeanIntegerExpr := .atom (39, 89)
  let e2 : LowMeanIntegerExpr := .mul (78, 89) e0 e1
  let e3 : LowMeanIntegerExpr := .atom (1, 1)
  let e4 : LowMeanIntegerExpr := .add (167, 89) e3 e2
  let e5 : LowMeanIntegerExpr := .mul (13026, 7921) e2 e4
  let e6 : LowMeanIntegerExpr := .neg (-39, 89) e1
  let e7 : LowMeanIntegerExpr := .add (50, 89) e3 e6
  let e8 : LowMeanIntegerExpr := .mul (651300, 704969) e5 e7
  let e9 : LowMeanIntegerExpr := .add (128, 89) e3 e1
  let e10 : LowMeanIntegerExpr := .add (139, 89) e0 e6
  let e11 : LowMeanIntegerExpr := .mul (17792, 7921) e9 e10
  let e12 : LowMeanIntegerExpr := .div (162825, 395872) e8 e11
  let e13 : LowMeanIntegerExpr := .atom (3, 7)
  let e14 : LowMeanIntegerExpr := .atom (-1, 125)
  let e15 : LowMeanIntegerExpr := .atom (3, 1250)
  let e16 : LowMeanIntegerExpr := .selectLT (3, 1250) e1 e13 e14 e15
  let e17 : LowMeanIntegerExpr := .add (102359433, 247420000) e12 e16
  let e18 : LowMeanIntegerExpr := .div (34119811, 36140000) e17 e1
  let e19 : LowMeanIntegerExpr := .atom (3823, 4125)
  let e20 : LowMeanIntegerExpr := .neg (-3823, 4125) e19
  let e21 : LowMeanIntegerExpr := .add (20648003, 1192620000) e18 e20
  e21

def lowMeanRatioSwitchExpr1 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (2, 1)
  let e1 : LowMeanIntegerExpr := .atom (3, 7)
  let e2 : LowMeanIntegerExpr := .mul (6, 7) e0 e1
  let e3 : LowMeanIntegerExpr := .atom (1, 1)
  let e4 : LowMeanIntegerExpr := .add (13, 7) e3 e2
  let e5 : LowMeanIntegerExpr := .mul (78, 49) e2 e4
  let e6 : LowMeanIntegerExpr := .neg (-3, 7) e1
  let e7 : LowMeanIntegerExpr := .add (4, 7) e3 e6
  let e8 : LowMeanIntegerExpr := .mul (312, 343) e5 e7
  let e9 : LowMeanIntegerExpr := .add (10, 7) e3 e1
  let e10 : LowMeanIntegerExpr := .add (11, 7) e0 e6
  let e11 : LowMeanIntegerExpr := .mul (110, 49) e9 e10
  let e12 : LowMeanIntegerExpr := .div (156, 385) e8 e11
  let e13 : LowMeanIntegerExpr := .div (52, 55) e12 e1
  let e14 : LowMeanIntegerExpr := .atom (-1, 125)
  let e15 : LowMeanIntegerExpr := .div (-7, 375) e14 e1
  let e16 : LowMeanIntegerExpr := .add (3823, 4125) e13 e15
  let e17 : LowMeanIntegerExpr := .atom (3823, 4125)
  let e18 : LowMeanIntegerExpr := .neg (-3823, 4125) e17
  let e19 : LowMeanIntegerExpr := .add (0, 1) e16 e18
  e19

def lowMeanRatioHighExpr2 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (2, 1)
  let e1 : LowMeanIntegerExpr := .atom (19, 29)
  let e2 : LowMeanIntegerExpr := .mul (38, 29) e0 e1
  let e3 : LowMeanIntegerExpr := .atom (1, 1)
  let e4 : LowMeanIntegerExpr := .add (67, 29) e3 e2
  let e5 : LowMeanIntegerExpr := .mul (2546, 841) e2 e4
  let e6 : LowMeanIntegerExpr := .neg (-19, 29) e1
  let e7 : LowMeanIntegerExpr := .add (10, 29) e3 e6
  let e8 : LowMeanIntegerExpr := .mul (25460, 24389) e5 e7
  let e9 : LowMeanIntegerExpr := .add (48, 29) e3 e1
  let e10 : LowMeanIntegerExpr := .add (39, 29) e0 e6
  let e11 : LowMeanIntegerExpr := .mul (1872, 841) e9 e10
  let e12 : LowMeanIntegerExpr := .div (6365, 13572) e8 e11
  let e13 : LowMeanIntegerExpr := .atom (3, 7)
  let e14 : LowMeanIntegerExpr := .atom (-1, 125)
  let e15 : LowMeanIntegerExpr := .atom (3, 1250)
  let e16 : LowMeanIntegerExpr := .selectLT (3, 1250) e1 e13 e14 e15
  let e17 : LowMeanIntegerExpr := .add (3998483, 8482500) e12 e16
  let e18 : LowMeanIntegerExpr := .div (3998483, 5557500) e17 e1
  let e19 : LowMeanIntegerExpr := .atom (3998483, 5557500)
  let e20 : LowMeanIntegerExpr := .neg (-3998483, 5557500) e19
  let e21 : LowMeanIntegerExpr := .add (0, 1) e18 e20
  e21

def lowMeanRatioSwitchExpr2 : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (2, 1)
  let e1 : LowMeanIntegerExpr := .atom (3, 7)
  let e2 : LowMeanIntegerExpr := .mul (6, 7) e0 e1
  let e3 : LowMeanIntegerExpr := .atom (1, 1)
  let e4 : LowMeanIntegerExpr := .add (13, 7) e3 e2
  let e5 : LowMeanIntegerExpr := .mul (78, 49) e2 e4
  let e6 : LowMeanIntegerExpr := .neg (-3, 7) e1
  let e7 : LowMeanIntegerExpr := .add (4, 7) e3 e6
  let e8 : LowMeanIntegerExpr := .mul (312, 343) e5 e7
  let e9 : LowMeanIntegerExpr := .add (10, 7) e3 e1
  let e10 : LowMeanIntegerExpr := .add (11, 7) e0 e6
  let e11 : LowMeanIntegerExpr := .mul (110, 49) e9 e10
  let e12 : LowMeanIntegerExpr := .div (156, 385) e8 e11
  let e13 : LowMeanIntegerExpr := .div (52, 55) e12 e1
  let e14 : LowMeanIntegerExpr := .atom (-1, 125)
  let e15 : LowMeanIntegerExpr := .div (-7, 375) e14 e1
  let e16 : LowMeanIntegerExpr := .add (3823, 4125) e13 e15
  let e17 : LowMeanIntegerExpr := .atom (3998483, 5557500)
  let e18 : LowMeanIntegerExpr := .neg (-3998483, 5557500) e17
  let e19 : LowMeanIntegerExpr := .add (12673547, 61132500) e16 e18
  e19

def lowMeanRatioRecords : List (LowMeanCertificateInput × lowMeanFraction × LowMeanIntegerExpr × LowMeanIntegerExpr × ℕ) :=
  [ (lowMeanCertificate01, (51356, 53625), lowMeanRatioHighExpr0, lowMeanRatioSwitchExpr0, 1),
    (lowMeanCertificate02, (3823, 4125), lowMeanRatioHighExpr1, lowMeanRatioSwitchExpr1, 2),
    (lowMeanCertificate24, (3998483, 5557500), lowMeanRatioHighExpr2, lowMeanRatioSwitchExpr2, 24) ]

end Erdos993Lean.Analytic.V213
