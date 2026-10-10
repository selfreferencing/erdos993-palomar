module

public import Erdos993Lean.Analytic.V213.LowMeanCoreChecker
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0023
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0031Part0000
public import Erdos993Lean.Analytic.V213.LowMeanIntegerExpr
public import Erdos993Lean.Ceiling.Prefix
public import Erdos993Lean.Ceiling.Statement


/-! Direct-fiber core witnesses with explicit complete integer windows. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanRankExpr0032_47_a : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (9807, 125000)
  let e1 : LowMeanIntegerExpr := .atom (4183, 5000000)
  let e2 : LowMeanIntegerExpr := .atom (44, 1)
  let e3 : LowMeanIntegerExpr := .atom (121, 4)
  let e4 : LowMeanIntegerExpr := .neg (-121, 4) e3
  let e5 : LowMeanIntegerExpr := .add (55, 4) e2 e4
  let e6 : LowMeanIntegerExpr := .mul (46013, 4000000) e1 e5
  let e7 : LowMeanIntegerExpr := .add (359837, 4000000) e0 e6
  let e8 : LowMeanIntegerExpr := .atom (327, 6250000)
  let e9 : LowMeanIntegerExpr := .pow (3025, 16) e5 2
  let e10 : LowMeanIntegerExpr := .mul (39567, 4000000) e8 e9
  let e11 : LowMeanIntegerExpr := .neg (-39567, 4000000) e10
  let e12 : LowMeanIntegerExpr := .add (32027, 400000) e7 e11
  let e13 : LowMeanIntegerExpr := .atom (317, 20000)
  let e14 : LowMeanIntegerExpr := .pow (100489, 400000000) e13 2
  let e15 : LowMeanIntegerExpr := .atom (4, 1)
  let e16 : LowMeanIntegerExpr := .atom (5511, 1000000)
  let e17 : LowMeanIntegerExpr := .mul (5511, 250000) e15 e16
  let e18 : LowMeanIntegerExpr := .div (100489, 8817600) e14 e17
  let e19 : LowMeanIntegerExpr := .add (201623047, 2204400000) e12 e18
  let e20 : LowMeanIntegerExpr := .atom (2461, 2500)
  let e21 : LowMeanIntegerExpr := .atom (1, 1)
  let e22 : LowMeanIntegerExpr := .atom (3, 8)
  let e23 : LowMeanIntegerExpr := .neg (-3, 8) e22
  let e24 : LowMeanIntegerExpr := .add (5, 8) e21 e23
  let e25 : LowMeanIntegerExpr := .pow (5684341886080801486968994140625, 5444517870735015415413993718908291383296) e24 44
  let e26 : LowMeanIntegerExpr := .mul (22382664610631763935089111328125, 21778071482940061661655974875633165533184) e20 e25
  let e27 : LowMeanIntegerExpr := .neg (-22382664610631763935089111328125, 21778071482940061661655974875633165533184) e26
  let e28 : LowMeanIntegerExpr := .add (34304383444014358460267971106798186541696778841, 375059224820258374429331492311294922666803200000) e19 e27
  let e29 : LowMeanIntegerExpr := .atom (1253228031892170912114126775293, 1934281311383406679529881600000000)
  let e30 : LowMeanIntegerExpr := .add (4318423213261746920555013552145292664534752339317, 46882403102532296803666436538911865333350400000000) e28 e29
  let e31 : LowMeanIntegerExpr := .atom (5646768381085527453010082244873046875, 2722258935367507707706996859454145691648)
  let e32 : LowMeanIntegerExpr := .mul (5646768381085527453010082244873046875, 2722258935367507707706996859454145691648) e21 e31
  let e33 : LowMeanIntegerExpr := .add (4415671152474754238659821562306215668685142964317, 46882403102532296803666436538911865333350400000000) e30 e32
  let e34 : LowMeanIntegerExpr := .atom (0, 1)
  let e35 : LowMeanIntegerExpr := .atom (1, 4)
  let e36 : LowMeanIntegerExpr := .mul (11, 1) e2 e35
  let e37 : LowMeanIntegerExpr := .atom (39, 1)
  let e38 : LowMeanIntegerExpr := .atom (2, 1)
  let e39 : LowMeanIntegerExpr := .mul (5511, 500000) e38 e16
  let e40 : LowMeanIntegerExpr := .div (7925, 5511) e13 e39
  let e41 : LowMeanIntegerExpr := .add (222854, 5511) e37 e40
  let e42 : LowMeanIntegerExpr := .neg (-222854, 5511) e41
  let e43 : LowMeanIntegerExpr := .add (-162233, 5511) e36 e42
  let e44 : LowMeanIntegerExpr := .mul (33, 2) e2 e22
  let e45 : LowMeanIntegerExpr := .neg (-33, 2) e44
  let e46 : LowMeanIntegerExpr := .add (263845, 11022) e41 e45
  let e47 : LowMeanIntegerExpr := .maximum (263845, 11022) e43 e46
  let e48 : LowMeanIntegerExpr := .maximum (263845, 11022) e34 e47
  let e49 : LowMeanIntegerExpr := .pow (69614184025, 121484484) e48 2
  let e50 : LowMeanIntegerExpr := .mul (2784567361, 881760000) e16 e49
  let e51 : LowMeanIntegerExpr := .neg (-2784567361, 881760000) e50
  let e52 : LowMeanIntegerExpr := .add (-26063749690279466230101759344150619665729307653, 8507059173023461586584365185794205286400000000) e33 e51
  let e53 : LowMeanIntegerExpr := .neg (26063749690279466230101759344150619665729307653, 8507059173023461586584365185794205286400000000) e52
  e53

noncomputable def lowMeanRankExpr0032_47_b : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (0, 1)
  e0

noncomputable def lowMeanRankExpr0032_48_a : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (9807, 125000)
  let e1 : LowMeanIntegerExpr := .atom (4183, 5000000)
  let e2 : LowMeanIntegerExpr := .atom (44, 1)
  let e3 : LowMeanIntegerExpr := .atom (121, 4)
  let e4 : LowMeanIntegerExpr := .neg (-121, 4) e3
  let e5 : LowMeanIntegerExpr := .add (55, 4) e2 e4
  let e6 : LowMeanIntegerExpr := .mul (46013, 4000000) e1 e5
  let e7 : LowMeanIntegerExpr := .add (359837, 4000000) e0 e6
  let e8 : LowMeanIntegerExpr := .atom (327, 6250000)
  let e9 : LowMeanIntegerExpr := .pow (3025, 16) e5 2
  let e10 : LowMeanIntegerExpr := .mul (39567, 4000000) e8 e9
  let e11 : LowMeanIntegerExpr := .neg (-39567, 4000000) e10
  let e12 : LowMeanIntegerExpr := .add (32027, 400000) e7 e11
  let e13 : LowMeanIntegerExpr := .atom (317, 20000)
  let e14 : LowMeanIntegerExpr := .pow (100489, 400000000) e13 2
  let e15 : LowMeanIntegerExpr := .atom (4, 1)
  let e16 : LowMeanIntegerExpr := .atom (5511, 1000000)
  let e17 : LowMeanIntegerExpr := .mul (5511, 250000) e15 e16
  let e18 : LowMeanIntegerExpr := .div (100489, 8817600) e14 e17
  let e19 : LowMeanIntegerExpr := .add (201623047, 2204400000) e12 e18
  let e20 : LowMeanIntegerExpr := .atom (2461, 2500)
  let e21 : LowMeanIntegerExpr := .atom (1, 1)
  let e22 : LowMeanIntegerExpr := .atom (3, 8)
  let e23 : LowMeanIntegerExpr := .neg (-3, 8) e22
  let e24 : LowMeanIntegerExpr := .add (5, 8) e21 e23
  let e25 : LowMeanIntegerExpr := .pow (5684341886080801486968994140625, 5444517870735015415413993718908291383296) e24 44
  let e26 : LowMeanIntegerExpr := .mul (22382664610631763935089111328125, 21778071482940061661655974875633165533184) e20 e25
  let e27 : LowMeanIntegerExpr := .neg (-22382664610631763935089111328125, 21778071482940061661655974875633165533184) e26
  let e28 : LowMeanIntegerExpr := .add (34304383444014358460267971106798186541696778841, 375059224820258374429331492311294922666803200000) e19 e27
  let e29 : LowMeanIntegerExpr := .atom (1253228031892170912114126775293, 1934281311383406679529881600000000)
  let e30 : LowMeanIntegerExpr := .add (4318423213261746920555013552145292664534752339317, 46882403102532296803666436538911865333350400000000) e28 e29
  let e31 : LowMeanIntegerExpr := .atom (5646768381085527453010082244873046875, 2722258935367507707706996859454145691648)
  let e32 : LowMeanIntegerExpr := .mul (5646768381085527453010082244873046875, 2722258935367507707706996859454145691648) e21 e31
  let e33 : LowMeanIntegerExpr := .add (4415671152474754238659821562306215668685142964317, 46882403102532296803666436538911865333350400000000) e30 e32
  let e34 : LowMeanIntegerExpr := .atom (0, 1)
  let e35 : LowMeanIntegerExpr := .atom (1, 4)
  let e36 : LowMeanIntegerExpr := .mul (11, 1) e2 e35
  let e37 : LowMeanIntegerExpr := .atom (40, 1)
  let e38 : LowMeanIntegerExpr := .atom (2, 1)
  let e39 : LowMeanIntegerExpr := .mul (5511, 500000) e38 e16
  let e40 : LowMeanIntegerExpr := .div (7925, 5511) e13 e39
  let e41 : LowMeanIntegerExpr := .add (228365, 5511) e37 e40
  let e42 : LowMeanIntegerExpr := .neg (-228365, 5511) e41
  let e43 : LowMeanIntegerExpr := .add (-167744, 5511) e36 e42
  let e44 : LowMeanIntegerExpr := .mul (33, 2) e2 e22
  let e45 : LowMeanIntegerExpr := .neg (-33, 2) e44
  let e46 : LowMeanIntegerExpr := .add (274867, 11022) e41 e45
  let e47 : LowMeanIntegerExpr := .maximum (274867, 11022) e43 e46
  let e48 : LowMeanIntegerExpr := .maximum (274867, 11022) e34 e47
  let e49 : LowMeanIntegerExpr := .pow (75551867689, 121484484) e48 2
  let e50 : LowMeanIntegerExpr := .mul (75551867689, 22044000000) e16 e49
  let e51 : LowMeanIntegerExpr := .neg (-75551867689, 22044000000) e50
  let e52 : LowMeanIntegerExpr := .add (-28355177120888373749217777613135403624852866053, 8507059173023461586584365185794205286400000000) e33 e51
  let e53 : LowMeanIntegerExpr := .neg (28355177120888373749217777613135403624852866053, 8507059173023461586584365185794205286400000000) e52
  e53

noncomputable def lowMeanRankExpr0032_48_b : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (0, 1)
  e0

noncomputable def lowMeanRankExpr0032_49_a : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (9807, 125000)
  let e1 : LowMeanIntegerExpr := .atom (4183, 5000000)
  let e2 : LowMeanIntegerExpr := .atom (44, 1)
  let e3 : LowMeanIntegerExpr := .atom (121, 4)
  let e4 : LowMeanIntegerExpr := .neg (-121, 4) e3
  let e5 : LowMeanIntegerExpr := .add (55, 4) e2 e4
  let e6 : LowMeanIntegerExpr := .mul (46013, 4000000) e1 e5
  let e7 : LowMeanIntegerExpr := .add (359837, 4000000) e0 e6
  let e8 : LowMeanIntegerExpr := .atom (327, 6250000)
  let e9 : LowMeanIntegerExpr := .pow (3025, 16) e5 2
  let e10 : LowMeanIntegerExpr := .mul (39567, 4000000) e8 e9
  let e11 : LowMeanIntegerExpr := .neg (-39567, 4000000) e10
  let e12 : LowMeanIntegerExpr := .add (32027, 400000) e7 e11
  let e13 : LowMeanIntegerExpr := .atom (317, 20000)
  let e14 : LowMeanIntegerExpr := .pow (100489, 400000000) e13 2
  let e15 : LowMeanIntegerExpr := .atom (4, 1)
  let e16 : LowMeanIntegerExpr := .atom (5511, 1000000)
  let e17 : LowMeanIntegerExpr := .mul (5511, 250000) e15 e16
  let e18 : LowMeanIntegerExpr := .div (100489, 8817600) e14 e17
  let e19 : LowMeanIntegerExpr := .add (201623047, 2204400000) e12 e18
  let e20 : LowMeanIntegerExpr := .atom (2461, 2500)
  let e21 : LowMeanIntegerExpr := .atom (1, 1)
  let e22 : LowMeanIntegerExpr := .atom (3, 8)
  let e23 : LowMeanIntegerExpr := .neg (-3, 8) e22
  let e24 : LowMeanIntegerExpr := .add (5, 8) e21 e23
  let e25 : LowMeanIntegerExpr := .pow (5684341886080801486968994140625, 5444517870735015415413993718908291383296) e24 44
  let e26 : LowMeanIntegerExpr := .mul (22382664610631763935089111328125, 21778071482940061661655974875633165533184) e20 e25
  let e27 : LowMeanIntegerExpr := .neg (-22382664610631763935089111328125, 21778071482940061661655974875633165533184) e26
  let e28 : LowMeanIntegerExpr := .add (34304383444014358460267971106798186541696778841, 375059224820258374429331492311294922666803200000) e19 e27
  let e29 : LowMeanIntegerExpr := .atom (1253228031892170912114126775293, 1934281311383406679529881600000000)
  let e30 : LowMeanIntegerExpr := .add (4318423213261746920555013552145292664534752339317, 46882403102532296803666436538911865333350400000000) e28 e29
  let e31 : LowMeanIntegerExpr := .atom (5646768381085527453010082244873046875, 2722258935367507707706996859454145691648)
  let e32 : LowMeanIntegerExpr := .mul (5646768381085527453010082244873046875, 2722258935367507707706996859454145691648) e21 e31
  let e33 : LowMeanIntegerExpr := .add (4415671152474754238659821562306215668685142964317, 46882403102532296803666436538911865333350400000000) e30 e32
  let e34 : LowMeanIntegerExpr := .atom (0, 1)
  let e35 : LowMeanIntegerExpr := .atom (1, 4)
  let e36 : LowMeanIntegerExpr := .mul (11, 1) e2 e35
  let e37 : LowMeanIntegerExpr := .atom (41, 1)
  let e38 : LowMeanIntegerExpr := .atom (2, 1)
  let e39 : LowMeanIntegerExpr := .mul (5511, 500000) e38 e16
  let e40 : LowMeanIntegerExpr := .div (7925, 5511) e13 e39
  let e41 : LowMeanIntegerExpr := .add (233876, 5511) e37 e40
  let e42 : LowMeanIntegerExpr := .neg (-233876, 5511) e41
  let e43 : LowMeanIntegerExpr := .add (-173255, 5511) e36 e42
  let e44 : LowMeanIntegerExpr := .mul (33, 2) e2 e22
  let e45 : LowMeanIntegerExpr := .neg (-33, 2) e44
  let e46 : LowMeanIntegerExpr := .add (285889, 11022) e41 e45
  let e47 : LowMeanIntegerExpr := .maximum (285889, 11022) e43 e46
  let e48 : LowMeanIntegerExpr := .maximum (285889, 11022) e34 e47
  let e49 : LowMeanIntegerExpr := .pow (81732520321, 121484484) e48 2
  let e50 : LowMeanIntegerExpr := .mul (81732520321, 22044000000) e16 e49
  let e51 : LowMeanIntegerExpr := .neg (-81732520321, 22044000000) e50
  let e52 : LowMeanIntegerExpr := .add (-30740369357702345861941128755198011314643125253, 8507059173023461586584365185794205286400000000) e33 e51
  let e53 : LowMeanIntegerExpr := .neg (30740369357702345861941128755198011314643125253, 8507059173023461586584365185794205286400000000) e52
  e53

noncomputable def lowMeanRankExpr0032_49_b : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (0, 1)
  e0

noncomputable def lowMeanRankExpr0032_50_a : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (9807, 125000)
  let e1 : LowMeanIntegerExpr := .atom (4183, 5000000)
  let e2 : LowMeanIntegerExpr := .atom (44, 1)
  let e3 : LowMeanIntegerExpr := .atom (121, 4)
  let e4 : LowMeanIntegerExpr := .neg (-121, 4) e3
  let e5 : LowMeanIntegerExpr := .add (55, 4) e2 e4
  let e6 : LowMeanIntegerExpr := .mul (46013, 4000000) e1 e5
  let e7 : LowMeanIntegerExpr := .add (359837, 4000000) e0 e6
  let e8 : LowMeanIntegerExpr := .atom (327, 6250000)
  let e9 : LowMeanIntegerExpr := .pow (3025, 16) e5 2
  let e10 : LowMeanIntegerExpr := .mul (39567, 4000000) e8 e9
  let e11 : LowMeanIntegerExpr := .neg (-39567, 4000000) e10
  let e12 : LowMeanIntegerExpr := .add (32027, 400000) e7 e11
  let e13 : LowMeanIntegerExpr := .atom (317, 20000)
  let e14 : LowMeanIntegerExpr := .pow (100489, 400000000) e13 2
  let e15 : LowMeanIntegerExpr := .atom (4, 1)
  let e16 : LowMeanIntegerExpr := .atom (5511, 1000000)
  let e17 : LowMeanIntegerExpr := .mul (5511, 250000) e15 e16
  let e18 : LowMeanIntegerExpr := .div (100489, 8817600) e14 e17
  let e19 : LowMeanIntegerExpr := .add (201623047, 2204400000) e12 e18
  let e20 : LowMeanIntegerExpr := .atom (2461, 2500)
  let e21 : LowMeanIntegerExpr := .atom (1, 1)
  let e22 : LowMeanIntegerExpr := .atom (3, 8)
  let e23 : LowMeanIntegerExpr := .neg (-3, 8) e22
  let e24 : LowMeanIntegerExpr := .add (5, 8) e21 e23
  let e25 : LowMeanIntegerExpr := .pow (5684341886080801486968994140625, 5444517870735015415413993718908291383296) e24 44
  let e26 : LowMeanIntegerExpr := .mul (22382664610631763935089111328125, 21778071482940061661655974875633165533184) e20 e25
  let e27 : LowMeanIntegerExpr := .neg (-22382664610631763935089111328125, 21778071482940061661655974875633165533184) e26
  let e28 : LowMeanIntegerExpr := .add (34304383444014358460267971106798186541696778841, 375059224820258374429331492311294922666803200000) e19 e27
  let e29 : LowMeanIntegerExpr := .atom (1253228031892170912114126775293, 1934281311383406679529881600000000)
  let e30 : LowMeanIntegerExpr := .add (4318423213261746920555013552145292664534752339317, 46882403102532296803666436538911865333350400000000) e28 e29
  let e31 : LowMeanIntegerExpr := .atom (5646768381085527453010082244873046875, 2722258935367507707706996859454145691648)
  let e32 : LowMeanIntegerExpr := .mul (5646768381085527453010082244873046875, 2722258935367507707706996859454145691648) e21 e31
  let e33 : LowMeanIntegerExpr := .add (4415671152474754238659821562306215668685142964317, 46882403102532296803666436538911865333350400000000) e30 e32
  let e34 : LowMeanIntegerExpr := .atom (0, 1)
  let e35 : LowMeanIntegerExpr := .atom (1, 4)
  let e36 : LowMeanIntegerExpr := .mul (11, 1) e2 e35
  let e37 : LowMeanIntegerExpr := .atom (42, 1)
  let e38 : LowMeanIntegerExpr := .atom (2, 1)
  let e39 : LowMeanIntegerExpr := .mul (5511, 500000) e38 e16
  let e40 : LowMeanIntegerExpr := .div (7925, 5511) e13 e39
  let e41 : LowMeanIntegerExpr := .add (239387, 5511) e37 e40
  let e42 : LowMeanIntegerExpr := .neg (-239387, 5511) e41
  let e43 : LowMeanIntegerExpr := .add (-178766, 5511) e36 e42
  let e44 : LowMeanIntegerExpr := .mul (33, 2) e2 e22
  let e45 : LowMeanIntegerExpr := .neg (-33, 2) e44
  let e46 : LowMeanIntegerExpr := .add (296911, 11022) e41 e45
  let e47 : LowMeanIntegerExpr := .maximum (296911, 11022) e43 e46
  let e48 : LowMeanIntegerExpr := .maximum (296911, 11022) e34 e47
  let e49 : LowMeanIntegerExpr := .pow (88156141921, 121484484) e48 2
  let e50 : LowMeanIntegerExpr := .mul (88156141921, 22044000000) e16 e49
  let e51 : LowMeanIntegerExpr := .neg (-88156141921, 22044000000) e50
  let e52 : LowMeanIntegerExpr := .add (-33219326400721382568271812770338442735100085253, 8507059173023461586584365185794205286400000000) e33 e51
  let e53 : LowMeanIntegerExpr := .neg (33219326400721382568271812770338442735100085253, 8507059173023461586584365185794205286400000000) e52
  e53

noncomputable def lowMeanRankExpr0032_50_b : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (0, 1)
  e0

noncomputable def lowMeanRankExpr0032_51_a : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (9807, 125000)
  let e1 : LowMeanIntegerExpr := .atom (4183, 5000000)
  let e2 : LowMeanIntegerExpr := .atom (44, 1)
  let e3 : LowMeanIntegerExpr := .atom (121, 4)
  let e4 : LowMeanIntegerExpr := .neg (-121, 4) e3
  let e5 : LowMeanIntegerExpr := .add (55, 4) e2 e4
  let e6 : LowMeanIntegerExpr := .mul (46013, 4000000) e1 e5
  let e7 : LowMeanIntegerExpr := .add (359837, 4000000) e0 e6
  let e8 : LowMeanIntegerExpr := .atom (327, 6250000)
  let e9 : LowMeanIntegerExpr := .pow (3025, 16) e5 2
  let e10 : LowMeanIntegerExpr := .mul (39567, 4000000) e8 e9
  let e11 : LowMeanIntegerExpr := .neg (-39567, 4000000) e10
  let e12 : LowMeanIntegerExpr := .add (32027, 400000) e7 e11
  let e13 : LowMeanIntegerExpr := .atom (317, 20000)
  let e14 : LowMeanIntegerExpr := .pow (100489, 400000000) e13 2
  let e15 : LowMeanIntegerExpr := .atom (4, 1)
  let e16 : LowMeanIntegerExpr := .atom (5511, 1000000)
  let e17 : LowMeanIntegerExpr := .mul (5511, 250000) e15 e16
  let e18 : LowMeanIntegerExpr := .div (100489, 8817600) e14 e17
  let e19 : LowMeanIntegerExpr := .add (201623047, 2204400000) e12 e18
  let e20 : LowMeanIntegerExpr := .atom (2461, 2500)
  let e21 : LowMeanIntegerExpr := .atom (1, 1)
  let e22 : LowMeanIntegerExpr := .atom (3, 8)
  let e23 : LowMeanIntegerExpr := .neg (-3, 8) e22
  let e24 : LowMeanIntegerExpr := .add (5, 8) e21 e23
  let e25 : LowMeanIntegerExpr := .pow (5684341886080801486968994140625, 5444517870735015415413993718908291383296) e24 44
  let e26 : LowMeanIntegerExpr := .mul (22382664610631763935089111328125, 21778071482940061661655974875633165533184) e20 e25
  let e27 : LowMeanIntegerExpr := .neg (-22382664610631763935089111328125, 21778071482940061661655974875633165533184) e26
  let e28 : LowMeanIntegerExpr := .add (34304383444014358460267971106798186541696778841, 375059224820258374429331492311294922666803200000) e19 e27
  let e29 : LowMeanIntegerExpr := .atom (1253228031892170912114126775293, 1934281311383406679529881600000000)
  let e30 : LowMeanIntegerExpr := .add (4318423213261746920555013552145292664534752339317, 46882403102532296803666436538911865333350400000000) e28 e29
  let e31 : LowMeanIntegerExpr := .atom (5646768381085527453010082244873046875, 2722258935367507707706996859454145691648)
  let e32 : LowMeanIntegerExpr := .mul (5646768381085527453010082244873046875, 2722258935367507707706996859454145691648) e21 e31
  let e33 : LowMeanIntegerExpr := .add (4415671152474754238659821562306215668685142964317, 46882403102532296803666436538911865333350400000000) e30 e32
  let e34 : LowMeanIntegerExpr := .atom (0, 1)
  let e35 : LowMeanIntegerExpr := .atom (1, 4)
  let e36 : LowMeanIntegerExpr := .mul (11, 1) e2 e35
  let e37 : LowMeanIntegerExpr := .atom (43, 1)
  let e38 : LowMeanIntegerExpr := .atom (2, 1)
  let e39 : LowMeanIntegerExpr := .mul (5511, 500000) e38 e16
  let e40 : LowMeanIntegerExpr := .div (7925, 5511) e13 e39
  let e41 : LowMeanIntegerExpr := .add (244898, 5511) e37 e40
  let e42 : LowMeanIntegerExpr := .neg (-244898, 5511) e41
  let e43 : LowMeanIntegerExpr := .add (-184277, 5511) e36 e42
  let e44 : LowMeanIntegerExpr := .mul (33, 2) e2 e22
  let e45 : LowMeanIntegerExpr := .neg (-33, 2) e44
  let e46 : LowMeanIntegerExpr := .add (307933, 11022) e41 e45
  let e47 : LowMeanIntegerExpr := .maximum (307933, 11022) e43 e46
  let e48 : LowMeanIntegerExpr := .maximum (307933, 11022) e34 e47
  let e49 : LowMeanIntegerExpr := .pow (94822732489, 121484484) e48 2
  let e50 : LowMeanIntegerExpr := .mul (94822732489, 22044000000) e16 e49
  let e51 : LowMeanIntegerExpr := .neg (-94822732489, 22044000000) e50
  let e52 : LowMeanIntegerExpr := .add (-35792048249945483868209829658556697886223746053, 8507059173023461586584365185794205286400000000) e33 e51
  let e53 : LowMeanIntegerExpr := .neg (35792048249945483868209829658556697886223746053, 8507059173023461586584365185794205286400000000) e52
  e53

noncomputable def lowMeanRankExpr0032_51_b : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (0, 1)
  e0

noncomputable def lowMeanRankExpr0032_52_a : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (9807, 125000)
  let e1 : LowMeanIntegerExpr := .atom (4183, 5000000)
  let e2 : LowMeanIntegerExpr := .atom (44, 1)
  let e3 : LowMeanIntegerExpr := .atom (121, 4)
  let e4 : LowMeanIntegerExpr := .neg (-121, 4) e3
  let e5 : LowMeanIntegerExpr := .add (55, 4) e2 e4
  let e6 : LowMeanIntegerExpr := .mul (46013, 4000000) e1 e5
  let e7 : LowMeanIntegerExpr := .add (359837, 4000000) e0 e6
  let e8 : LowMeanIntegerExpr := .atom (327, 6250000)
  let e9 : LowMeanIntegerExpr := .pow (3025, 16) e5 2
  let e10 : LowMeanIntegerExpr := .mul (39567, 4000000) e8 e9
  let e11 : LowMeanIntegerExpr := .neg (-39567, 4000000) e10
  let e12 : LowMeanIntegerExpr := .add (32027, 400000) e7 e11
  let e13 : LowMeanIntegerExpr := .atom (317, 20000)
  let e14 : LowMeanIntegerExpr := .pow (100489, 400000000) e13 2
  let e15 : LowMeanIntegerExpr := .atom (4, 1)
  let e16 : LowMeanIntegerExpr := .atom (5511, 1000000)
  let e17 : LowMeanIntegerExpr := .mul (5511, 250000) e15 e16
  let e18 : LowMeanIntegerExpr := .div (100489, 8817600) e14 e17
  let e19 : LowMeanIntegerExpr := .add (201623047, 2204400000) e12 e18
  let e20 : LowMeanIntegerExpr := .atom (2461, 2500)
  let e21 : LowMeanIntegerExpr := .atom (1, 1)
  let e22 : LowMeanIntegerExpr := .atom (3, 8)
  let e23 : LowMeanIntegerExpr := .neg (-3, 8) e22
  let e24 : LowMeanIntegerExpr := .add (5, 8) e21 e23
  let e25 : LowMeanIntegerExpr := .pow (5684341886080801486968994140625, 5444517870735015415413993718908291383296) e24 44
  let e26 : LowMeanIntegerExpr := .mul (22382664610631763935089111328125, 21778071482940061661655974875633165533184) e20 e25
  let e27 : LowMeanIntegerExpr := .neg (-22382664610631763935089111328125, 21778071482940061661655974875633165533184) e26
  let e28 : LowMeanIntegerExpr := .add (34304383444014358460267971106798186541696778841, 375059224820258374429331492311294922666803200000) e19 e27
  let e29 : LowMeanIntegerExpr := .atom (1253228031892170912114126775293, 1934281311383406679529881600000000)
  let e30 : LowMeanIntegerExpr := .add (4318423213261746920555013552145292664534752339317, 46882403102532296803666436538911865333350400000000) e28 e29
  let e31 : LowMeanIntegerExpr := .atom (5646768381085527453010082244873046875, 2722258935367507707706996859454145691648)
  let e32 : LowMeanIntegerExpr := .mul (5646768381085527453010082244873046875, 2722258935367507707706996859454145691648) e21 e31
  let e33 : LowMeanIntegerExpr := .add (4415671152474754238659821562306215668685142964317, 46882403102532296803666436538911865333350400000000) e30 e32
  let e34 : LowMeanIntegerExpr := .atom (0, 1)
  let e35 : LowMeanIntegerExpr := .atom (1, 4)
  let e36 : LowMeanIntegerExpr := .mul (11, 1) e2 e35
  let e37 : LowMeanIntegerExpr := .atom (2, 1)
  let e38 : LowMeanIntegerExpr := .mul (5511, 500000) e37 e16
  let e39 : LowMeanIntegerExpr := .div (7925, 5511) e13 e38
  let e40 : LowMeanIntegerExpr := .add (250409, 5511) e2 e39
  let e41 : LowMeanIntegerExpr := .neg (-250409, 5511) e40
  let e42 : LowMeanIntegerExpr := .add (-189788, 5511) e36 e41
  let e43 : LowMeanIntegerExpr := .mul (33, 2) e2 e22
  let e44 : LowMeanIntegerExpr := .neg (-33, 2) e43
  let e45 : LowMeanIntegerExpr := .add (318955, 11022) e40 e44
  let e46 : LowMeanIntegerExpr := .maximum (318955, 11022) e42 e45
  let e47 : LowMeanIntegerExpr := .maximum (318955, 11022) e34 e46
  let e48 : LowMeanIntegerExpr := .pow (101732292025, 121484484) e47 2
  let e49 : LowMeanIntegerExpr := .mul (4069291681, 881760000) e16 e48
  let e50 : LowMeanIntegerExpr := .neg (-4069291681, 881760000) e49
  let e51 : LowMeanIntegerExpr := .add (-38458534905374649761755179419852776768014107653, 8507059173023461586584365185794205286400000000) e33 e50
  let e52 : LowMeanIntegerExpr := .neg (38458534905374649761755179419852776768014107653, 8507059173023461586584365185794205286400000000) e51
  e52

noncomputable def lowMeanRankExpr0032_52_b : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (0, 1)
  e0

noncomputable def lowMeanRankExpr0032_53_a : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (9807, 125000)
  let e1 : LowMeanIntegerExpr := .atom (4183, 5000000)
  let e2 : LowMeanIntegerExpr := .atom (44, 1)
  let e3 : LowMeanIntegerExpr := .atom (121, 4)
  let e4 : LowMeanIntegerExpr := .neg (-121, 4) e3
  let e5 : LowMeanIntegerExpr := .add (55, 4) e2 e4
  let e6 : LowMeanIntegerExpr := .mul (46013, 4000000) e1 e5
  let e7 : LowMeanIntegerExpr := .add (359837, 4000000) e0 e6
  let e8 : LowMeanIntegerExpr := .atom (327, 6250000)
  let e9 : LowMeanIntegerExpr := .pow (3025, 16) e5 2
  let e10 : LowMeanIntegerExpr := .mul (39567, 4000000) e8 e9
  let e11 : LowMeanIntegerExpr := .neg (-39567, 4000000) e10
  let e12 : LowMeanIntegerExpr := .add (32027, 400000) e7 e11
  let e13 : LowMeanIntegerExpr := .atom (317, 20000)
  let e14 : LowMeanIntegerExpr := .pow (100489, 400000000) e13 2
  let e15 : LowMeanIntegerExpr := .atom (4, 1)
  let e16 : LowMeanIntegerExpr := .atom (5511, 1000000)
  let e17 : LowMeanIntegerExpr := .mul (5511, 250000) e15 e16
  let e18 : LowMeanIntegerExpr := .div (100489, 8817600) e14 e17
  let e19 : LowMeanIntegerExpr := .add (201623047, 2204400000) e12 e18
  let e20 : LowMeanIntegerExpr := .atom (2461, 2500)
  let e21 : LowMeanIntegerExpr := .atom (1, 1)
  let e22 : LowMeanIntegerExpr := .atom (3, 8)
  let e23 : LowMeanIntegerExpr := .neg (-3, 8) e22
  let e24 : LowMeanIntegerExpr := .add (5, 8) e21 e23
  let e25 : LowMeanIntegerExpr := .pow (5684341886080801486968994140625, 5444517870735015415413993718908291383296) e24 44
  let e26 : LowMeanIntegerExpr := .mul (22382664610631763935089111328125, 21778071482940061661655974875633165533184) e20 e25
  let e27 : LowMeanIntegerExpr := .neg (-22382664610631763935089111328125, 21778071482940061661655974875633165533184) e26
  let e28 : LowMeanIntegerExpr := .add (34304383444014358460267971106798186541696778841, 375059224820258374429331492311294922666803200000) e19 e27
  let e29 : LowMeanIntegerExpr := .atom (1253228031892170912114126775293, 1934281311383406679529881600000000)
  let e30 : LowMeanIntegerExpr := .add (4318423213261746920555013552145292664534752339317, 46882403102532296803666436538911865333350400000000) e28 e29
  let e31 : LowMeanIntegerExpr := .atom (5646768381085527453010082244873046875, 2722258935367507707706996859454145691648)
  let e32 : LowMeanIntegerExpr := .mul (5646768381085527453010082244873046875, 2722258935367507707706996859454145691648) e21 e31
  let e33 : LowMeanIntegerExpr := .add (4415671152474754238659821562306215668685142964317, 46882403102532296803666436538911865333350400000000) e30 e32
  let e34 : LowMeanIntegerExpr := .atom (0, 1)
  let e35 : LowMeanIntegerExpr := .atom (1, 4)
  let e36 : LowMeanIntegerExpr := .mul (11, 1) e2 e35
  let e37 : LowMeanIntegerExpr := .atom (45, 1)
  let e38 : LowMeanIntegerExpr := .atom (2, 1)
  let e39 : LowMeanIntegerExpr := .mul (5511, 500000) e38 e16
  let e40 : LowMeanIntegerExpr := .div (7925, 5511) e13 e39
  let e41 : LowMeanIntegerExpr := .add (255920, 5511) e37 e40
  let e42 : LowMeanIntegerExpr := .neg (-255920, 5511) e41
  let e43 : LowMeanIntegerExpr := .add (-195299, 5511) e36 e42
  let e44 : LowMeanIntegerExpr := .mul (33, 2) e2 e22
  let e45 : LowMeanIntegerExpr := .neg (-33, 2) e44
  let e46 : LowMeanIntegerExpr := .add (329977, 11022) e41 e45
  let e47 : LowMeanIntegerExpr := .maximum (329977, 11022) e43 e46
  let e48 : LowMeanIntegerExpr := .maximum (329977, 11022) e34 e47
  let e49 : LowMeanIntegerExpr := .pow (108884820529, 121484484) e48 2
  let e50 : LowMeanIntegerExpr := .mul (108884820529, 22044000000) e16 e49
  let e51 : LowMeanIntegerExpr := .neg (-108884820529, 22044000000) e50
  let e52 : LowMeanIntegerExpr := .add (-41218786367008880248907862054226679380471170053, 8507059173023461586584365185794205286400000000) e33 e51
  let e53 : LowMeanIntegerExpr := .neg (41218786367008880248907862054226679380471170053, 8507059173023461586584365185794205286400000000) e52
  e53

noncomputable def lowMeanRankExpr0032_53_b : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (0, 1)
  e0

noncomputable def lowMeanRankExpr0032_54_a : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (9807, 125000)
  let e1 : LowMeanIntegerExpr := .atom (4183, 5000000)
  let e2 : LowMeanIntegerExpr := .atom (44, 1)
  let e3 : LowMeanIntegerExpr := .atom (121, 4)
  let e4 : LowMeanIntegerExpr := .neg (-121, 4) e3
  let e5 : LowMeanIntegerExpr := .add (55, 4) e2 e4
  let e6 : LowMeanIntegerExpr := .mul (46013, 4000000) e1 e5
  let e7 : LowMeanIntegerExpr := .add (359837, 4000000) e0 e6
  let e8 : LowMeanIntegerExpr := .atom (327, 6250000)
  let e9 : LowMeanIntegerExpr := .pow (3025, 16) e5 2
  let e10 : LowMeanIntegerExpr := .mul (39567, 4000000) e8 e9
  let e11 : LowMeanIntegerExpr := .neg (-39567, 4000000) e10
  let e12 : LowMeanIntegerExpr := .add (32027, 400000) e7 e11
  let e13 : LowMeanIntegerExpr := .atom (317, 20000)
  let e14 : LowMeanIntegerExpr := .pow (100489, 400000000) e13 2
  let e15 : LowMeanIntegerExpr := .atom (4, 1)
  let e16 : LowMeanIntegerExpr := .atom (5511, 1000000)
  let e17 : LowMeanIntegerExpr := .mul (5511, 250000) e15 e16
  let e18 : LowMeanIntegerExpr := .div (100489, 8817600) e14 e17
  let e19 : LowMeanIntegerExpr := .add (201623047, 2204400000) e12 e18
  let e20 : LowMeanIntegerExpr := .atom (2461, 2500)
  let e21 : LowMeanIntegerExpr := .atom (1, 1)
  let e22 : LowMeanIntegerExpr := .atom (3, 8)
  let e23 : LowMeanIntegerExpr := .neg (-3, 8) e22
  let e24 : LowMeanIntegerExpr := .add (5, 8) e21 e23
  let e25 : LowMeanIntegerExpr := .pow (5684341886080801486968994140625, 5444517870735015415413993718908291383296) e24 44
  let e26 : LowMeanIntegerExpr := .mul (22382664610631763935089111328125, 21778071482940061661655974875633165533184) e20 e25
  let e27 : LowMeanIntegerExpr := .neg (-22382664610631763935089111328125, 21778071482940061661655974875633165533184) e26
  let e28 : LowMeanIntegerExpr := .add (34304383444014358460267971106798186541696778841, 375059224820258374429331492311294922666803200000) e19 e27
  let e29 : LowMeanIntegerExpr := .atom (1253228031892170912114126775293, 1934281311383406679529881600000000)
  let e30 : LowMeanIntegerExpr := .add (4318423213261746920555013552145292664534752339317, 46882403102532296803666436538911865333350400000000) e28 e29
  let e31 : LowMeanIntegerExpr := .atom (0, 1)
  let e32 : LowMeanIntegerExpr := .add (4318423213261746920555013552145292664534752339317, 46882403102532296803666436538911865333350400000000) e30 e31
  let e33 : LowMeanIntegerExpr := .atom (1, 4)
  let e34 : LowMeanIntegerExpr := .mul (11, 1) e2 e33
  let e35 : LowMeanIntegerExpr := .atom (46, 1)
  let e36 : LowMeanIntegerExpr := .atom (2, 1)
  let e37 : LowMeanIntegerExpr := .mul (5511, 500000) e36 e16
  let e38 : LowMeanIntegerExpr := .div (7925, 5511) e13 e37
  let e39 : LowMeanIntegerExpr := .add (261431, 5511) e35 e38
  let e40 : LowMeanIntegerExpr := .neg (-261431, 5511) e39
  let e41 : LowMeanIntegerExpr := .add (-200810, 5511) e34 e40
  let e42 : LowMeanIntegerExpr := .mul (33, 2) e2 e22
  let e43 : LowMeanIntegerExpr := .neg (-33, 2) e42
  let e44 : LowMeanIntegerExpr := .add (340999, 11022) e39 e43
  let e45 : LowMeanIntegerExpr := .maximum (340999, 11022) e41 e44
  let e46 : LowMeanIntegerExpr := .maximum (340999, 11022) e31 e45
  let e47 : LowMeanIntegerExpr := .pow (116280318001, 121484484) e46 2
  let e48 : LowMeanIntegerExpr := .mul (116280318001, 22044000000) e16 e47
  let e49 : LowMeanIntegerExpr := .neg (-116280318001, 22044000000) e48
  let e50 : LowMeanIntegerExpr := .add (-44090448786039067602958534068693633995079308253, 8507059173023461586584365185794205286400000000) e32 e49
  let e51 : LowMeanIntegerExpr := .neg (44090448786039067602958534068693633995079308253, 8507059173023461586584365185794205286400000000) e50
  e51

noncomputable def lowMeanRankExpr0032_54_b : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (0, 1)
  e0

noncomputable def lowMeanRankExpr0032_55_a : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (9807, 125000)
  let e1 : LowMeanIntegerExpr := .atom (4183, 5000000)
  let e2 : LowMeanIntegerExpr := .atom (44, 1)
  let e3 : LowMeanIntegerExpr := .atom (121, 4)
  let e4 : LowMeanIntegerExpr := .neg (-121, 4) e3
  let e5 : LowMeanIntegerExpr := .add (55, 4) e2 e4
  let e6 : LowMeanIntegerExpr := .mul (46013, 4000000) e1 e5
  let e7 : LowMeanIntegerExpr := .add (359837, 4000000) e0 e6
  let e8 : LowMeanIntegerExpr := .atom (327, 6250000)
  let e9 : LowMeanIntegerExpr := .pow (3025, 16) e5 2
  let e10 : LowMeanIntegerExpr := .mul (39567, 4000000) e8 e9
  let e11 : LowMeanIntegerExpr := .neg (-39567, 4000000) e10
  let e12 : LowMeanIntegerExpr := .add (32027, 400000) e7 e11
  let e13 : LowMeanIntegerExpr := .atom (317, 20000)
  let e14 : LowMeanIntegerExpr := .pow (100489, 400000000) e13 2
  let e15 : LowMeanIntegerExpr := .atom (4, 1)
  let e16 : LowMeanIntegerExpr := .atom (5511, 1000000)
  let e17 : LowMeanIntegerExpr := .mul (5511, 250000) e15 e16
  let e18 : LowMeanIntegerExpr := .div (100489, 8817600) e14 e17
  let e19 : LowMeanIntegerExpr := .add (201623047, 2204400000) e12 e18
  let e20 : LowMeanIntegerExpr := .atom (2461, 2500)
  let e21 : LowMeanIntegerExpr := .atom (1, 1)
  let e22 : LowMeanIntegerExpr := .atom (3, 8)
  let e23 : LowMeanIntegerExpr := .neg (-3, 8) e22
  let e24 : LowMeanIntegerExpr := .add (5, 8) e21 e23
  let e25 : LowMeanIntegerExpr := .pow (5684341886080801486968994140625, 5444517870735015415413993718908291383296) e24 44
  let e26 : LowMeanIntegerExpr := .mul (22382664610631763935089111328125, 21778071482940061661655974875633165533184) e20 e25
  let e27 : LowMeanIntegerExpr := .neg (-22382664610631763935089111328125, 21778071482940061661655974875633165533184) e26
  let e28 : LowMeanIntegerExpr := .add (34304383444014358460267971106798186541696778841, 375059224820258374429331492311294922666803200000) e19 e27
  let e29 : LowMeanIntegerExpr := .atom (1253228031892170912114126775293, 1934281311383406679529881600000000)
  let e30 : LowMeanIntegerExpr := .add (4318423213261746920555013552145292664534752339317, 46882403102532296803666436538911865333350400000000) e28 e29
  let e31 : LowMeanIntegerExpr := .atom (0, 1)
  let e32 : LowMeanIntegerExpr := .add (4318423213261746920555013552145292664534752339317, 46882403102532296803666436538911865333350400000000) e30 e31
  let e33 : LowMeanIntegerExpr := .atom (1, 4)
  let e34 : LowMeanIntegerExpr := .mul (11, 1) e2 e33
  let e35 : LowMeanIntegerExpr := .atom (47, 1)
  let e36 : LowMeanIntegerExpr := .atom (2, 1)
  let e37 : LowMeanIntegerExpr := .mul (5511, 500000) e36 e16
  let e38 : LowMeanIntegerExpr := .div (7925, 5511) e13 e37
  let e39 : LowMeanIntegerExpr := .add (266942, 5511) e35 e38
  let e40 : LowMeanIntegerExpr := .neg (-266942, 5511) e39
  let e41 : LowMeanIntegerExpr := .add (-206321, 5511) e34 e40
  let e42 : LowMeanIntegerExpr := .mul (33, 2) e2 e22
  let e43 : LowMeanIntegerExpr := .neg (-33, 2) e42
  let e44 : LowMeanIntegerExpr := .add (352021, 11022) e39 e43
  let e45 : LowMeanIntegerExpr := .maximum (352021, 11022) e41 e44
  let e46 : LowMeanIntegerExpr := .maximum (352021, 11022) e31 e45
  let e47 : LowMeanIntegerExpr := .pow (123918784441, 121484484) e46 2
  let e48 : LowMeanIntegerExpr := .mul (123918784441, 22044000000) e16 e47
  let e49 : LowMeanIntegerExpr := .neg (-123918784441, 22044000000) e48
  let e50 : LowMeanIntegerExpr := .add (-47038229860083427277325882449223184068869772253, 8507059173023461586584365185794205286400000000) e32 e49
  let e51 : LowMeanIntegerExpr := .neg (47038229860083427277325882449223184068869772253, 8507059173023461586584365185794205286400000000) e50
  e51

noncomputable def lowMeanRankExpr0032_55_b : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (0, 1)
  e0

noncomputable def lowMeanFiber0032 : LowMeanFiberInput :=
{ record := 32, certificate := 1, M := 44, zeta := (1253228031892170912114126775293, 1934281311383406679529881600000000), lo := -8, hi := 47,
  gL := (14778703617941155239733815, 154742504910672534362390528), gR := (5646768381085527453010082244873046875, 2722258935367507707706996859454145691648), core := [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19],
  gLExpr := lowMeanFiberExpr0032_0, gRExpr := lowMeanFiberExpr0032_1,
  leftSide := lowMeanFiberExpr0032_2, rightSide := lowMeanFiberExpr0032_3,
  leftTail := lowMeanFiberExpr0032_4, rightTail := lowMeanFiberExpr0032_5,
  ranks := [{ j := -8, state := 0, first := lowMeanRankExpr0032_0_a, second := lowMeanRankExpr0032_0_b }, { j := -7, state := 0, first := lowMeanRankExpr0032_1_a, second := lowMeanRankExpr0032_1_b }, { j := -6, state := 0, first := lowMeanRankExpr0032_2_a, second := lowMeanRankExpr0032_2_b }, { j := -5, state := 0, first := lowMeanRankExpr0032_3_a, second := lowMeanRankExpr0032_3_b }, { j := -4, state := 0, first := lowMeanRankExpr0032_4_a, second := lowMeanRankExpr0032_4_b }, { j := -3, state := 0, first := lowMeanRankExpr0032_5_a, second := lowMeanRankExpr0032_5_b }, { j := -2, state := 0, first := lowMeanRankExpr0032_6_a, second := lowMeanRankExpr0032_6_b }, { j := -1, state := 0, first := lowMeanRankExpr0032_7_a, second := lowMeanRankExpr0032_7_b }, { j := 0, state := 0, first := lowMeanRankExpr0032_8_a, second := lowMeanRankExpr0032_8_b }, { j := 1, state := 0, first := lowMeanRankExpr0032_9_a, second := lowMeanRankExpr0032_9_b }, { j := 2, state := 0, first := lowMeanRankExpr0032_10_a, second := lowMeanRankExpr0032_10_b }, { j := 3, state := 0, first := lowMeanRankExpr0032_11_a, second := lowMeanRankExpr0032_11_b }, { j := 4, state := 0, first := lowMeanRankExpr0032_12_a, second := lowMeanRankExpr0032_12_b }, { j := 5, state := 0, first := lowMeanRankExpr0032_13_a, second := lowMeanRankExpr0032_13_b }, { j := 6, state := 2, first := lowMeanRankExpr0032_14_a, second := lowMeanRankExpr0032_14_b }, { j := 7, state := 2, first := lowMeanRankExpr0032_15_a, second := lowMeanRankExpr0032_15_b }, { j := 8, state := 2, first := lowMeanRankExpr0032_16_a, second := lowMeanRankExpr0032_16_b }, { j := 9, state := 2, first := lowMeanRankExpr0032_17_a, second := lowMeanRankExpr0032_17_b }, { j := 10, state := 2, first := lowMeanRankExpr0032_18_a, second := lowMeanRankExpr0032_18_b }, { j := 11, state := 2, first := lowMeanRankExpr0032_19_a, second := lowMeanRankExpr0032_19_b }, { j := 12, state := 2, first := lowMeanRankExpr0032_20_a, second := lowMeanRankExpr0032_20_b }, { j := 13, state := 2, first := lowMeanRankExpr0032_21_a, second := lowMeanRankExpr0032_21_b }, { j := 14, state := 2, first := lowMeanRankExpr0032_22_a, second := lowMeanRankExpr0032_22_b }, { j := 15, state := 2, first := lowMeanRankExpr0032_23_a, second := lowMeanRankExpr0032_23_b }, { j := 16, state := 2, first := lowMeanRankExpr0032_24_a, second := lowMeanRankExpr0032_24_b }, { j := 17, state := 2, first := lowMeanRankExpr0032_25_a, second := lowMeanRankExpr0032_25_b }, { j := 18, state := 2, first := lowMeanRankExpr0032_26_a, second := lowMeanRankExpr0032_26_b }, { j := 19, state := 2, first := lowMeanRankExpr0032_27_a, second := lowMeanRankExpr0032_27_b }, { j := 20, state := 0, first := lowMeanRankExpr0032_28_a, second := lowMeanRankExpr0032_28_b }, { j := 21, state := 0, first := lowMeanRankExpr0032_29_a, second := lowMeanRankExpr0032_29_b }, { j := 22, state := 0, first := lowMeanRankExpr0032_30_a, second := lowMeanRankExpr0032_30_b }, { j := 23, state := 0, first := lowMeanRankExpr0032_31_a, second := lowMeanRankExpr0032_31_b }, { j := 24, state := 0, first := lowMeanRankExpr0032_32_a, second := lowMeanRankExpr0032_32_b }, { j := 25, state := 0, first := lowMeanRankExpr0032_33_a, second := lowMeanRankExpr0032_33_b }, { j := 26, state := 0, first := lowMeanRankExpr0032_34_a, second := lowMeanRankExpr0032_34_b }, { j := 27, state := 0, first := lowMeanRankExpr0032_35_a, second := lowMeanRankExpr0032_35_b }, { j := 28, state := 0, first := lowMeanRankExpr0032_36_a, second := lowMeanRankExpr0032_36_b }, { j := 29, state := 0, first := lowMeanRankExpr0032_37_a, second := lowMeanRankExpr0032_37_b }, { j := 30, state := 0, first := lowMeanRankExpr0032_38_a, second := lowMeanRankExpr0032_38_b }, { j := 31, state := 0, first := lowMeanRankExpr0032_39_a, second := lowMeanRankExpr0032_39_b }, { j := 32, state := 0, first := lowMeanRankExpr0032_40_a, second := lowMeanRankExpr0032_40_b }, { j := 33, state := 0, first := lowMeanRankExpr0032_41_a, second := lowMeanRankExpr0032_41_b }, { j := 34, state := 0, first := lowMeanRankExpr0032_42_a, second := lowMeanRankExpr0032_42_b }, { j := 35, state := 0, first := lowMeanRankExpr0032_43_a, second := lowMeanRankExpr0032_43_b }, { j := 36, state := 0, first := lowMeanRankExpr0032_44_a, second := lowMeanRankExpr0032_44_b }, { j := 37, state := 0, first := lowMeanRankExpr0032_45_a, second := lowMeanRankExpr0032_45_b }, { j := 38, state := 0, first := lowMeanRankExpr0032_46_a, second := lowMeanRankExpr0032_46_b }, { j := 39, state := 0, first := lowMeanRankExpr0032_47_a, second := lowMeanRankExpr0032_47_b }, { j := 40, state := 0, first := lowMeanRankExpr0032_48_a, second := lowMeanRankExpr0032_48_b }, { j := 41, state := 0, first := lowMeanRankExpr0032_49_a, second := lowMeanRankExpr0032_49_b }, { j := 42, state := 0, first := lowMeanRankExpr0032_50_a, second := lowMeanRankExpr0032_50_b }, { j := 43, state := 0, first := lowMeanRankExpr0032_51_a, second := lowMeanRankExpr0032_51_b }, { j := 44, state := 0, first := lowMeanRankExpr0032_52_a, second := lowMeanRankExpr0032_52_b }, { j := 45, state := 0, first := lowMeanRankExpr0032_53_a, second := lowMeanRankExpr0032_53_b }, { j := 46, state := 0, first := lowMeanRankExpr0032_54_a, second := lowMeanRankExpr0032_54_b }, { j := 47, state := 0, first := lowMeanRankExpr0032_55_a, second := lowMeanRankExpr0032_55_b }] }

noncomputable def lowMeanFiberGroup0031 : List LowMeanFiberInput := [lowMeanFiber0031, lowMeanFiber0032]

end Erdos993Lean.Analytic.V213
