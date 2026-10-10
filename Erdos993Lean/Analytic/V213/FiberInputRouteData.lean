module

public import Erdos993Lean.Analytic.V213.FiberWeightData
public import Erdos993Lean.Analytic.V213.LowMeanCoverageShape

/-!
All55 accepted F06 printed iota identities, literal routing fields and
Part1 ell0 leaves. Actual closed endpoints are read from accepted N44
Params, with no duplicate endpoint or historical D44 cap table.
Data only; source bindings, full interval/skew/rate and route consumers
are separately proved.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

inductive FiberInputIdentity where
  | iota_0 | iota_1 | iota_2 | iota_3 | iota_4 | iota_5 | iota_6 | iota_7 | iota_8 | iota_9 | iota_10 | iota_11 | iota_12 | iota_13 | iota_14 | iota_15 | iota_16 | iota_17 | iota_18 | iota_19 | iota_20 | iota_21 | iota_22 | iota_23 | iota_24 | iota_25 | iota_26 | iota_27 | iota_28 | iota_29 | iota_30 | iota_31 | iota_32 | iota_33 | iota_34 | iota_35 | iota_36 | iota_37 | iota_38 | iota_39 | iota_40 | iota_41 | iota_42 | iota_43 | iota_44 | iota_45 | iota_46 | iota_47 | iota_48 | iota_49 | iota_50 | iota_51 | iota_52 | iota_53 | iota_54

inductive FiberInputClass where
  | c1 | c2 | central | w1 | w2 | w3 | c3 | c4 | c5 | c6 | c7 | c8

inductive FiberInputTail where
  | c1 | c2 | a | b10 | b19 | c | def | g | h40 | h45 | c5 | c6 | c78

structure FiberInputRouteRow where
  printed : String
  iota : ℕ
  kind : FiberInputClass
  mu0 : lowMeanFraction
  c : lowMeanFraction
  ts : lowMeanFraction
  ell0 : lowMeanFraction
  tail : FiberInputTail
  profile : Option FiberRationalProfileIdentity
  weight : Option FiberWeightIdentity
  windows : List ℕ

def fiberInputRouteById : FiberInputIdentity → FiberInputRouteRow
  | .iota_0 => ⟨"F06:iota=0", 0, .c1, (45, 1), (13, 25), (3, 5), (619, 2500), .c1, none, none, [1]⟩
  | .iota_1 => ⟨"F06:iota=1", 1, .c1, (45, 1), (13, 25), (3, 5), (1309, 5000), .c1, none, none, [1]⟩
  | .iota_2 => ⟨"F06:iota=2", 2, .c1, (45, 1), (13, 25), (3, 5), (2793, 10000), .c1, none, none, [1]⟩
  | .iota_3 => ⟨"F06:iota=3", 3, .c2, (50, 1), (27, 50), (69, 100), (751, 2500), .c2, none, none, [2]⟩
  | .iota_4 => ⟨"F06:iota=4", 4, .c2, (50, 1), (27, 50), (69, 100), (643, 2000), .c2, none, none, [2]⟩
  | .iota_5 => ⟨"F06:iota=5", 5, .c2, (50, 1), (27, 50), (69, 100), (339, 1000), .c2, none, none, [2]⟩
  | .iota_6 => ⟨"F06:iota=6", 6, .central, (23, 1), (1, 3), (3, 5), (3531, 10000), .a, some .a, some .a, []⟩
  | .iota_7 => ⟨"F06:iota=7", 7, .central, (23, 1), (1, 3), (3, 5), (459, 1250), .a, some .a, some .a, []⟩
  | .iota_8 => ⟨"F06:iota=8", 8, .central, (23, 1), (1, 3), (3, 5), (953, 2500), .a, some .a, some .a, []⟩
  | .iota_9 => ⟨"F06:iota=9", 9, .central, (23, 1), (1, 3), (3, 5), (1959, 5000), .a, some .a, some .a, []⟩
  | .iota_10 => ⟨"F06:iota=10", 10, .central, (20, 1), (1, 3), (3, 5), (817, 2000), .b10, some .b, some .b, []⟩
  | .iota_11 => ⟨"F06:iota=11", 11, .central, (19, 1), (1, 3), (3, 5), (4059, 10000), .b19, some .b, some .b, []⟩
  | .iota_12 => ⟨"F06:iota=12", 12, .central, (19, 1), (1, 3), (3, 5), (4129, 10000), .b19, some .b, some .b, []⟩
  | .iota_13 => ⟨"F06:iota=13", 13, .central, (19, 1), (1, 3), (3, 5), (4129, 10000), .b19, some .b, some .b, []⟩
  | .iota_14 => ⟨"F06:iota=14", 14, .central, (19, 1), (1, 3), (3, 5), (171, 400), .b19, some .b, some .b, []⟩
  | .iota_15 => ⟨"F06:iota=15", 15, .central, (19, 1), (1, 3), (3, 5), (4199, 10000), .b19, some .b, some .b, []⟩
  | .iota_16 => ⟨"F06:iota=16", 16, .central, (19, 1), (1, 3), (3, 5), (851, 2000), .b19, some .b, some .b, []⟩
  | .iota_17 => ⟨"F06:iota=17", 17, .central, (19, 1), (1, 3), (3, 5), (217, 500), .b19, some .b, some .b, []⟩
  | .iota_18 => ⟨"F06:iota=18", 18, .central, (19, 1), (1, 3), (3, 5), (871, 2000), .b19, some .b, some .b, []⟩
  | .iota_19 => ⟨"F06:iota=19", 19, .central, (19, 1), (1, 3), (3, 5), (173, 400), .b19, some .b, some .b, []⟩
  | .iota_20 => ⟨"F06:iota=20", 20, .central, (19, 1), (1, 3), (3, 5), (871, 2000), .b19, some .b, some .b, []⟩
  | .iota_21 => ⟨"F06:iota=21", 21, .central, (19, 1), (1, 3), (3, 5), (441, 1000), .b19, some .b, some .b, []⟩
  | .iota_22 => ⟨"F06:iota=22", 22, .central, (19, 1), (1, 3), (3, 5), (879, 2000), .b19, some .b, some .b, []⟩
  | .iota_23 => ⟨"F06:iota=23", 23, .central, (19, 1), (1, 3), (3, 5), (889, 2000), .b19, some .b, some .b, []⟩
  | .iota_24 => ⟨"F06:iota=24", 24, .central, (19, 1), (1, 3), (3, 5), (881, 2000), .b19, some .b, some .b, []⟩
  | .iota_25 => ⟨"F06:iota=25", 25, .central, (19, 1), (1, 3), (3, 5), (449, 1000), .b19, some .b, some .b, []⟩
  | .iota_26 => ⟨"F06:iota=26", 26, .central, (19, 1), (1, 3), (3, 5), (901, 2000), .b19, some .b, some .b, []⟩
  | .iota_27 => ⟨"F06:iota=27", 27, .central, (19, 1), (1, 3), (3, 5), (449, 1000), .b19, some .b, some .b, []⟩
  | .iota_28 => ⟨"F06:iota=28", 28, .central, (19, 1), (1, 3), (3, 5), (907, 2000), .b19, some .b, some .b, []⟩
  | .iota_29 => ⟨"F06:iota=29", 29, .central, (19, 1), (1, 3), (3, 5), (113, 250), .b19, some .b, some .b, []⟩
  | .iota_30 => ⟨"F06:iota=30", 30, .central, (20, 1), (1, 3), (3, 5), (907, 2000), .c, some .b, some .c, []⟩
  | .iota_31 => ⟨"F06:iota=31", 31, .w1, (20, 1), (1, 3), (29, 50), (4481, 10000), .c, some .b, some .c, []⟩
  | .iota_32 => ⟨"F06:iota=32", 32, .w1, (21, 1), (1, 3), (29, 50), (4481, 10000), .c, some .b, some .c, []⟩
  | .iota_33 => ⟨"F06:iota=33", 33, .w2, (21, 1), (1, 3), (11, 20), (1129, 2500), .c, some .b, some .c, []⟩
  | .iota_34 => ⟨"F06:iota=34", 34, .w2, (21, 1), (1, 3), (11, 20), (1129, 2500), .c, some .b, some .c, []⟩
  | .iota_35 => ⟨"F06:iota=35", 35, .w2, (22, 1), (1, 3), (11, 20), (1129, 2500), .c, some .b, some .c, []⟩
  | .iota_36 => ⟨"F06:iota=36", 36, .w2, (22, 1), (1, 3), (11, 20), (1129, 2500), .c, some .b, some .c, []⟩
  | .iota_37 => ⟨"F06:iota=37", 37, .w3, (26, 1), (1, 3), (13, 25), (4551, 10000), .def, some .d, some .d, []⟩
  | .iota_38 => ⟨"F06:iota=38", 38, .w3, (32, 1), (1, 3), (13, 25), (23, 50), .def, some .d, some .e, []⟩
  | .iota_39 => ⟨"F06:iota=39", 39, .w3, (36, 1), (1, 3), (13, 25), (37, 80), .def, some .d, some .f, []⟩
  | .iota_40 => ⟨"F06:iota=40", 40, .c3, (50, 1), (1, 3), (11, 25), (4481, 10000), .g, some .g, some .g, []⟩
  | .iota_41 => ⟨"F06:iota=41", 41, .c3, (50, 1), (1, 3), (11, 25), (4481, 10000), .g, some .g, some .g, []⟩
  | .iota_42 => ⟨"F06:iota=42", 42, .c3, (50, 1), (1, 3), (11, 25), (4481, 10000), .g, some .g, some .g, []⟩
  | .iota_43 => ⟨"F06:iota=43", 43, .c3, (50, 1), (1, 3), (11, 25), (1129, 2500), .g, some .g, some .g, []⟩
  | .iota_44 => ⟨"F06:iota=44", 44, .c4, (40, 1), (1, 3), (21, 50), (939, 2000), .h40, some .h, some .h, [3, 4]⟩
  | .iota_45 => ⟨"F06:iota=45", 45, .c4, (45, 1), (1, 3), (21, 50), (47, 100), .h45, some .h, some .h, [3, 4]⟩
  | .iota_46 => ⟨"F06:iota=46", 46, .c4, (50, 1), (1, 3), (21, 50), (941, 2000), .h45, some .h, some .h, [3, 4]⟩
  | .iota_47 => ⟨"F06:iota=47", 47, .c5, (50, 1), (17, 50), (2, 5), (941, 2000), .c5, none, none, [5]⟩
  | .iota_48 => ⟨"F06:iota=48", 48, .c5, (50, 1), (17, 50), (2, 5), (47, 100), .c5, none, none, [5]⟩
  | .iota_49 => ⟨"F06:iota=49", 49, .c5, (50, 1), (17, 50), (2, 5), (47, 100), .c5, none, none, [5]⟩
  | .iota_50 => ⟨"F06:iota=50", 50, .c6, (50, 1), (3, 10), (9, 25), (47, 100), .c6, none, none, [6, 7]⟩
  | .iota_51 => ⟨"F06:iota=51", 51, .c6, (50, 1), (3, 10), (9, 25), (2223, 5000), .c6, none, none, [6, 7]⟩
  | .iota_52 => ⟨"F06:iota=52", 52, .c6, (50, 1), (3, 10), (9, 25), (2223, 5000), .c6, none, none, [6, 7]⟩
  | .iota_53 => ⟨"F06:iota=53", 53, .c7, (50, 1), (1, 4), (33, 100), (269, 625), .c78, none, none, [8, 9]⟩
  | .iota_54 => ⟨"F06:iota=54", 54, .c8, (50, 1), (1, 4), (3, 10), (1129, 2500), .c78, none, none, [10]⟩

def fiberInputPrinted : FiberInputIdentity → String
  | .iota_0 => "F06:iota=0"
  | .iota_1 => "F06:iota=1"
  | .iota_2 => "F06:iota=2"
  | .iota_3 => "F06:iota=3"
  | .iota_4 => "F06:iota=4"
  | .iota_5 => "F06:iota=5"
  | .iota_6 => "F06:iota=6"
  | .iota_7 => "F06:iota=7"
  | .iota_8 => "F06:iota=8"
  | .iota_9 => "F06:iota=9"
  | .iota_10 => "F06:iota=10"
  | .iota_11 => "F06:iota=11"
  | .iota_12 => "F06:iota=12"
  | .iota_13 => "F06:iota=13"
  | .iota_14 => "F06:iota=14"
  | .iota_15 => "F06:iota=15"
  | .iota_16 => "F06:iota=16"
  | .iota_17 => "F06:iota=17"
  | .iota_18 => "F06:iota=18"
  | .iota_19 => "F06:iota=19"
  | .iota_20 => "F06:iota=20"
  | .iota_21 => "F06:iota=21"
  | .iota_22 => "F06:iota=22"
  | .iota_23 => "F06:iota=23"
  | .iota_24 => "F06:iota=24"
  | .iota_25 => "F06:iota=25"
  | .iota_26 => "F06:iota=26"
  | .iota_27 => "F06:iota=27"
  | .iota_28 => "F06:iota=28"
  | .iota_29 => "F06:iota=29"
  | .iota_30 => "F06:iota=30"
  | .iota_31 => "F06:iota=31"
  | .iota_32 => "F06:iota=32"
  | .iota_33 => "F06:iota=33"
  | .iota_34 => "F06:iota=34"
  | .iota_35 => "F06:iota=35"
  | .iota_36 => "F06:iota=36"
  | .iota_37 => "F06:iota=37"
  | .iota_38 => "F06:iota=38"
  | .iota_39 => "F06:iota=39"
  | .iota_40 => "F06:iota=40"
  | .iota_41 => "F06:iota=41"
  | .iota_42 => "F06:iota=42"
  | .iota_43 => "F06:iota=43"
  | .iota_44 => "F06:iota=44"
  | .iota_45 => "F06:iota=45"
  | .iota_46 => "F06:iota=46"
  | .iota_47 => "F06:iota=47"
  | .iota_48 => "F06:iota=48"
  | .iota_49 => "F06:iota=49"
  | .iota_50 => "F06:iota=50"
  | .iota_51 => "F06:iota=51"
  | .iota_52 => "F06:iota=52"
  | .iota_53 => "F06:iota=53"
  | .iota_54 => "F06:iota=54"

def fiberInputIdentityAt : ℕ → FiberInputIdentity
  | 0 => .iota_0
  | 1 => .iota_1
  | 2 => .iota_2
  | 3 => .iota_3
  | 4 => .iota_4
  | 5 => .iota_5
  | 6 => .iota_6
  | 7 => .iota_7
  | 8 => .iota_8
  | 9 => .iota_9
  | 10 => .iota_10
  | 11 => .iota_11
  | 12 => .iota_12
  | 13 => .iota_13
  | 14 => .iota_14
  | 15 => .iota_15
  | 16 => .iota_16
  | 17 => .iota_17
  | 18 => .iota_18
  | 19 => .iota_19
  | 20 => .iota_20
  | 21 => .iota_21
  | 22 => .iota_22
  | 23 => .iota_23
  | 24 => .iota_24
  | 25 => .iota_25
  | 26 => .iota_26
  | 27 => .iota_27
  | 28 => .iota_28
  | 29 => .iota_29
  | 30 => .iota_30
  | 31 => .iota_31
  | 32 => .iota_32
  | 33 => .iota_33
  | 34 => .iota_34
  | 35 => .iota_35
  | 36 => .iota_36
  | 37 => .iota_37
  | 38 => .iota_38
  | 39 => .iota_39
  | 40 => .iota_40
  | 41 => .iota_41
  | 42 => .iota_42
  | 43 => .iota_43
  | 44 => .iota_44
  | 45 => .iota_45
  | 46 => .iota_46
  | 47 => .iota_47
  | 48 => .iota_48
  | 49 => .iota_49
  | 50 => .iota_50
  | 51 => .iota_51
  | 52 => .iota_52
  | 53 => .iota_53
  | _ => .iota_54

def fiberInputIndex : FiberInputIdentity → ℕ
  | .iota_0 => 0
  | .iota_1 => 1
  | .iota_2 => 2
  | .iota_3 => 3
  | .iota_4 => 4
  | .iota_5 => 5
  | .iota_6 => 6
  | .iota_7 => 7
  | .iota_8 => 8
  | .iota_9 => 9
  | .iota_10 => 10
  | .iota_11 => 11
  | .iota_12 => 12
  | .iota_13 => 13
  | .iota_14 => 14
  | .iota_15 => 15
  | .iota_16 => 16
  | .iota_17 => 17
  | .iota_18 => 18
  | .iota_19 => 19
  | .iota_20 => 20
  | .iota_21 => 21
  | .iota_22 => 22
  | .iota_23 => 23
  | .iota_24 => 24
  | .iota_25 => 25
  | .iota_26 => 26
  | .iota_27 => 27
  | .iota_28 => 28
  | .iota_29 => 29
  | .iota_30 => 30
  | .iota_31 => 31
  | .iota_32 => 32
  | .iota_33 => 33
  | .iota_34 => 34
  | .iota_35 => 35
  | .iota_36 => 36
  | .iota_37 => 37
  | .iota_38 => 38
  | .iota_39 => 39
  | .iota_40 => 40
  | .iota_41 => 41
  | .iota_42 => 42
  | .iota_43 => 43
  | .iota_44 => 44
  | .iota_45 => 45
  | .iota_46 => 46
  | .iota_47 => 47
  | .iota_48 => 48
  | .iota_49 => 49
  | .iota_50 => 50
  | .iota_51 => 51
  | .iota_52 => 52
  | .iota_53 => 53
  | .iota_54 => 54

def fiberInputLoFraction (id : FiberInputIdentity) : lowMeanFraction :=
  lowMeanN44LoFraction (fiberInputRouteById id).iota

def fiberInputHiFraction (id : FiberInputIdentity) : lowMeanFraction :=
  lowMeanN44HiFraction (fiberInputRouteById id).iota

end Erdos993Lean.Analytic.V213
