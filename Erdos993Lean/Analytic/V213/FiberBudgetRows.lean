module

public import Erdos993Lean.Analytic.V213.FiberPriceData
public import Erdos993Lean.Analytic.V213.LowMeanCoverageData

/-!
All thirteen accepted F17 printed budget rows, keyed by their own iota
spans (distinct from F16's partition at37). Complete canonical B, strict
budget gap and printed margin trees retain every operation. Actual input
D/theta/mean leaves remain the accepted Part1 records; no second list of
55 epsilon values is introduced. Data only; two ordered checkers follow.

-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

inductive FiberBudgetIdentity where
  | iota_0_5 | iota_6_9 | iota_10_10 | iota_11_29 | iota_30_36 | iota_37_37 | iota_38_39 | iota_40_43 | iota_44_44 | iota_45_46 | iota_47_49 | iota_50_52 | iota_53_54

inductive FiberBudgetRole where
  | budget | strictGap | margin

structure FiberBudgetRow where
  printed : String
  inputLo : ℕ
  inputHi : ℕ
  mu_star : lowMeanFraction
  b : lowMeanFraction
  Theta : lowMeanFraction
  D_star : lowMeanFraction
  R : lowMeanFraction
  B_star : lowMeanFraction
  Z : lowMeanFraction
  printed_gap : lowMeanFraction
  actual_B : lowMeanFraction

def fiberBudgetById : FiberBudgetIdentity → FiberBudgetRow
  | .iota_0_5 => ⟨"F17:iota=0..5", 0, 5, (45, 1), (2, 5), (1, 1), (6, 5), (1, 2), (34, 125), (13, 50), (3, 250), (184, 675)⟩
  | .iota_6_9 => ⟨"F17:iota=6..9", 6, 9, (23, 1), (0, 1), (7, 10), (6, 5), (1, 4), (31, 500), (3, 50), (1, 500), (43, 690)⟩
  | .iota_10_10 => ⟨"F17:iota=10..10", 10, 10, (20, 1), (0, 1), (13, 20), (6, 5), (1, 8), (79, 1000), (77, 1000), (1, 500), (499, 6300)⟩
  | .iota_11_29 => ⟨"F17:iota=11..29", 11, 29, (19, 1), (0, 1), (3, 5), (6, 5), (1, 8), (57, 500), (11, 100), (1, 250), (688, 5985)⟩
  | .iota_30_36 => ⟨"F17:iota=30..36", 30, 36, (20, 1), (0, 1), (3, 5), (6, 5), (1, 8), (129, 1000), (1, 8), (1, 250), (407, 3150)⟩
  | .iota_37_37 => ⟨"F17:iota=37..37", 37, 37, (26, 1), (0, 1), (3, 5), (6, 5), (1, 6), (191, 1000), (1, 10), (91, 1000), (87, 455)⟩
  | .iota_38_39 => ⟨"F17:iota=38..39", 38, 39, (32, 1), (0, 1), (7, 10), (7, 5), (1, 6), (51, 500), (1, 10), (1, 500), (229, 2240)⟩
  | .iota_40_43 => ⟨"F17:iota=40..43", 40, 43, (50, 1), (0, 1), (7, 10), (8, 5), (1, 4), (77, 500), (3, 25), (17, 500), (58, 375)⟩
  | .iota_44_44 => ⟨"F17:iota=44..44", 44, 44, (40, 1), (3, 20), (9, 10), (8, 5), (7, 25), (67, 1000), (53, 1000), (7, 500), (7819, 115200)⟩
  | .iota_45_46 => ⟨"F17:iota=45..46", 45, 46, (45, 1), (3, 20), (19, 20), (8, 5), (7, 25), (19, 500), (17, 500), (1, 250), (4939, 129600)⟩
  | .iota_47_49 => ⟨"F17:iota=47..49", 47, 49, (50, 1), (3, 10), (1, 1), (9, 5), (2, 5), (67, 500), (11, 100), (3, 125), (1409, 10500)⟩
  | .iota_50_52 => ⟨"F17:iota=50..52", 50, 52, (50, 1), (3, 10), (1, 1), (21, 10), (2, 5), (107, 1000), (3, 50), (47, 1000), (2251, 21000)⟩
  | .iota_53_54 => ⟨"F17:iota=53..54", 53, 54, (50, 1), (3, 10), (1, 1), (21, 10), (2, 5), (107, 1000), (1, 10), (7, 1000), (2251, 21000)⟩

def fiberBudgetIdentityAt : ℕ → FiberBudgetIdentity
  | 0 => .iota_0_5
  | 1 => .iota_6_9
  | 2 => .iota_10_10
  | 3 => .iota_11_29
  | 4 => .iota_30_36
  | 5 => .iota_37_37
  | 6 => .iota_38_39
  | 7 => .iota_40_43
  | 8 => .iota_44_44
  | 9 => .iota_45_46
  | 10 => .iota_47_49
  | 11 => .iota_50_52
  | _ => .iota_53_54

def fiberBudgetIndex : FiberBudgetIdentity → ℕ
  | .iota_0_5 => 0
  | .iota_6_9 => 1
  | .iota_10_10 => 2
  | .iota_11_29 => 3
  | .iota_30_36 => 4
  | .iota_37_37 => 5
  | .iota_38_39 => 6
  | .iota_40_43 => 7
  | .iota_44_44 => 8
  | .iota_45_46 => 9
  | .iota_47_49 => 10
  | .iota_50_52 => 11
  | .iota_53_54 => 12

def fiberBudgetPrinted : FiberBudgetIdentity → String
  | .iota_0_5 => "F17:iota=0..5"
  | .iota_6_9 => "F17:iota=6..9"
  | .iota_10_10 => "F17:iota=10..10"
  | .iota_11_29 => "F17:iota=11..29"
  | .iota_30_36 => "F17:iota=30..36"
  | .iota_37_37 => "F17:iota=37..37"
  | .iota_38_39 => "F17:iota=38..39"
  | .iota_40_43 => "F17:iota=40..43"
  | .iota_44_44 => "F17:iota=44..44"
  | .iota_45_46 => "F17:iota=45..46"
  | .iota_47_49 => "F17:iota=47..49"
  | .iota_50_52 => "F17:iota=50..52"
  | .iota_53_54 => "F17:iota=53..54"

def fiberInputBudget : FiberInputIdentity → FiberBudgetIdentity
  | .iota_0 => .iota_0_5
  | .iota_1 => .iota_0_5
  | .iota_2 => .iota_0_5
  | .iota_3 => .iota_0_5
  | .iota_4 => .iota_0_5
  | .iota_5 => .iota_0_5
  | .iota_6 => .iota_6_9
  | .iota_7 => .iota_6_9
  | .iota_8 => .iota_6_9
  | .iota_9 => .iota_6_9
  | .iota_10 => .iota_10_10
  | .iota_11 => .iota_11_29
  | .iota_12 => .iota_11_29
  | .iota_13 => .iota_11_29
  | .iota_14 => .iota_11_29
  | .iota_15 => .iota_11_29
  | .iota_16 => .iota_11_29
  | .iota_17 => .iota_11_29
  | .iota_18 => .iota_11_29
  | .iota_19 => .iota_11_29
  | .iota_20 => .iota_11_29
  | .iota_21 => .iota_11_29
  | .iota_22 => .iota_11_29
  | .iota_23 => .iota_11_29
  | .iota_24 => .iota_11_29
  | .iota_25 => .iota_11_29
  | .iota_26 => .iota_11_29
  | .iota_27 => .iota_11_29
  | .iota_28 => .iota_11_29
  | .iota_29 => .iota_11_29
  | .iota_30 => .iota_30_36
  | .iota_31 => .iota_30_36
  | .iota_32 => .iota_30_36
  | .iota_33 => .iota_30_36
  | .iota_34 => .iota_30_36
  | .iota_35 => .iota_30_36
  | .iota_36 => .iota_30_36
  | .iota_37 => .iota_37_37
  | .iota_38 => .iota_38_39
  | .iota_39 => .iota_38_39
  | .iota_40 => .iota_40_43
  | .iota_41 => .iota_40_43
  | .iota_42 => .iota_40_43
  | .iota_43 => .iota_40_43
  | .iota_44 => .iota_44_44
  | .iota_45 => .iota_45_46
  | .iota_46 => .iota_45_46
  | .iota_47 => .iota_47_49
  | .iota_48 => .iota_47_49
  | .iota_49 => .iota_47_49
  | .iota_50 => .iota_50_52
  | .iota_51 => .iota_50_52
  | .iota_52 => .iota_50_52
  | .iota_53 => .iota_53_54
  | .iota_54 => .iota_53_54

def fiberInputPaperRow (id : FiberInputIdentity) : LowMeanInputRow :=
  lowMeanInputRowAt (fiberInputIndex id)

end Erdos993Lean.Analytic.V213
