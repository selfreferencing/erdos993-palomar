module

public import Erdos993Lean.Analytic.V213.FiberTailInputDomain
public import Erdos993Lean.Analytic.V213.FiberWindowInputData

/-!
Accepted F16 thirteen printed maximum-price groups.  Every component is
read from the actual accepted F15 tail, F11 weight or F13 window/corner
record.  The group identity is its printed iota span; enumeration is only
for exhaustive checking.  No sum of prices or duplicate component table.
Data only; the kernel checks are in a separate module.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

inductive FiberPriceGroupIdentity where
  | iota_0_5 | iota_6_9 | iota_10_10 | iota_11_29 | iota_30_36 | iota_37_39 | iota_40_43 | iota_44_44 | iota_45_46 | iota_47_49 | iota_50_52 | iota_53_53 | iota_54_54

structure FiberPriceGroupRow where
  printed : String
  inputLo : ℕ
  inputHi : ℕ
  z : lowMeanFraction

def fiberPriceGroupById : FiberPriceGroupIdentity → FiberPriceGroupRow
  | .iota_0_5 => ⟨"F16:iota=0..5", 0, 5, (13, 50)⟩
  | .iota_6_9 => ⟨"F16:iota=6..9", 6, 9, (3, 50)⟩
  | .iota_10_10 => ⟨"F16:iota=10..10", 10, 10, (77, 1000)⟩
  | .iota_11_29 => ⟨"F16:iota=11..29", 11, 29, (11, 100)⟩
  | .iota_30_36 => ⟨"F16:iota=30..36", 30, 36, (1, 8)⟩
  | .iota_37_39 => ⟨"F16:iota=37..39", 37, 39, (1, 10)⟩
  | .iota_40_43 => ⟨"F16:iota=40..43", 40, 43, (3, 25)⟩
  | .iota_44_44 => ⟨"F16:iota=44..44", 44, 44, (53, 1000)⟩
  | .iota_45_46 => ⟨"F16:iota=45..46", 45, 46, (17, 500)⟩
  | .iota_47_49 => ⟨"F16:iota=47..49", 47, 49, (11, 100)⟩
  | .iota_50_52 => ⟨"F16:iota=50..52", 50, 52, (3, 50)⟩
  | .iota_53_53 => ⟨"F16:iota=53..53", 53, 53, (1, 10)⟩
  | .iota_54_54 => ⟨"F16:iota=54..54", 54, 54, (1, 25)⟩

def fiberInputPriceGroup : FiberInputIdentity → FiberPriceGroupIdentity
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
  | .iota_37 => .iota_37_39
  | .iota_38 => .iota_37_39
  | .iota_39 => .iota_37_39
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
  | .iota_53 => .iota_53_53
  | .iota_54 => .iota_54_54

def fiberWindowPriceFraction : FiberWindowIdentity → lowMeanFraction
  | .window1 => (fiberWindowById .window1).L_W
  | .window2 => (fiberWindowById .window2).L_W
  | .window3 => (fiberWindowCornerById (fiberWindowWeightById .window3).corner).Z_W
  | .window4 => (fiberWindowCornerById (fiberWindowWeightById .window4).corner).Z_W
  | .window5 => (fiberWindowCornerById (fiberWindowWeightById .window5).corner).Z_W
  | .window6 => (fiberWindowCornerById (fiberWindowWeightById .window6).corner).Z_W
  | .window7 => (fiberWindowCornerById (fiberWindowWeightById .window7).corner).Z_W
  | .window8 => (fiberWindowCornerById (fiberWindowWeightById .window8).corner).Z_W
  | .window9 => (fiberWindowCornerById (fiberWindowWeightById .window9).corner).Z_W
  | .window10 => (fiberWindowCornerById (fiberWindowWeightById .window10).corner).Z_W

def fiberInputPriceComponents (id : FiberInputIdentity) : List lowMeanFraction :=
  [(fiberTailById (fiberInputTail id)).Z_a,
    (fiberTailById (fiberInputTail id)).Z_small] ++
  (match (fiberInputRouteById id).weight with
    | none => []
    | some wid => [(fiberWeightById wid).eta_w]) ++
  (match id with
    | .iota_0 => [fiberWindowPriceFraction .window1]
    | .iota_1 => [fiberWindowPriceFraction .window1]
    | .iota_2 => [fiberWindowPriceFraction .window1]
    | .iota_3 => [fiberWindowPriceFraction .window2]
    | .iota_4 => [fiberWindowPriceFraction .window2]
    | .iota_5 => [fiberWindowPriceFraction .window2]
    | .iota_6 => []
    | .iota_7 => []
    | .iota_8 => []
    | .iota_9 => []
    | .iota_10 => []
    | .iota_11 => []
    | .iota_12 => []
    | .iota_13 => []
    | .iota_14 => []
    | .iota_15 => []
    | .iota_16 => []
    | .iota_17 => []
    | .iota_18 => []
    | .iota_19 => []
    | .iota_20 => []
    | .iota_21 => []
    | .iota_22 => []
    | .iota_23 => []
    | .iota_24 => []
    | .iota_25 => []
    | .iota_26 => []
    | .iota_27 => []
    | .iota_28 => []
    | .iota_29 => []
    | .iota_30 => []
    | .iota_31 => []
    | .iota_32 => []
    | .iota_33 => []
    | .iota_34 => []
    | .iota_35 => []
    | .iota_36 => []
    | .iota_37 => []
    | .iota_38 => []
    | .iota_39 => []
    | .iota_40 => []
    | .iota_41 => []
    | .iota_42 => []
    | .iota_43 => []
    | .iota_44 => [fiberWindowPriceFraction .window3, fiberWindowPriceFraction .window4]
    | .iota_45 => [fiberWindowPriceFraction .window3, fiberWindowPriceFraction .window4]
    | .iota_46 => [fiberWindowPriceFraction .window3, fiberWindowPriceFraction .window4]
    | .iota_47 => [fiberWindowPriceFraction .window5]
    | .iota_48 => [fiberWindowPriceFraction .window5]
    | .iota_49 => [fiberWindowPriceFraction .window5]
    | .iota_50 => [fiberWindowPriceFraction .window6, fiberWindowPriceFraction .window7]
    | .iota_51 => [fiberWindowPriceFraction .window6, fiberWindowPriceFraction .window7]
    | .iota_52 => [fiberWindowPriceFraction .window6, fiberWindowPriceFraction .window7]
    | .iota_53 => [fiberWindowPriceFraction .window8, fiberWindowPriceFraction .window9]
    | .iota_54 => [fiberWindowPriceFraction .window10])

def fiberInputPriceFraction (id : FiberInputIdentity) : lowMeanFraction :=
  (fiberPriceGroupById (fiberInputPriceGroup id)).z

end Erdos993Lean.Analytic.V213
