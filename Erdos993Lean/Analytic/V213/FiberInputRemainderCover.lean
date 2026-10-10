module

public import Erdos993Lean.Analytic.V213.FiberWindowInputPrices

/-!
Actual gapless closed coverage after the two tail branches.  Every input
uses its actual F06 cut and strict spike endpoint, actual F11 profile cap
and actual F13 window endpoints.  In particular H stops at19/50; windows
3 and4 cover the remaining range.  Overlapping seams are both allowed.

-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

def FiberInputProfileRoute (id : FiberInputIdentity) (t : ℝ) : Prop :=
  ∃ aid : FiberAnalyticInputIdentity, fiberAnalyticInput aid = id ∧
    1/3 ≤ t ∧ t ≤ fiberProfileTimeCap (fiberWeightById (fiberAnalyticWeight aid)).profile

def FiberInputCoupledWindowRoute (id : FiberInputIdentity) (t : ℝ) : Prop :=
  ∃ rid : FiberCornerRateIdentity, (fiberCornerRateById rid).input = id ∧
    lowMeanFractionReal (fiberWindowById (fiberCornerRateWindow rid)).l ≤ t ∧
    t ≤ lowMeanFractionReal (fiberWindowById (fiberCornerRateWindow rid)).h

def FiberInputWeightedWindowRoute (id : FiberInputIdentity) (t : ℝ) : Prop :=
  ∃ iid : FiberWindowInputIdentity, ∃ wid : FiberWindowWeightIdentity,
    fiberWindowInput iid = id ∧
    (fiberWindowWeightById wid).window ∈ fiberWindowInputWindows iid ∧
    fiberWindowInputCorner iid = some (fiberWindowWeightById wid).corner ∧
    lowMeanFractionReal (fiberWindowById (fiberWindowWeightById wid).window).l ≤ t ∧
    t ≤ lowMeanFractionReal (fiberWindowById (fiberWindowWeightById wid).window).h

theorem fiber_input_remainder_cover (id : FiberInputIdentity) {t : ℝ}
    (hc : lowMeanFractionReal (fiberInputRouteById id).c ≤ t)
    (hts : t ≤ lowMeanFractionReal (fiberInputRouteById id).ts) :
    FiberInputProfileRoute id t ∨ FiberInputCoupledWindowRoute id t ∨
      FiberInputWeightedWindowRoute id t := by
  cases id with
  | iota_0 =>
    refine Or.inr (Or.inl ⟨.iota0, rfl, ?_, ?_⟩) <;>
      norm_num [fiberInputRouteById, fiberAnalyticWeight, fiberWeightById,
        fiberProfileTimeCap, fiberCornerRateWindow, fiberCornerRateById,
        fiberWindowById, fiberWindowWeightById, lowMeanFractionReal] at hc hts ⊢ <;>
        linarith only [hc,hts]
  | iota_1 =>
    refine Or.inr (Or.inl ⟨.iota1, rfl, ?_, ?_⟩) <;>
      norm_num [fiberInputRouteById, fiberAnalyticWeight, fiberWeightById,
        fiberProfileTimeCap, fiberCornerRateWindow, fiberCornerRateById,
        fiberWindowById, fiberWindowWeightById, lowMeanFractionReal] at hc hts ⊢ <;>
        linarith only [hc,hts]
  | iota_2 =>
    refine Or.inr (Or.inl ⟨.iota2, rfl, ?_, ?_⟩) <;>
      norm_num [fiberInputRouteById, fiberAnalyticWeight, fiberWeightById,
        fiberProfileTimeCap, fiberCornerRateWindow, fiberCornerRateById,
        fiberWindowById, fiberWindowWeightById, lowMeanFractionReal] at hc hts ⊢ <;>
        linarith only [hc,hts]
  | iota_3 =>
    refine Or.inr (Or.inl ⟨.iota3, rfl, ?_, ?_⟩) <;>
      norm_num [fiberInputRouteById, fiberAnalyticWeight, fiberWeightById,
        fiberProfileTimeCap, fiberCornerRateWindow, fiberCornerRateById,
        fiberWindowById, fiberWindowWeightById, lowMeanFractionReal] at hc hts ⊢ <;>
        linarith only [hc,hts]
  | iota_4 =>
    refine Or.inr (Or.inl ⟨.iota4, rfl, ?_, ?_⟩) <;>
      norm_num [fiberInputRouteById, fiberAnalyticWeight, fiberWeightById,
        fiberProfileTimeCap, fiberCornerRateWindow, fiberCornerRateById,
        fiberWindowById, fiberWindowWeightById, lowMeanFractionReal] at hc hts ⊢ <;>
        linarith only [hc,hts]
  | iota_5 =>
    refine Or.inr (Or.inl ⟨.iota5, rfl, ?_, ?_⟩) <;>
      norm_num [fiberInputRouteById, fiberAnalyticWeight, fiberWeightById,
        fiberProfileTimeCap, fiberCornerRateWindow, fiberCornerRateById,
        fiberWindowById, fiberWindowWeightById, lowMeanFractionReal] at hc hts ⊢ <;>
        linarith only [hc,hts]
  | iota_6 =>
    refine Or.inl ⟨.iota_6, rfl, ?_, ?_⟩ <;>
      norm_num [fiberInputRouteById, fiberAnalyticWeight, fiberWeightById,
        fiberProfileTimeCap, fiberCornerRateWindow, fiberCornerRateById,
        fiberWindowById, fiberWindowWeightById, lowMeanFractionReal] at hc hts ⊢ <;>
        linarith only [hc,hts]
  | iota_7 =>
    refine Or.inl ⟨.iota_7, rfl, ?_, ?_⟩ <;>
      norm_num [fiberInputRouteById, fiberAnalyticWeight, fiberWeightById,
        fiberProfileTimeCap, fiberCornerRateWindow, fiberCornerRateById,
        fiberWindowById, fiberWindowWeightById, lowMeanFractionReal] at hc hts ⊢ <;>
        linarith only [hc,hts]
  | iota_8 =>
    refine Or.inl ⟨.iota_8, rfl, ?_, ?_⟩ <;>
      norm_num [fiberInputRouteById, fiberAnalyticWeight, fiberWeightById,
        fiberProfileTimeCap, fiberCornerRateWindow, fiberCornerRateById,
        fiberWindowById, fiberWindowWeightById, lowMeanFractionReal] at hc hts ⊢ <;>
        linarith only [hc,hts]
  | iota_9 =>
    refine Or.inl ⟨.iota_9, rfl, ?_, ?_⟩ <;>
      norm_num [fiberInputRouteById, fiberAnalyticWeight, fiberWeightById,
        fiberProfileTimeCap, fiberCornerRateWindow, fiberCornerRateById,
        fiberWindowById, fiberWindowWeightById, lowMeanFractionReal] at hc hts ⊢ <;>
        linarith only [hc,hts]
  | iota_10 =>
    refine Or.inl ⟨.iota_10, rfl, ?_, ?_⟩ <;>
      norm_num [fiberInputRouteById, fiberAnalyticWeight, fiberWeightById,
        fiberProfileTimeCap, fiberCornerRateWindow, fiberCornerRateById,
        fiberWindowById, fiberWindowWeightById, lowMeanFractionReal] at hc hts ⊢ <;>
        linarith only [hc,hts]
  | iota_11 =>
    refine Or.inl ⟨.iota_11, rfl, ?_, ?_⟩ <;>
      norm_num [fiberInputRouteById, fiberAnalyticWeight, fiberWeightById,
        fiberProfileTimeCap, fiberCornerRateWindow, fiberCornerRateById,
        fiberWindowById, fiberWindowWeightById, lowMeanFractionReal] at hc hts ⊢ <;>
        linarith only [hc,hts]
  | iota_12 =>
    refine Or.inl ⟨.iota_12, rfl, ?_, ?_⟩ <;>
      norm_num [fiberInputRouteById, fiberAnalyticWeight, fiberWeightById,
        fiberProfileTimeCap, fiberCornerRateWindow, fiberCornerRateById,
        fiberWindowById, fiberWindowWeightById, lowMeanFractionReal] at hc hts ⊢ <;>
        linarith only [hc,hts]
  | iota_13 =>
    refine Or.inl ⟨.iota_13, rfl, ?_, ?_⟩ <;>
      norm_num [fiberInputRouteById, fiberAnalyticWeight, fiberWeightById,
        fiberProfileTimeCap, fiberCornerRateWindow, fiberCornerRateById,
        fiberWindowById, fiberWindowWeightById, lowMeanFractionReal] at hc hts ⊢ <;>
        linarith only [hc,hts]
  | iota_14 =>
    refine Or.inl ⟨.iota_14, rfl, ?_, ?_⟩ <;>
      norm_num [fiberInputRouteById, fiberAnalyticWeight, fiberWeightById,
        fiberProfileTimeCap, fiberCornerRateWindow, fiberCornerRateById,
        fiberWindowById, fiberWindowWeightById, lowMeanFractionReal] at hc hts ⊢ <;>
        linarith only [hc,hts]
  | iota_15 =>
    refine Or.inl ⟨.iota_15, rfl, ?_, ?_⟩ <;>
      norm_num [fiberInputRouteById, fiberAnalyticWeight, fiberWeightById,
        fiberProfileTimeCap, fiberCornerRateWindow, fiberCornerRateById,
        fiberWindowById, fiberWindowWeightById, lowMeanFractionReal] at hc hts ⊢ <;>
        linarith only [hc,hts]
  | iota_16 =>
    refine Or.inl ⟨.iota_16, rfl, ?_, ?_⟩ <;>
      norm_num [fiberInputRouteById, fiberAnalyticWeight, fiberWeightById,
        fiberProfileTimeCap, fiberCornerRateWindow, fiberCornerRateById,
        fiberWindowById, fiberWindowWeightById, lowMeanFractionReal] at hc hts ⊢ <;>
        linarith only [hc,hts]
  | iota_17 =>
    refine Or.inl ⟨.iota_17, rfl, ?_, ?_⟩ <;>
      norm_num [fiberInputRouteById, fiberAnalyticWeight, fiberWeightById,
        fiberProfileTimeCap, fiberCornerRateWindow, fiberCornerRateById,
        fiberWindowById, fiberWindowWeightById, lowMeanFractionReal] at hc hts ⊢ <;>
        linarith only [hc,hts]
  | iota_18 =>
    refine Or.inl ⟨.iota_18, rfl, ?_, ?_⟩ <;>
      norm_num [fiberInputRouteById, fiberAnalyticWeight, fiberWeightById,
        fiberProfileTimeCap, fiberCornerRateWindow, fiberCornerRateById,
        fiberWindowById, fiberWindowWeightById, lowMeanFractionReal] at hc hts ⊢ <;>
        linarith only [hc,hts]
  | iota_19 =>
    refine Or.inl ⟨.iota_19, rfl, ?_, ?_⟩ <;>
      norm_num [fiberInputRouteById, fiberAnalyticWeight, fiberWeightById,
        fiberProfileTimeCap, fiberCornerRateWindow, fiberCornerRateById,
        fiberWindowById, fiberWindowWeightById, lowMeanFractionReal] at hc hts ⊢ <;>
        linarith only [hc,hts]
  | iota_20 =>
    refine Or.inl ⟨.iota_20, rfl, ?_, ?_⟩ <;>
      norm_num [fiberInputRouteById, fiberAnalyticWeight, fiberWeightById,
        fiberProfileTimeCap, fiberCornerRateWindow, fiberCornerRateById,
        fiberWindowById, fiberWindowWeightById, lowMeanFractionReal] at hc hts ⊢ <;>
        linarith only [hc,hts]
  | iota_21 =>
    refine Or.inl ⟨.iota_21, rfl, ?_, ?_⟩ <;>
      norm_num [fiberInputRouteById, fiberAnalyticWeight, fiberWeightById,
        fiberProfileTimeCap, fiberCornerRateWindow, fiberCornerRateById,
        fiberWindowById, fiberWindowWeightById, lowMeanFractionReal] at hc hts ⊢ <;>
        linarith only [hc,hts]
  | iota_22 =>
    refine Or.inl ⟨.iota_22, rfl, ?_, ?_⟩ <;>
      norm_num [fiberInputRouteById, fiberAnalyticWeight, fiberWeightById,
        fiberProfileTimeCap, fiberCornerRateWindow, fiberCornerRateById,
        fiberWindowById, fiberWindowWeightById, lowMeanFractionReal] at hc hts ⊢ <;>
        linarith only [hc,hts]
  | iota_23 =>
    refine Or.inl ⟨.iota_23, rfl, ?_, ?_⟩ <;>
      norm_num [fiberInputRouteById, fiberAnalyticWeight, fiberWeightById,
        fiberProfileTimeCap, fiberCornerRateWindow, fiberCornerRateById,
        fiberWindowById, fiberWindowWeightById, lowMeanFractionReal] at hc hts ⊢ <;>
        linarith only [hc,hts]
  | iota_24 =>
    refine Or.inl ⟨.iota_24, rfl, ?_, ?_⟩ <;>
      norm_num [fiberInputRouteById, fiberAnalyticWeight, fiberWeightById,
        fiberProfileTimeCap, fiberCornerRateWindow, fiberCornerRateById,
        fiberWindowById, fiberWindowWeightById, lowMeanFractionReal] at hc hts ⊢ <;>
        linarith only [hc,hts]
  | iota_25 =>
    refine Or.inl ⟨.iota_25, rfl, ?_, ?_⟩ <;>
      norm_num [fiberInputRouteById, fiberAnalyticWeight, fiberWeightById,
        fiberProfileTimeCap, fiberCornerRateWindow, fiberCornerRateById,
        fiberWindowById, fiberWindowWeightById, lowMeanFractionReal] at hc hts ⊢ <;>
        linarith only [hc,hts]
  | iota_26 =>
    refine Or.inl ⟨.iota_26, rfl, ?_, ?_⟩ <;>
      norm_num [fiberInputRouteById, fiberAnalyticWeight, fiberWeightById,
        fiberProfileTimeCap, fiberCornerRateWindow, fiberCornerRateById,
        fiberWindowById, fiberWindowWeightById, lowMeanFractionReal] at hc hts ⊢ <;>
        linarith only [hc,hts]
  | iota_27 =>
    refine Or.inl ⟨.iota_27, rfl, ?_, ?_⟩ <;>
      norm_num [fiberInputRouteById, fiberAnalyticWeight, fiberWeightById,
        fiberProfileTimeCap, fiberCornerRateWindow, fiberCornerRateById,
        fiberWindowById, fiberWindowWeightById, lowMeanFractionReal] at hc hts ⊢ <;>
        linarith only [hc,hts]
  | iota_28 =>
    refine Or.inl ⟨.iota_28, rfl, ?_, ?_⟩ <;>
      norm_num [fiberInputRouteById, fiberAnalyticWeight, fiberWeightById,
        fiberProfileTimeCap, fiberCornerRateWindow, fiberCornerRateById,
        fiberWindowById, fiberWindowWeightById, lowMeanFractionReal] at hc hts ⊢ <;>
        linarith only [hc,hts]
  | iota_29 =>
    refine Or.inl ⟨.iota_29, rfl, ?_, ?_⟩ <;>
      norm_num [fiberInputRouteById, fiberAnalyticWeight, fiberWeightById,
        fiberProfileTimeCap, fiberCornerRateWindow, fiberCornerRateById,
        fiberWindowById, fiberWindowWeightById, lowMeanFractionReal] at hc hts ⊢ <;>
        linarith only [hc,hts]
  | iota_30 =>
    refine Or.inl ⟨.iota_30, rfl, ?_, ?_⟩ <;>
      norm_num [fiberInputRouteById, fiberAnalyticWeight, fiberWeightById,
        fiberProfileTimeCap, fiberCornerRateWindow, fiberCornerRateById,
        fiberWindowById, fiberWindowWeightById, lowMeanFractionReal] at hc hts ⊢ <;>
        linarith only [hc,hts]
  | iota_31 =>
    refine Or.inl ⟨.iota_31, rfl, ?_, ?_⟩ <;>
      norm_num [fiberInputRouteById, fiberAnalyticWeight, fiberWeightById,
        fiberProfileTimeCap, fiberCornerRateWindow, fiberCornerRateById,
        fiberWindowById, fiberWindowWeightById, lowMeanFractionReal] at hc hts ⊢ <;>
        linarith only [hc,hts]
  | iota_32 =>
    refine Or.inl ⟨.iota_32, rfl, ?_, ?_⟩ <;>
      norm_num [fiberInputRouteById, fiberAnalyticWeight, fiberWeightById,
        fiberProfileTimeCap, fiberCornerRateWindow, fiberCornerRateById,
        fiberWindowById, fiberWindowWeightById, lowMeanFractionReal] at hc hts ⊢ <;>
        linarith only [hc,hts]
  | iota_33 =>
    refine Or.inl ⟨.iota_33, rfl, ?_, ?_⟩ <;>
      norm_num [fiberInputRouteById, fiberAnalyticWeight, fiberWeightById,
        fiberProfileTimeCap, fiberCornerRateWindow, fiberCornerRateById,
        fiberWindowById, fiberWindowWeightById, lowMeanFractionReal] at hc hts ⊢ <;>
        linarith only [hc,hts]
  | iota_34 =>
    refine Or.inl ⟨.iota_34, rfl, ?_, ?_⟩ <;>
      norm_num [fiberInputRouteById, fiberAnalyticWeight, fiberWeightById,
        fiberProfileTimeCap, fiberCornerRateWindow, fiberCornerRateById,
        fiberWindowById, fiberWindowWeightById, lowMeanFractionReal] at hc hts ⊢ <;>
        linarith only [hc,hts]
  | iota_35 =>
    refine Or.inl ⟨.iota_35, rfl, ?_, ?_⟩ <;>
      norm_num [fiberInputRouteById, fiberAnalyticWeight, fiberWeightById,
        fiberProfileTimeCap, fiberCornerRateWindow, fiberCornerRateById,
        fiberWindowById, fiberWindowWeightById, lowMeanFractionReal] at hc hts ⊢ <;>
        linarith only [hc,hts]
  | iota_36 =>
    refine Or.inl ⟨.iota_36, rfl, ?_, ?_⟩ <;>
      norm_num [fiberInputRouteById, fiberAnalyticWeight, fiberWeightById,
        fiberProfileTimeCap, fiberCornerRateWindow, fiberCornerRateById,
        fiberWindowById, fiberWindowWeightById, lowMeanFractionReal] at hc hts ⊢ <;>
        linarith only [hc,hts]
  | iota_37 =>
    refine Or.inl ⟨.iota_37, rfl, ?_, ?_⟩ <;>
      norm_num [fiberInputRouteById, fiberAnalyticWeight, fiberWeightById,
        fiberProfileTimeCap, fiberCornerRateWindow, fiberCornerRateById,
        fiberWindowById, fiberWindowWeightById, lowMeanFractionReal] at hc hts ⊢ <;>
        linarith only [hc,hts]
  | iota_38 =>
    refine Or.inl ⟨.iota_38, rfl, ?_, ?_⟩ <;>
      norm_num [fiberInputRouteById, fiberAnalyticWeight, fiberWeightById,
        fiberProfileTimeCap, fiberCornerRateWindow, fiberCornerRateById,
        fiberWindowById, fiberWindowWeightById, lowMeanFractionReal] at hc hts ⊢ <;>
        linarith only [hc,hts]
  | iota_39 =>
    refine Or.inl ⟨.iota_39, rfl, ?_, ?_⟩ <;>
      norm_num [fiberInputRouteById, fiberAnalyticWeight, fiberWeightById,
        fiberProfileTimeCap, fiberCornerRateWindow, fiberCornerRateById,
        fiberWindowById, fiberWindowWeightById, lowMeanFractionReal] at hc hts ⊢ <;>
        linarith only [hc,hts]
  | iota_40 =>
    refine Or.inl ⟨.iota_40, rfl, ?_, ?_⟩ <;>
      norm_num [fiberInputRouteById, fiberAnalyticWeight, fiberWeightById,
        fiberProfileTimeCap, fiberCornerRateWindow, fiberCornerRateById,
        fiberWindowById, fiberWindowWeightById, lowMeanFractionReal] at hc hts ⊢ <;>
        linarith only [hc,hts]
  | iota_41 =>
    refine Or.inl ⟨.iota_41, rfl, ?_, ?_⟩ <;>
      norm_num [fiberInputRouteById, fiberAnalyticWeight, fiberWeightById,
        fiberProfileTimeCap, fiberCornerRateWindow, fiberCornerRateById,
        fiberWindowById, fiberWindowWeightById, lowMeanFractionReal] at hc hts ⊢ <;>
        linarith only [hc,hts]
  | iota_42 =>
    refine Or.inl ⟨.iota_42, rfl, ?_, ?_⟩ <;>
      norm_num [fiberInputRouteById, fiberAnalyticWeight, fiberWeightById,
        fiberProfileTimeCap, fiberCornerRateWindow, fiberCornerRateById,
        fiberWindowById, fiberWindowWeightById, lowMeanFractionReal] at hc hts ⊢ <;>
        linarith only [hc,hts]
  | iota_43 =>
    refine Or.inl ⟨.iota_43, rfl, ?_, ?_⟩ <;>
      norm_num [fiberInputRouteById, fiberAnalyticWeight, fiberWeightById,
        fiberProfileTimeCap, fiberCornerRateWindow, fiberCornerRateById,
        fiberWindowById, fiberWindowWeightById, lowMeanFractionReal] at hc hts ⊢ <;>
        linarith only [hc,hts]
  | iota_44 =>
    norm_num [fiberInputRouteById,lowMeanFractionReal] at hc hts
    by_cases hp : t ≤ 19/50
    · refine Or.inl ⟨.iota_44, rfl, hc, ?_⟩
      simpa [fiberAnalyticWeight,fiberWeightById,fiberProfileTimeCap] using hp
    · by_cases hw : t ≤ 2/5
      · refine Or.inr (Or.inr ⟨.iota44, .window3, rfl, ?_, rfl, ?_, ?_⟩)
        · simp [fiberWindowInputWindows,fiberWindowWeightById]
        · norm_num [fiberWindowById,fiberWindowWeightById,lowMeanFractionReal] at * <;> linarith
        · norm_num [fiberWindowById,fiberWindowWeightById,lowMeanFractionReal] at * <;> linarith
      · refine Or.inr (Or.inr ⟨.iota44, .window4, rfl, ?_, rfl, ?_, ?_⟩)
        · simp [fiberWindowInputWindows,fiberWindowWeightById]
        · norm_num [fiberWindowById,fiberWindowWeightById,lowMeanFractionReal] at * <;> linarith
        · norm_num [fiberWindowById,fiberWindowWeightById,lowMeanFractionReal] at * <;> linarith
  | iota_45 =>
    norm_num [fiberInputRouteById,lowMeanFractionReal] at hc hts
    by_cases hp : t ≤ 19/50
    · refine Or.inl ⟨.iota_45, rfl, hc, ?_⟩
      simpa [fiberAnalyticWeight,fiberWeightById,fiberProfileTimeCap] using hp
    · by_cases hw : t ≤ 2/5
      · refine Or.inr (Or.inr ⟨.iota45, .window3, rfl, ?_, rfl, ?_, ?_⟩)
        · simp [fiberWindowInputWindows,fiberWindowWeightById]
        · norm_num [fiberWindowById,fiberWindowWeightById,lowMeanFractionReal] at * <;> linarith
        · norm_num [fiberWindowById,fiberWindowWeightById,lowMeanFractionReal] at * <;> linarith
      · refine Or.inr (Or.inr ⟨.iota45, .window4, rfl, ?_, rfl, ?_, ?_⟩)
        · simp [fiberWindowInputWindows,fiberWindowWeightById]
        · norm_num [fiberWindowById,fiberWindowWeightById,lowMeanFractionReal] at * <;> linarith
        · norm_num [fiberWindowById,fiberWindowWeightById,lowMeanFractionReal] at * <;> linarith
  | iota_46 =>
    norm_num [fiberInputRouteById,lowMeanFractionReal] at hc hts
    by_cases hp : t ≤ 19/50
    · refine Or.inl ⟨.iota_46, rfl, hc, ?_⟩
      simpa [fiberAnalyticWeight,fiberWeightById,fiberProfileTimeCap] using hp
    · by_cases hw : t ≤ 2/5
      · refine Or.inr (Or.inr ⟨.iota46, .window3, rfl, ?_, rfl, ?_, ?_⟩)
        · simp [fiberWindowInputWindows,fiberWindowWeightById]
        · norm_num [fiberWindowById,fiberWindowWeightById,lowMeanFractionReal] at * <;> linarith
        · norm_num [fiberWindowById,fiberWindowWeightById,lowMeanFractionReal] at * <;> linarith
      · refine Or.inr (Or.inr ⟨.iota46, .window4, rfl, ?_, rfl, ?_, ?_⟩)
        · simp [fiberWindowInputWindows,fiberWindowWeightById]
        · norm_num [fiberWindowById,fiberWindowWeightById,lowMeanFractionReal] at * <;> linarith
        · norm_num [fiberWindowById,fiberWindowWeightById,lowMeanFractionReal] at * <;> linarith
  | iota_47 =>
    norm_num [fiberInputRouteById,lowMeanFractionReal] at hc hts
    refine Or.inr (Or.inr ⟨.iota47, .window5, rfl, ?_, rfl, ?_, ?_⟩)
    · simp [fiberWindowInputWindows,fiberWindowWeightById]
    · norm_num [fiberWindowById,fiberWindowWeightById,lowMeanFractionReal] at * <;> linarith
    · norm_num [fiberWindowById,fiberWindowWeightById,lowMeanFractionReal] at * <;> linarith
  | iota_48 =>
    norm_num [fiberInputRouteById,lowMeanFractionReal] at hc hts
    refine Or.inr (Or.inr ⟨.iota48, .window5, rfl, ?_, rfl, ?_, ?_⟩)
    · simp [fiberWindowInputWindows,fiberWindowWeightById]
    · norm_num [fiberWindowById,fiberWindowWeightById,lowMeanFractionReal] at * <;> linarith
    · norm_num [fiberWindowById,fiberWindowWeightById,lowMeanFractionReal] at * <;> linarith
  | iota_49 =>
    norm_num [fiberInputRouteById,lowMeanFractionReal] at hc hts
    refine Or.inr (Or.inr ⟨.iota49, .window5, rfl, ?_, rfl, ?_, ?_⟩)
    · simp [fiberWindowInputWindows,fiberWindowWeightById]
    · norm_num [fiberWindowById,fiberWindowWeightById,lowMeanFractionReal] at * <;> linarith
    · norm_num [fiberWindowById,fiberWindowWeightById,lowMeanFractionReal] at * <;> linarith
  | iota_50 =>
    norm_num [fiberInputRouteById,lowMeanFractionReal] at hc hts
    by_cases hw : t ≤ 33/100
    · refine Or.inr (Or.inr ⟨.iota50, .window6, rfl, ?_, rfl, ?_, ?_⟩)
      · simp [fiberWindowInputWindows,fiberWindowWeightById]
      · norm_num [fiberWindowById,fiberWindowWeightById,lowMeanFractionReal] at * <;> linarith
      · norm_num [fiberWindowById,fiberWindowWeightById,lowMeanFractionReal] at * <;> linarith
    · refine Or.inr (Or.inr ⟨.iota50, .window7, rfl, ?_, rfl, ?_, ?_⟩)
      · simp [fiberWindowInputWindows,fiberWindowWeightById]
      · norm_num [fiberWindowById,fiberWindowWeightById,lowMeanFractionReal] at * <;> linarith
      · norm_num [fiberWindowById,fiberWindowWeightById,lowMeanFractionReal] at * <;> linarith
  | iota_51 =>
    norm_num [fiberInputRouteById,lowMeanFractionReal] at hc hts
    by_cases hw : t ≤ 33/100
    · refine Or.inr (Or.inr ⟨.iota51, .window6, rfl, ?_, rfl, ?_, ?_⟩)
      · simp [fiberWindowInputWindows,fiberWindowWeightById]
      · norm_num [fiberWindowById,fiberWindowWeightById,lowMeanFractionReal] at * <;> linarith
      · norm_num [fiberWindowById,fiberWindowWeightById,lowMeanFractionReal] at * <;> linarith
    · refine Or.inr (Or.inr ⟨.iota51, .window7, rfl, ?_, rfl, ?_, ?_⟩)
      · simp [fiberWindowInputWindows,fiberWindowWeightById]
      · norm_num [fiberWindowById,fiberWindowWeightById,lowMeanFractionReal] at * <;> linarith
      · norm_num [fiberWindowById,fiberWindowWeightById,lowMeanFractionReal] at * <;> linarith
  | iota_52 =>
    norm_num [fiberInputRouteById,lowMeanFractionReal] at hc hts
    by_cases hw : t ≤ 33/100
    · refine Or.inr (Or.inr ⟨.iota52, .window6, rfl, ?_, rfl, ?_, ?_⟩)
      · simp [fiberWindowInputWindows,fiberWindowWeightById]
      · norm_num [fiberWindowById,fiberWindowWeightById,lowMeanFractionReal] at * <;> linarith
      · norm_num [fiberWindowById,fiberWindowWeightById,lowMeanFractionReal] at * <;> linarith
    · refine Or.inr (Or.inr ⟨.iota52, .window7, rfl, ?_, rfl, ?_, ?_⟩)
      · simp [fiberWindowInputWindows,fiberWindowWeightById]
      · norm_num [fiberWindowById,fiberWindowWeightById,lowMeanFractionReal] at * <;> linarith
      · norm_num [fiberWindowById,fiberWindowWeightById,lowMeanFractionReal] at * <;> linarith
  | iota_53 =>
    norm_num [fiberInputRouteById,lowMeanFractionReal] at hc hts
    by_cases hw : t ≤ 3/10
    · refine Or.inr (Or.inr ⟨.iota53, .window8, rfl, ?_, rfl, ?_, ?_⟩)
      · simp [fiberWindowInputWindows,fiberWindowWeightById]
      · norm_num [fiberWindowById,fiberWindowWeightById,lowMeanFractionReal] at * <;> linarith
      · norm_num [fiberWindowById,fiberWindowWeightById,lowMeanFractionReal] at * <;> linarith
    · refine Or.inr (Or.inr ⟨.iota53, .window9, rfl, ?_, rfl, ?_, ?_⟩)
      · simp [fiberWindowInputWindows,fiberWindowWeightById]
      · norm_num [fiberWindowById,fiberWindowWeightById,lowMeanFractionReal] at * <;> linarith
      · norm_num [fiberWindowById,fiberWindowWeightById,lowMeanFractionReal] at * <;> linarith
  | iota_54 =>
    norm_num [fiberInputRouteById,lowMeanFractionReal] at hc hts
    refine Or.inr (Or.inr ⟨.iota54, .window10, rfl, ?_, rfl, ?_, ?_⟩)
    · simp [fiberWindowInputWindows,fiberWindowWeightById]
    · norm_num [fiberWindowById,fiberWindowWeightById,lowMeanFractionReal] at * <;> linarith
    · norm_num [fiberWindowById,fiberWindowWeightById,lowMeanFractionReal] at * <;> linarith

end Erdos993Lean.Analytic.V213
