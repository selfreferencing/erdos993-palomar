module

public import F4Heavy.Analysis.HLowerWPiece0_1
public import F4Heavy.Analysis.HUpperPrimaryCore

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

def batchAlpha : PolynomialExpr :=
  (.mul (.add (.mul (.const ⟨(51799), 1⟩) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity))) (.mul (.const ⟨(8158), 1⟩) (.add (.mul (.const ⟨(7), 4⟩) (.add (.const ⟨(1), 1⟩) .activity)) (.mul (.const ⟨(-1), 1⟩) (.mul (.const ⟨(523), 256⟩) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity))))))) (.const ⟨(1), 65536⟩))

def batchGamma : PolynomialExpr :=
  (.mul (.add (.mul (.const ⟨(29750), 1⟩) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity))) (.mul (.const ⟨(4333), 1⟩) (.add (.mul (.const ⟨(7), 4⟩) (.add (.const ⟨(1), 1⟩) .activity)) (.mul (.const ⟨(-1), 1⟩) (.mul (.const ⟨(523), 256⟩) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity))))))) (.const ⟨(1), 65536⟩))

def batchVacancy : PolynomialExpr :=
  (.add (.pow (.add (.const ⟨(11), 1⟩) (.mul (.const ⟨(3), 1⟩) .activity)) 2) (.mul (.mul (.const ⟨(28), 1⟩) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) (.pow .activity 2)))) .parent))

def batchLogDen : PolynomialExpr :=
  (.add (.add (.mul (.const ⟨(9), 1⟩) (.pow .parent 2)) (.mul (.const ⟨(12), 1⟩) .parent)) (.const ⟨(1), 1⟩))

def batchUpper : PolynomialExpr :=
  (.add (.mul batchLogDen (.add (.mul (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity)) (.add (.add (.const ⟨(1112405610801), 1000000000000⟩) (.const ⟨(1386294361120), 1000000000000⟩)) (.mul (.const ⟨(-1), 1⟩) (.const ⟨(21), 73⟩)))) (.mul (.add (.mul (.const ⟨(42), 1⟩) (.add (.const ⟨(1), 1⟩) .activity)) (.mul (.const ⟨(-1), 1⟩) (.mul (.const ⟨(49), 1⟩) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity))))) (.const ⟨(1), 73⟩)))) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.const ⟨(3), 1⟩) (.add (.mul (.const ⟨(9), 1⟩) (.pow .parent 2)) (.mul (.const ⟨(-1), 1⟩) (.const ⟨(1), 1⟩)))) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity)))))

def batchParentLower : PolynomialExpr :=
  (.add (.mul (.mul batchGamma batchVacancy) (.add (.add (.mul (.const ⟨(12), 1⟩) (.pow sampleBase 2)) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.const ⟨(6), 1⟩) sampleProb) sampleBase))) (.mul (.const ⟨(-1), 1⟩) (.pow sampleProb 2)))) (.mul (.mul (.mul (.const ⟨(48), 1⟩) (.pow (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity)) 2)) (.pow sampleBase 2)) (.add sampleBase (.mul (.const ⟨(-1), 1⟩) sampleProb))))

def batchNLower : PolynomialExpr :=
  (.add (.add (.mul (.mul (.mul (.mul (.mul (.mul (.const ⟨(3), 1⟩) (.pow (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity)) 2)) (.add (.const ⟨(9), 1⟩) (.mul (.const ⟨(5), 1⟩) .activity))) .parent) sampleBase) (.add (.const ⟨(8), 1⟩) (.mul (.const ⟨(-1), 1⟩) .parent))) (.add (.mul (.mul (.const ⟨(64), 1⟩) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity))) sampleBase) (.mul (.const ⟨(-1), 1⟩) (.mul (.add (.const ⟨(8), 1⟩) (.mul (.const ⟨(-1), 1⟩) .parent)) batchVacancy)))) (.mul (.mul (.mul (.mul (.const ⟨(24), 1⟩) batchAlpha) (.add (.const ⟨(11), 1⟩) (.mul (.const ⟨(3), 1⟩) .activity))) (.pow sampleBase 2)) (.add batchVacancy (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.const ⟨(4), 1⟩) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity))) sampleBase))))) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.const ⟨(2), 1⟩) (.add (.const ⟨(11), 1⟩) (.mul (.const ⟨(3), 1⟩) .activity))) batchParentLower)))

def batchParentUpper : PolynomialExpr :=
  (.add (.mul batchGamma (.add (.add (.mul (.const ⟨(12), 1⟩) (.pow sampleBase 2)) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.const ⟨(6), 1⟩) sampleProb) sampleBase))) (.mul (.const ⟨(-1), 1⟩) (.pow sampleProb 2)))) (.mul (.mul (.mul (.const ⟨(12), 1⟩) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity))) sampleBase) (.add sampleBase (.mul (.const ⟨(-1), 1⟩) sampleProb))))

def batchNUpper : PolynomialExpr :=
  (.add (.mul (.mul (.mul (.mul (.mul (.const ⟨(3), 1⟩) (.pow (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity)) 2)) (.add (.const ⟨(9), 1⟩) (.mul (.const ⟨(5), 1⟩) .activity))) .parent) sampleBase) (.add (.const ⟨(64), 1⟩) (.mul (.const ⟨(-1), 1⟩) (.pow .parent 2)))) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.const ⟨(2), 1⟩) (.add (.const ⟨(11), 1⟩) (.mul (.const ⟨(3), 1⟩) .activity))) batchParentUpper)))

theorem batchAlpha_value (v x : ℝ) :
    batchAlpha.value v x = hAlphaNum v := by
  simp only [batchAlpha, PolynomialExpr.value, hAlphaNum, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  ring

theorem batchGamma_value (v x : ℝ) :
    batchGamma.value v x = hGammaNum v := by
  simp only [batchGamma, PolynomialExpr.value, hGammaNum, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  ring

theorem batchVacancy_value (v x : ℝ) :
    batchVacancy.value v x = hVacancyDen v x := by
  simp only [batchVacancy, PolynomialExpr.value, hVacancyDen, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  ring

theorem batchLogDen_value (v x : ℝ) :
    batchLogDen.value v x = eLogDen x := by
  simp only [batchLogDen, PolynomialExpr.value, eLogDen, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]

theorem batchUpper_value (v x : ℝ) :
    batchUpper.value v x = hUpperNum v x := by
  simp only [batchUpper, PolynomialExpr.value, batchLogDen_value, hUpperNum, activityLogMidpointUpper, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  ring

theorem batchParentLower_value (v x : ℝ) :
    batchParentLower.value v x = hParentLowerNum v x := by
  simp only [batchParentLower, PolynomialExpr.value, sampleBase_value, sampleProb_value, batchGamma_value, batchVacancy_value, hParentLowerNum, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  ring

theorem batchNLower_value (v x : ℝ) :
    batchNLower.value v x = hNLowerNum v x := by
  simp only [batchNLower, PolynomialExpr.value, sampleBase_value, batchAlpha_value, batchVacancy_value, batchParentLower_value, hNLowerNum, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  ring

theorem batchParentUpper_value (v x : ℝ) :
    batchParentUpper.value v x = hParentUpperNum v x := by
  simp only [batchParentUpper, PolynomialExpr.value, sampleBase_value, sampleProb_value, batchGamma_value, hParentUpperNum, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  ring

theorem batchNUpper_value (v x : ℝ) :
    batchNUpper.value v x = hNUpperNum v x := by
  simp only [batchNUpper, PolynomialExpr.value, sampleBase_value, batchParentUpper_value, hNUpperNum, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  ring

end F4Heavy.Analysis
