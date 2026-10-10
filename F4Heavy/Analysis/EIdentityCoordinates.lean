module

public import F4Heavy.Analysis.PolynomialIdentity
public import F4Heavy.Analysis.EFormulaUPieces
public import F4Heavy.Analysis.ESupportData

@[expose] public section
set_option autoImplicit false
namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

def reflectEBase : PolynomialExpr :=
  (.add (.add (.const ⟨(1), 1⟩) .activity) (.mul .activity .parent))

def reflectELogDen : PolynomialExpr :=
  (.add (.add (.mul (.const ⟨(9), 1⟩) (.pow .parent 2)) (.mul (.const ⟨(12), 1⟩) .parent)) (.const ⟨(1), 1⟩))

def reflectE1Alpha : PolynomialExpr :=
  (.mul (.add (.const ⟨(44917), 1⟩) (.mul (.const ⟨(29958), 1⟩) (.add .activity (.mul (.const ⟨(-1), 1⟩) (.const ⟨(11), 8⟩))))) (.const ⟨(1), 65536⟩))

def reflectE1Beta : PolynomialExpr :=
  (.mul (.add (.const ⟨(28533), 1⟩) (.mul (.const ⟨(57271), 1⟩) (.add .activity (.mul (.const ⟨(-1), 1⟩) (.const ⟨(11), 8⟩))))) (.const ⟨(1), 65536⟩))

def reflectE1Gamma : PolynomialExpr :=
  (.mul (.add (.const ⟨(17821), 1⟩) (.mul (.const ⟨(20483), 1⟩) (.add .activity (.mul (.const ⟨(-1), 1⟩) (.const ⟨(11), 8⟩))))) (.const ⟨(1), 65536⟩))

def reflectE1Delta : PolynomialExpr :=
  (.mul (.add (.const ⟨(3064), 1⟩) (.mul (.const ⟨(-4423), 1⟩) (.add .activity (.mul (.const ⟨(-1), 1⟩) (.const ⟨(11), 8⟩))))) (.const ⟨(1), 65536⟩))

def reflectE1K : PolynomialExpr :=
  (.mul (.mul (.const ⟨(17), 20⟩) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(2), 1⟩) .activity))) .parent)

def reflectE1Parent : PolynomialExpr :=
  (.mul (.mul reflectE1Gamma (.add (.mul (.const ⟨(2), 1⟩) reflectEBase) (.mul (.const ⟨(-1), 1⟩) (.mul .activity .parent)))) (.const ⟨(1), 2⟩))

def reflectE1Lower : PolynomialExpr :=
  (.add (.mul (.add (.const ⟨(1), 1⟩) .parent) (.add (.const ⟨(8329091229), 10000000000⟩) (.mul (.const ⟨(78973627), 187500000⟩) (.add .activity (.mul (.const ⟨(-1), 1⟩) (.const ⟨(13), 10⟩)))))) (.mul (.const ⟨(2), 1⟩) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .parent))))

def reflectE1Upper : PolynomialExpr :=
  (.add (.mul reflectELogDen (.add (.add (.add (.const ⟨(13839959), 16000000⟩) (.mul (.add .activity (.mul (.const ⟨(-1), 1⟩) (.const ⟨(11), 8⟩))) (.const ⟨(8), 19⟩))) (.const ⟨(8664339757), 6250000000⟩)) (.mul (.const ⟨(-1), 1⟩) (.const ⟨(21), 73⟩)))) (.mul (.const ⟨(-1), 1⟩) (.mul (.const ⟨(3), 1⟩) (.add (.mul (.const ⟨(9), 1⟩) (.pow .parent 2)) (.mul (.const ⟨(-1), 1⟩) (.const ⟨(1), 1⟩))))))

def reflectE1Intercept0 : PolynomialExpr :=
  (.add (.add (.const ⟨(-79166889), 50000000⟩) (.mul (.const ⟨(4229891), 15000000⟩) (.add .activity (.mul (.const ⟨(-1), 1⟩) (.const ⟨(13), 10⟩))))) (.const ⟨(18009), 25969216⟩))

def reflectE1Intercept1 : PolynomialExpr :=
  (.add (.add (.const ⟨(3500567), 100000000⟩) (.mul (.const ⟨(1211183), 7500000⟩) (.add .activity (.mul (.const ⟨(-1), 1⟩) (.const ⟨(13), 10⟩))))) (.const ⟨(18009), 25969216⟩))

def reflectE1Intercept2 : PolynomialExpr :=
  (.add (.add (.const ⟨(38732233), 50000000⟩) (.mul (.const ⟨(185137), 1500000⟩) (.add .activity (.mul (.const ⟨(-1), 1⟩) (.const ⟨(13), 10⟩))))) (.const ⟨(18009), 25969216⟩))

def reflectE1Vertex0 : PolynomialExpr :=
  (.mul (.mul (.const ⟨(-1), 1⟩) reflectE1Intercept0) (.const ⟨(3), 7⟩))

def reflectE1Vertex1 : PolynomialExpr :=
  (.mul (.add reflectE1Intercept1 (.mul (.const ⟨(-1), 1⟩) reflectE1Intercept0)) (.const ⟨(30), 61⟩))

def reflectE1Vertex2 : PolynomialExpr :=
  (.mul (.add reflectE1Intercept2 (.mul (.const ⟨(-1), 1⟩) reflectE1Intercept1)) (.const ⟨(6), 5⟩))

def reflectE1Vertex3 : PolynomialExpr :=
  (.const ⟨(1), 1⟩)

def reflectE1Height0 : PolynomialExpr :=
  (.const ⟨(0), 1⟩)

def reflectE1Height1 : PolynomialExpr :=
  (.add (.mul (.const ⟨(7), 3⟩) reflectE1Vertex1) reflectE1Intercept0)

def reflectE1Height2 : PolynomialExpr :=
  (.add (.mul (.const ⟨(3), 10⟩) reflectE1Vertex2) reflectE1Intercept1)

def reflectE1Height3 : PolynomialExpr :=
  (.add (.const ⟨(-8), 15⟩) reflectE1Intercept2)

def reflectE2Alpha : PolynomialExpr :=
  (.mul (.add (.const ⟨(45775), 1⟩) (.mul (.const ⟨(22238), 1⟩) (.add .activity (.mul (.const ⟨(-1), 1⟩) (.const ⟨(195), 128⟩))))) (.const ⟨(1), 65536⟩))

def reflectE2Beta : PolynomialExpr :=
  (.mul (.add (.const ⟨(30825), 1⟩) (.mul (.const ⟨(10297), 1⟩) (.add .activity (.mul (.const ⟨(-1), 1⟩) (.const ⟨(195), 128⟩))))) (.const ⟨(1), 65536⟩))

def reflectE2Gamma : PolynomialExpr :=
  (.mul (.add (.const ⟨(19913), 1⟩) (.mul (.const ⟨(13978), 1⟩) (.add .activity (.mul (.const ⟨(-1), 1⟩) (.const ⟨(195), 128⟩))))) (.const ⟨(1), 65536⟩))

def reflectE2Delta : PolynomialExpr :=
  (.mul (.add (.const ⟨(3161), 1⟩) (.mul (.const ⟨(4340), 1⟩) (.add .activity (.mul (.const ⟨(-1), 1⟩) (.const ⟨(195), 128⟩))))) (.const ⟨(1), 65536⟩))

def reflectE2K : PolynomialExpr :=
  (.mul (.mul (.const ⟨(17), 20⟩) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(2), 1⟩) .activity))) .parent)

def reflectE2Parent : PolynomialExpr :=
  (.mul (.mul reflectE2Gamma (.add (.mul (.const ⟨(2), 1⟩) reflectEBase) (.mul (.const ⟨(-1), 1⟩) (.mul .activity .parent)))) (.const ⟨(1), 2⟩))

def reflectE2Lower : PolynomialExpr :=
  (.add (.mul (.add (.const ⟨(1), 1⟩) .parent) (.add (.const ⟨(1792176049), 2000000000⟩) (.mul (.const ⟨(118846841), 300000000⟩) (.add .activity (.mul (.const ⟨(-1), 1⟩) (.const ⟨(29), 20⟩)))))) (.mul (.const ⟨(2), 1⟩) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .parent))))

def reflectE2Upper : PolynomialExpr :=
  (.add (.mul reflectELogDen (.add (.add (.add (.const ⟨(2315602657), 2500000000⟩) (.mul (.add .activity (.mul (.const ⟨(-1), 1⟩) (.const ⟨(61), 40⟩))) (.const ⟨(40), 101⟩))) (.const ⟨(8664339757), 6250000000⟩)) (.mul (.const ⟨(-1), 1⟩) (.const ⟨(21), 73⟩)))) (.mul (.const ⟨(-1), 1⟩) (.mul (.const ⟨(3), 1⟩) (.add (.mul (.const ⟨(9), 1⟩) (.pow .parent 2)) (.mul (.const ⟨(-1), 1⟩) (.const ⟨(1), 1⟩))))))

def reflectE2Intercept0 : PolynomialExpr :=
  (.add (.add (.const ⟨(-154103887), 100000000⟩) (.mul (.const ⟨(1939409), 7500000⟩) (.add .activity (.mul (.const ⟨(-1), 1⟩) (.const ⟨(29), 20⟩))))) (.const ⟨(81), 142129⟩))

def reflectE2Intercept1 : PolynomialExpr :=
  (.add (.add (.const ⟨(5922933), 100000000⟩) (.mul (.const ⟨(569293), 3750000⟩) (.add .activity (.mul (.const ⟨(-1), 1⟩) (.const ⟨(29), 20⟩))))) (.const ⟨(81), 142129⟩))

def reflectE2Intercept2 : PolynomialExpr :=
  (.add (.add (.const ⟨(19828959), 25000000⟩) (.mul (.const ⟨(1807147), 15000000⟩) (.add .activity (.mul (.const ⟨(-1), 1⟩) (.const ⟨(29), 20⟩))))) (.const ⟨(81), 142129⟩))

def reflectE2Vertex0 : PolynomialExpr :=
  (.mul (.mul (.const ⟨(-1), 1⟩) reflectE2Intercept0) (.const ⟨(3), 7⟩))

def reflectE2Vertex1 : PolynomialExpr :=
  (.mul (.add reflectE2Intercept1 (.mul (.const ⟨(-1), 1⟩) reflectE2Intercept0)) (.const ⟨(30), 61⟩))

def reflectE2Vertex2 : PolynomialExpr :=
  (.mul (.add reflectE2Intercept2 (.mul (.const ⟨(-1), 1⟩) reflectE2Intercept1)) (.const ⟨(6), 5⟩))

def reflectE2Vertex3 : PolynomialExpr :=
  (.const ⟨(1), 1⟩)

def reflectE2Height0 : PolynomialExpr :=
  (.const ⟨(0), 1⟩)

def reflectE2Height1 : PolynomialExpr :=
  (.add (.mul (.const ⟨(7), 3⟩) reflectE2Vertex1) reflectE2Intercept0)

def reflectE2Height2 : PolynomialExpr :=
  (.add (.mul (.const ⟨(3), 10⟩) reflectE2Vertex2) reflectE2Intercept1)

def reflectE2Height3 : PolynomialExpr :=
  (.add (.const ⟨(-8), 15⟩) reflectE2Intercept2)

theorem reflectEBase_value (v x : ℝ) :
    reflectEBase.value v x = eBaseDen v x := by
  simp only [reflectEBase, PolynomialExpr.value, eBaseDen, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectELogDen_value (v x : ℝ) :
    reflectELogDen.value v x = eLogDen x := by
  simp only [reflectELogDen, PolynomialExpr.value, eLogDen, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectE1Alpha_value (v x : ℝ) :
    reflectE1Alpha.value v x = alpha .E1 v := by
  simp only [reflectE1Alpha, PolynomialExpr.value, alpha, field, rowData, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectE1Beta_value (v x : ℝ) :
    reflectE1Beta.value v x = beta .E1 v := by
  simp only [reflectE1Beta, PolynomialExpr.value, beta, field, rowData, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectE1Gamma_value (v x : ℝ) :
    reflectE1Gamma.value v x = gamma .E1 v := by
  simp only [reflectE1Gamma, PolynomialExpr.value, gamma, field, rowData, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectE1Delta_value (v x : ℝ) :
    reflectE1Delta.value v x = delta .E1 v := by
  simp only [reflectE1Delta, PolynomialExpr.value, delta, field, rowData, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectE1K_value (v x : ℝ) :
    reflectE1K.value v x = eKNumerator .E1 v x := by
  simp only [reflectE1K, PolynomialExpr.value, eKNumerator, field, rowData, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectE1Parent_value (v x : ℝ) :
    reflectE1Parent.value v x = eParentNumerator .E1 v x := by
  simp only [reflectE1Parent, PolynomialExpr.value, reflectEBase_value, reflectE1Gamma_value, eParentNumerator, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectE1Lower_value (v x : ℝ) :
    reflectE1Lower.value v x = eLowerNumerator .E1 v x := by
  simp only [reflectE1Lower, PolynomialExpr.value, eLowerNumerator, activityLogLower, activityLogLeft, activityLogRight, rowData, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectE1Upper_value (v x : ℝ) :
    reflectE1Upper.value v x = eUpperNumerator .E1 v x := by
  simp only [reflectE1Upper, PolynomialExpr.value, reflectELogDen_value, eUpperNumerator, activityLogUpper, activityLogMidpointUpper, rowData, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectE1Intercept0_value (v x : ℝ) :
    reflectE1Intercept0.value v x = eSupportIntercept0 .E1 v := by
  simp only [reflectE1Intercept0, PolynomialExpr.value, eSupportIntercept0, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectE1Intercept1_value (v x : ℝ) :
    reflectE1Intercept1.value v x = eSupportIntercept1 .E1 v := by
  simp only [reflectE1Intercept1, PolynomialExpr.value, eSupportIntercept1, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectE1Intercept2_value (v x : ℝ) :
    reflectE1Intercept2.value v x = eSupportIntercept2 .E1 v := by
  simp only [reflectE1Intercept2, PolynomialExpr.value, eSupportIntercept2, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectE1Vertex0_value (v x : ℝ) :
    reflectE1Vertex0.value v x = eSupportVertex .E1 v 0 := by
  simp only [reflectE1Vertex0, PolynomialExpr.value, reflectE1Intercept0_value, eSupportVertex, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectE1Vertex1_value (v x : ℝ) :
    reflectE1Vertex1.value v x = eSupportVertex .E1 v 1 := by
  simp only [reflectE1Vertex1, PolynomialExpr.value, reflectE1Intercept0_value, reflectE1Intercept1_value, eSupportVertex, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectE1Vertex2_value (v x : ℝ) :
    reflectE1Vertex2.value v x = eSupportVertex .E1 v 2 := by
  simp only [reflectE1Vertex2, PolynomialExpr.value, reflectE1Intercept1_value, reflectE1Intercept2_value, eSupportVertex, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectE1Vertex3_value (v x : ℝ) :
    reflectE1Vertex3.value v x = eSupportVertex .E1 v 3 := by
  simp only [reflectE1Vertex3, PolynomialExpr.value, eSupportVertex, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectE1Height0_value (v x : ℝ) :
    reflectE1Height0.value v x = eSupportHeight .E1 v 0 := by
  simp only [reflectE1Height0, PolynomialExpr.value, eSupportHeight, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectE1Height1_value (v x : ℝ) :
    reflectE1Height1.value v x = eSupportHeight .E1 v 1 := by
  simp only [reflectE1Height1, PolynomialExpr.value, reflectE1Intercept0_value, reflectE1Vertex1_value, eSupportHeight, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectE1Height2_value (v x : ℝ) :
    reflectE1Height2.value v x = eSupportHeight .E1 v 2 := by
  simp only [reflectE1Height2, PolynomialExpr.value, reflectE1Intercept1_value, reflectE1Vertex2_value, eSupportHeight, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectE1Height3_value (v x : ℝ) :
    reflectE1Height3.value v x = eSupportHeight .E1 v 3 := by
  simp only [reflectE1Height3, PolynomialExpr.value, reflectE1Intercept2_value, eSupportHeight, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectE2Alpha_value (v x : ℝ) :
    reflectE2Alpha.value v x = alpha .E2 v := by
  simp only [reflectE2Alpha, PolynomialExpr.value, alpha, field, rowData, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectE2Beta_value (v x : ℝ) :
    reflectE2Beta.value v x = beta .E2 v := by
  simp only [reflectE2Beta, PolynomialExpr.value, beta, field, rowData, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectE2Gamma_value (v x : ℝ) :
    reflectE2Gamma.value v x = gamma .E2 v := by
  simp only [reflectE2Gamma, PolynomialExpr.value, gamma, field, rowData, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectE2Delta_value (v x : ℝ) :
    reflectE2Delta.value v x = delta .E2 v := by
  simp only [reflectE2Delta, PolynomialExpr.value, delta, field, rowData, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectE2K_value (v x : ℝ) :
    reflectE2K.value v x = eKNumerator .E2 v x := by
  simp only [reflectE2K, PolynomialExpr.value, eKNumerator, field, rowData, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectE2Parent_value (v x : ℝ) :
    reflectE2Parent.value v x = eParentNumerator .E2 v x := by
  simp only [reflectE2Parent, PolynomialExpr.value, reflectEBase_value, reflectE2Gamma_value, eParentNumerator, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectE2Lower_value (v x : ℝ) :
    reflectE2Lower.value v x = eLowerNumerator .E2 v x := by
  simp only [reflectE2Lower, PolynomialExpr.value, eLowerNumerator, activityLogLower, activityLogLeft, activityLogRight, rowData, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectE2Upper_value (v x : ℝ) :
    reflectE2Upper.value v x = eUpperNumerator .E2 v x := by
  simp only [reflectE2Upper, PolynomialExpr.value, reflectELogDen_value, eUpperNumerator, activityLogUpper, activityLogMidpointUpper, rowData, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectE2Intercept0_value (v x : ℝ) :
    reflectE2Intercept0.value v x = eSupportIntercept0 .E2 v := by
  simp only [reflectE2Intercept0, PolynomialExpr.value, eSupportIntercept0, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectE2Intercept1_value (v x : ℝ) :
    reflectE2Intercept1.value v x = eSupportIntercept1 .E2 v := by
  simp only [reflectE2Intercept1, PolynomialExpr.value, eSupportIntercept1, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectE2Intercept2_value (v x : ℝ) :
    reflectE2Intercept2.value v x = eSupportIntercept2 .E2 v := by
  simp only [reflectE2Intercept2, PolynomialExpr.value, eSupportIntercept2, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectE2Vertex0_value (v x : ℝ) :
    reflectE2Vertex0.value v x = eSupportVertex .E2 v 0 := by
  simp only [reflectE2Vertex0, PolynomialExpr.value, reflectE2Intercept0_value, eSupportVertex, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectE2Vertex1_value (v x : ℝ) :
    reflectE2Vertex1.value v x = eSupportVertex .E2 v 1 := by
  simp only [reflectE2Vertex1, PolynomialExpr.value, reflectE2Intercept0_value, reflectE2Intercept1_value, eSupportVertex, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectE2Vertex2_value (v x : ℝ) :
    reflectE2Vertex2.value v x = eSupportVertex .E2 v 2 := by
  simp only [reflectE2Vertex2, PolynomialExpr.value, reflectE2Intercept1_value, reflectE2Intercept2_value, eSupportVertex, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectE2Vertex3_value (v x : ℝ) :
    reflectE2Vertex3.value v x = eSupportVertex .E2 v 3 := by
  simp only [reflectE2Vertex3, PolynomialExpr.value, eSupportVertex, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectE2Height0_value (v x : ℝ) :
    reflectE2Height0.value v x = eSupportHeight .E2 v 0 := by
  simp only [reflectE2Height0, PolynomialExpr.value, eSupportHeight, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectE2Height1_value (v x : ℝ) :
    reflectE2Height1.value v x = eSupportHeight .E2 v 1 := by
  simp only [reflectE2Height1, PolynomialExpr.value, reflectE2Intercept0_value, reflectE2Vertex1_value, eSupportHeight, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectE2Height2_value (v x : ℝ) :
    reflectE2Height2.value v x = eSupportHeight .E2 v 2 := by
  simp only [reflectE2Height2, PolynomialExpr.value, reflectE2Intercept1_value, reflectE2Vertex2_value, eSupportHeight, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectE2Height3_value (v x : ℝ) :
    reflectE2Height3.value v x = eSupportHeight .E2 v 3 := by
  simp only [reflectE2Height3, PolynomialExpr.value, reflectE2Intercept2_value, eSupportHeight, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

end F4Heavy.Analysis
