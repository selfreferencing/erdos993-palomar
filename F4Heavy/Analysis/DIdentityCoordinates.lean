module

public import F4Heavy.Analysis.PolynomialIdentity
public import F4Heavy.Analysis.DLowerPrimaryCore
public import F4Heavy.Analysis.DUpperPrimaryCore

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

def reflectDBase : PolynomialExpr :=
  (.add (.add (.const ⟨(9), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity)) (.mul (.mul (.const ⟨(4), 1⟩) (.add (.const ⟨(1), 1⟩) .activity)) .parent))

def reflectDProb : PolynomialExpr :=
  (.mul (.mul (.const ⟨(4), 1⟩) (.add (.const ⟨(1), 1⟩) .activity)) .parent)

def reflectDAlpha : PolynomialExpr :=
  (.mul (.add (.mul (.const ⟨(46809), 1⟩) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity))) (.mul (.const ⟨(3327), 1⟩) (.add (.mul (.const ⟨(4), 5⟩) (.add (.const ⟨(1), 1⟩) .activity)) (.mul (.const ⟨(-1), 1⟩) (.mul (.const ⟨(269), 256⟩) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity))))))) (.const ⟨(1), 65536⟩))

def reflectDBeta : PolynomialExpr :=
  (.mul (.add (.mul (.const ⟨(35136), 1⟩) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity))) (.mul (.const ⟨(3086), 1⟩) (.add (.mul (.const ⟨(4), 5⟩) (.add (.const ⟨(1), 1⟩) .activity)) (.mul (.const ⟨(-1), 1⟩) (.mul (.const ⟨(269), 256⟩) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity))))))) (.const ⟨(1), 65536⟩))

def reflectDGamma : PolynomialExpr :=
  (.mul (.add (.mul (.const ⟨(14520), 1⟩) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity))) (.mul (.const ⟨(13694), 1⟩) (.add (.mul (.const ⟨(4), 5⟩) (.add (.const ⟨(1), 1⟩) .activity)) (.mul (.const ⟨(-1), 1⟩) (.mul (.const ⟨(269), 256⟩) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity))))))) (.const ⟨(1), 65536⟩))

def reflectDDelta : PolynomialExpr :=
  (.mul (.add (.mul (.const ⟨(1835), 1⟩) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity))) (.mul (.const ⟨(1340), 1⟩) (.add (.mul (.const ⟨(4), 5⟩) (.add (.const ⟨(1), 1⟩) .activity)) (.mul (.const ⟨(-1), 1⟩) (.mul (.const ⟨(269), 256⟩) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity))))))) (.const ⟨(1), 65536⟩))

def reflectDVacancy : PolynomialExpr :=
  (.add (.pow (.add (.const ⟨(9), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity)) 2) (.mul (.mul (.const ⟨(20), 1⟩) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) (.pow .activity 2)))) .parent))

def reflectDLogDen : PolynomialExpr :=
  (.add (.add (.mul (.const ⟨(9), 1⟩) (.pow .parent 2)) (.mul (.const ⟨(12), 1⟩) .parent)) (.const ⟨(1), 1⟩))

def reflectDLower : PolynomialExpr :=
  (.add (.mul (.add (.const ⟨(1), 1⟩) .parent) (.add (.mul (.const ⟨(293893332451), 500000000000⟩) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity))) (.mul (.mul (.add (.const ⟨(166581824587), 200000000000⟩) (.mul (.const ⟨(-1), 1⟩) (.const ⟨(293893332451), 500000000000⟩))) (.const ⟨(16), 5⟩)) .activity))) (.mul (.mul (.const ⟨(2), 1⟩) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .parent))) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity))))

def reflectDUpper : PolynomialExpr :=
  (.add (.mul reflectDLogDen (.add (.mul (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity)) (.add (.add (.const ⟨(717839793151), 1000000000000⟩) (.const ⟨(1386294361120), 1000000000000⟩)) (.mul (.const ⟨(-1), 1⟩) (.const ⟨(21), 73⟩)))) (.mul (.add (.mul (.const ⟨(16), 1⟩) (.add (.const ⟨(1), 1⟩) .activity)) (.mul (.const ⟨(-1), 1⟩) (.mul (.const ⟨(21), 1⟩) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity))))) (.const ⟨(1), 41⟩)))) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.const ⟨(3), 1⟩) (.add (.mul (.const ⟨(9), 1⟩) (.pow .parent 2)) (.mul (.const ⟨(-1), 1⟩) (.const ⟨(1), 1⟩)))) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity)))))

def reflectDSupport : PolynomialExpr :=
  (.mul (.const ⟨(1456523447343), 1⟩) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) (.pow .activity 2))))

def reflectDSupportNum : PolynomialExpr :=
  (.mul (.const ⟨(1000000000000), 1⟩) (.add (.mul (.const ⟨(6), 1⟩) .activity) (.mul (.const ⟨(-1), 1⟩) (.mul (.const ⟨(4), 1⟩) (.pow .activity 3)))))

def reflectDIntercept0 : PolynomialExpr :=
  (.add (.mul (.const ⟨(-3326942783), 2000000000⟩) reflectDSupport) (.mul (.add (.const ⟨(-23862523), 16000000⟩) (.mul (.const ⟨(-1), 1⟩) (.const ⟨(-3326942783), 2000000000⟩))) reflectDSupportNum))

def reflectDIntercept1 : PolynomialExpr :=
  (.add (.mul (.const ⟨(-60258643), 1000000000⟩) reflectDSupport) (.mul (.add (.const ⟨(174865111), 5000000000⟩) (.mul (.const ⟨(-1), 1⟩) (.const ⟨(-60258643), 1000000000⟩))) reflectDSupportNum))

def reflectDIntercept2 : PolynomialExpr :=
  (.add (.mul (.const ⟨(3819556393), 5000000000⟩) reflectDSupport) (.mul (.add (.const ⟨(8346294633), 10000000000⟩) (.mul (.const ⟨(-1), 1⟩) (.const ⟨(3819556393), 5000000000⟩))) reflectDSupportNum))

def reflectDZeroVertex : PolynomialExpr :=
  (.mul (.mul (.const ⟨(-1), 1⟩) reflectDIntercept0) (.const ⟨(5), 11⟩))

def reflectDVertex0 : PolynomialExpr :=
  reflectDZeroVertex

def reflectDVertex1 : PolynomialExpr :=
  (.mul (.add reflectDIntercept1 (.mul (.const ⟨(-1), 1⟩) reflectDIntercept0)) (.const ⟨(10), 19⟩))

def reflectDVertex2 : PolynomialExpr :=
  (.mul (.add reflectDIntercept2 (.mul (.const ⟨(-1), 1⟩) reflectDIntercept1)) (.const ⟨(10), 9⟩))

def reflectDVertex3 : PolynomialExpr :=
  reflectDSupport

def reflectDHeight0 : PolynomialExpr :=
  (.const ⟨(0), 1⟩)

def reflectDHeight1 : PolynomialExpr :=
  (.add (.mul (.const ⟨(11), 5⟩) reflectDVertex1) reflectDIntercept0)

def reflectDHeight2 : PolynomialExpr :=
  (.add (.mul (.const ⟨(3), 10⟩) reflectDVertex2) reflectDIntercept1)

def reflectDHeight3 : PolynomialExpr :=
  (.add (.mul (.const ⟨(-3), 5⟩) reflectDSupport) reflectDIntercept2)

def reflectDParentUpper : PolynomialExpr :=
  (.add (.mul reflectDGamma (.add (.add (.mul (.const ⟨(12), 1⟩) (.pow reflectDBase 2)) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.const ⟨(6), 1⟩) reflectDProb) reflectDBase))) (.mul (.const ⟨(-1), 1⟩) (.pow reflectDProb 2)))) (.mul (.mul (.mul (.const ⟨(12), 1⟩) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity))) reflectDBase) (.add reflectDBase (.mul (.const ⟨(-1), 1⟩) reflectDProb))))

def reflectDParentLower : PolynomialExpr :=
  (.add (.mul (.mul reflectDGamma reflectDVacancy) (.add (.add (.mul (.const ⟨(12), 1⟩) (.pow reflectDBase 2)) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.const ⟨(6), 1⟩) reflectDProb) reflectDBase))) (.mul (.const ⟨(-1), 1⟩) (.pow reflectDProb 2)))) (.mul (.mul (.mul (.const ⟨(60), 1⟩) (.pow (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity)) 2)) (.pow reflectDBase 2)) (.add reflectDBase (.mul (.const ⟨(-1), 1⟩) reflectDProb))))

def reflectDNUpper : PolynomialExpr :=
  (.add (.mul (.mul (.mul (.mul (.const ⟨(4653), 1⟩) (.pow (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity)) 2)) (.add (.const ⟨(13), 1⟩) (.mul (.const ⟨(3), 1⟩) .activity))) .parent) reflectDBase) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.const ⟨(100), 1⟩) (.add (.const ⟨(9), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity))) reflectDParentUpper)))

def reflectDNLower : PolynomialExpr :=
  (.add (.add (.mul (.mul (.mul (.mul (.mul (.const ⟨(3), 1⟩) (.pow (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity)) 2)) reflectDBase) (.add (.const ⟨(13), 1⟩) (.mul (.const ⟨(3), 1⟩) .activity))) .parent) (.add (.mul (.mul (.const ⟨(13200), 1⟩) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity))) reflectDBase) (.mul (.const ⟨(-1), 1⟩) (.mul (.const ⟨(1089), 1⟩) reflectDVacancy)))) (.mul (.mul (.mul (.mul (.const ⟨(1200), 1⟩) reflectDAlpha) (.add (.const ⟨(9), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity))) (.pow reflectDBase 2)) (.add reflectDVacancy (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.const ⟨(5), 1⟩) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity))) reflectDBase))))) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.const ⟨(100), 1⟩) (.add (.const ⟨(9), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity))) reflectDParentLower)))

theorem reflectDBase_value (v x : ℝ) :
    reflectDBase.value v x = dBase v x := by
  simp only [reflectDBase, PolynomialExpr.value, dBase, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectDProb_value (v x : ℝ) :
    reflectDProb.value v x = dProbNum v x := by
  simp only [reflectDProb, PolynomialExpr.value, dProbNum, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectDAlpha_value (v x : ℝ) :
    reflectDAlpha.value v x = dAlphaNum v := by
  simp only [reflectDAlpha, PolynomialExpr.value, dAlphaNum, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectDBeta_value (v x : ℝ) :
    reflectDBeta.value v x = dBetaNum v := by
  simp only [reflectDBeta, PolynomialExpr.value, dBetaNum, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectDGamma_value (v x : ℝ) :
    reflectDGamma.value v x = dGammaNum v := by
  simp only [reflectDGamma, PolynomialExpr.value, dGammaNum, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectDDelta_value (v x : ℝ) :
    reflectDDelta.value v x = dDeltaNum v := by
  simp only [reflectDDelta, PolynomialExpr.value, dDeltaNum, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectDVacancy_value (v x : ℝ) :
    reflectDVacancy.value v x = dVacancyDen v x := by
  simp only [reflectDVacancy, PolynomialExpr.value, dVacancyDen, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectDLogDen_value (v x : ℝ) :
    reflectDLogDen.value v x = eLogDen x := by
  simp only [reflectDLogDen, PolynomialExpr.value, eLogDen, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectDLower_value (v x : ℝ) :
    reflectDLower.value v x = dLowerNum v x := by
  simp only [reflectDLower, PolynomialExpr.value, dLowerNum, activityLogLeft, activityLogRight, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectDUpper_value (v x : ℝ) :
    reflectDUpper.value v x = dUpperNum v x := by
  simp only [reflectDUpper, PolynomialExpr.value, reflectDLogDen_value, dUpperNum, activityLogMidpointUpper, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectDSupport_value (v x : ℝ) :
    reflectDSupport.value v x = dSupportDen v := by
  simp only [reflectDSupport, PolynomialExpr.value, dSupportDen, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectDSupportNum_value (v x : ℝ) :
    reflectDSupportNum.value v x = dSupportNum v := by
  simp only [reflectDSupportNum, PolynomialExpr.value, dSupportNum, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectDIntercept0_value (v x : ℝ) :
    reflectDIntercept0.value v x = dInterceptNum0 v := by
  simp only [reflectDIntercept0, PolynomialExpr.value, reflectDSupport_value, reflectDSupportNum_value, dInterceptNum0, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectDIntercept1_value (v x : ℝ) :
    reflectDIntercept1.value v x = dInterceptNum1 v := by
  simp only [reflectDIntercept1, PolynomialExpr.value, reflectDSupport_value, reflectDSupportNum_value, dInterceptNum1, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectDIntercept2_value (v x : ℝ) :
    reflectDIntercept2.value v x = dInterceptNum2 v := by
  simp only [reflectDIntercept2, PolynomialExpr.value, reflectDSupport_value, reflectDSupportNum_value, dInterceptNum2, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectDZeroVertex_value (v x : ℝ) :
    reflectDZeroVertex.value v x = dZeroVertexNum v := by
  simp only [reflectDZeroVertex, PolynomialExpr.value, reflectDIntercept0_value, dZeroVertexNum, dInterceptNum0, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectDVertex0_value (v x : ℝ) :
    reflectDVertex0.value v x = dVertexNum v 0 := by
  simp only [reflectDVertex0, PolynomialExpr.value, reflectDZeroVertex_value, dVertexNum, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectDVertex1_value (v x : ℝ) :
    reflectDVertex1.value v x = dVertexNum v 1 := by
  simp only [reflectDVertex1, PolynomialExpr.value, reflectDIntercept0_value, reflectDIntercept1_value, dVertexNum, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectDVertex2_value (v x : ℝ) :
    reflectDVertex2.value v x = dVertexNum v 2 := by
  simp only [reflectDVertex2, PolynomialExpr.value, reflectDIntercept1_value, reflectDIntercept2_value, dVertexNum, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectDVertex3_value (v x : ℝ) :
    reflectDVertex3.value v x = dVertexNum v 3 := by
  simp only [reflectDVertex3, PolynomialExpr.value, reflectDSupport_value, dVertexNum, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectDHeight0_value (v x : ℝ) :
    reflectDHeight0.value v x = dHeightNum v 0 := by
  simp only [reflectDHeight0, PolynomialExpr.value, dHeightNum, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectDHeight1_value (v x : ℝ) :
    reflectDHeight1.value v x = dHeightNum v 1 := by
  simp only [reflectDHeight1, PolynomialExpr.value, reflectDIntercept0_value, reflectDVertex1_value, dHeightNum, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectDHeight2_value (v x : ℝ) :
    reflectDHeight2.value v x = dHeightNum v 2 := by
  simp only [reflectDHeight2, PolynomialExpr.value, reflectDIntercept1_value, reflectDVertex2_value, dHeightNum, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectDHeight3_value (v x : ℝ) :
    reflectDHeight3.value v x = dHeightNum v 3 := by
  simp only [reflectDHeight3, PolynomialExpr.value, reflectDSupport_value, reflectDIntercept2_value, dHeightNum, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectDParentUpper_value (v x : ℝ) :
    reflectDParentUpper.value v x = dParentUpperNum v x := by
  simp only [reflectDParentUpper, PolynomialExpr.value, reflectDBase_value, reflectDProb_value, reflectDGamma_value, dParentUpperNum, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectDParentLower_value (v x : ℝ) :
    reflectDParentLower.value v x = dParentLowerNum v x := by
  simp only [reflectDParentLower, PolynomialExpr.value, reflectDBase_value, reflectDProb_value, reflectDGamma_value, reflectDVacancy_value, dParentLowerNum, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectDNUpper_value (v x : ℝ) :
    reflectDNUpper.value v x = dNUpperNum v x := by
  simp only [reflectDNUpper, PolynomialExpr.value, reflectDBase_value, reflectDParentUpper_value, dNUpperNum, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem reflectDNLower_value (v x : ℝ) :
    reflectDNLower.value v x = dNLowerNum v x := by
  simp only [reflectDNLower, PolynomialExpr.value, reflectDBase_value, reflectDAlpha_value, reflectDVacancy_value, reflectDParentLower_value, dNLowerNum, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

end F4Heavy.Analysis
