module

public import F4Heavy.Analysis.HIdentityCoordinates

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

def upperIntercept1 : PolynomialExpr :=
  (.add (.mul (.const ⟨(516659173), 5000000000⟩) sampleSupport) (.mul (.add (.const ⟨(1762035691), 10000000000⟩) (.mul (.const ⟨(-1), 1⟩) (.const ⟨(516659173), 5000000000⟩))) sampleSupportNum))

def upperIntercept2 : PolynomialExpr :=
  (.add (.mul (.const ⟨(8871047271), 10000000000⟩) sampleSupport) (.mul (.add (.const ⟨(9444767991), 10000000000⟩) (.mul (.const ⟨(-1), 1⟩) (.const ⟨(8871047271), 10000000000⟩))) sampleSupportNum))

def upperIntercept4 : PolynomialExpr :=
  (.add (.mul (.const ⟨(10178601269), 2500000000⟩) sampleSupport) (.mul (.add (.const ⟨(10226130853), 2500000000⟩) (.mul (.const ⟨(-1), 1⟩) (.const ⟨(10178601269), 2500000000⟩))) sampleSupportNum))

def upperVertex1 : PolynomialExpr :=
  (.mul (.add upperIntercept1 (.mul (.const ⟨(-1), 1⟩) sampleIntercept)) (.const ⟨(10), 21⟩))

def upperVertex2 : PolynomialExpr :=
  (.mul (.add upperIntercept2 (.mul (.const ⟨(-1), 1⟩) upperIntercept1)) (.const ⟨(10), 9⟩))

def upperVertex3 : PolynomialExpr :=
  (.mul (.add upperIntercept4 (.mul (.const ⟨(-1), 1⟩) upperIntercept2)) (.const ⟨(5), 17⟩))

def upperVertex4 : PolynomialExpr :=
  sampleSupport

def upperHeight0 : PolynomialExpr :=
  (.const ⟨(0), 1⟩)

def upperHeight1 : PolynomialExpr :=
  (.add (.mul (.const ⟨(12), 5⟩) upperVertex1) sampleIntercept)

def upperHeight2 : PolynomialExpr :=
  (.add (.mul (.const ⟨(3), 10⟩) upperVertex2) upperIntercept1)

def upperHeight3 : PolynomialExpr :=
  (.add (.mul (.const ⟨(-3), 5⟩) upperVertex3) upperIntercept2)

def upperHeight4 : PolynomialExpr :=
  (.add (.mul (.const ⟨(-4), 1⟩) sampleSupport) upperIntercept4)

theorem upperIntercept1_value (v x : ℝ) :
    upperIntercept1.value v x = hInterceptNum1 v := by
  simp only [upperIntercept1, PolynomialExpr.value, sampleSupport_value, sampleSupportNum_value, hInterceptNum1, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem upperIntercept2_value (v x : ℝ) :
    upperIntercept2.value v x = hInterceptNum2 v := by
  simp only [upperIntercept2, PolynomialExpr.value, sampleSupport_value, sampleSupportNum_value, hInterceptNum2, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem upperIntercept4_value (v x : ℝ) :
    upperIntercept4.value v x = hInterceptNum4 v := by
  simp only [upperIntercept4, PolynomialExpr.value, sampleSupport_value, sampleSupportNum_value, hInterceptNum4, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem upperVertex1_value (v x : ℝ) :
    upperVertex1.value v x = hVertexNum v 1 := by
  simp only [upperVertex1, PolynomialExpr.value, sampleIntercept_value, upperIntercept1_value, hVertexNum, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem upperVertex2_value (v x : ℝ) :
    upperVertex2.value v x = hVertexNum v 2 := by
  simp only [upperVertex2, PolynomialExpr.value, upperIntercept1_value, upperIntercept2_value, hVertexNum, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem upperVertex3_value (v x : ℝ) :
    upperVertex3.value v x = hVertexNum v 3 := by
  simp only [upperVertex3, PolynomialExpr.value, upperIntercept2_value, upperIntercept4_value, hVertexNum, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem upperVertex4_value (v x : ℝ) :
    upperVertex4.value v x = hVertexNum v 4 := by
  simp only [upperVertex4, PolynomialExpr.value, sampleSupport_value, hVertexNum, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem upperHeight0_value (v x : ℝ) :
    upperHeight0.value v x = hHeightNum v 0 := by
  simp only [upperHeight0, PolynomialExpr.value, hHeightNum, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem upperHeight1_value (v x : ℝ) :
    upperHeight1.value v x = hHeightNum v 1 := by
  simp only [upperHeight1, PolynomialExpr.value, sampleIntercept_value, upperVertex1_value, hHeightNum, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem upperHeight2_value (v x : ℝ) :
    upperHeight2.value v x = hHeightNum v 2 := by
  simp only [upperHeight2, PolynomialExpr.value, upperIntercept1_value, upperVertex2_value, hHeightNum, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem upperHeight3_value (v x : ℝ) :
    upperHeight3.value v x = hHeightNum v 3 := by
  simp only [upperHeight3, PolynomialExpr.value, upperIntercept2_value, upperVertex3_value, hHeightNum, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

theorem upperHeight4_value (v x : ℝ) :
    upperHeight4.value v x = hHeightNum v 4 := by
  simp only [upperHeight4, PolynomialExpr.value, sampleSupport_value, upperIntercept4_value, hHeightNum, fractionValue, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]
  <;> ring

end F4Heavy.Analysis
