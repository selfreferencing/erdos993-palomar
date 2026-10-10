module

public import Erdos993Lean.Analytic.V213.LowMeanScalarShape
public import Erdos993Lean.Analytic.V213.LowMeanIntegerOrder

/-! Exact syntax for the six curved signs and switch-aware ratio floors. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

def lowMeanCertificateCurvedB (c : LowMeanCertificateInput) : LowMeanIntegerShape :=
  lowMeanShapeSub (.add (.mul (lowMeanShapeInt 4) (.atom c.beta))
    (.mul (.mul (lowMeanShapeInt 8) (.atom c.gamma)) (.atom c.m0)))
    (.mul (.mul (lowMeanShapeInt 4) (.atom c.gamma)) (.atom c.D))
def lowMeanCertificateCurvedH (c : LowMeanCertificateInput) (q : LowMeanIntegerShape) : LowMeanIntegerShape :=
  .add (lowMeanShapeSub (.mul (.mul (.mul (lowMeanShapeInt 4) (.atom c.eta)) (.atom c.theta)) (.pow q 3))
    (.mul (lowMeanCertificateCurvedB c) q)) (.mul (lowMeanShapeInt 32) (.atom c.gamma))
def lowMeanCertificateCurvedHD (c : LowMeanCertificateInput) (q : LowMeanIntegerShape) : LowMeanIntegerShape :=
  lowMeanShapeSub (.mul (.mul (.mul (lowMeanShapeInt 12) (.atom c.eta)) (.atom c.theta)) (.pow q 2))
    (lowMeanCertificateCurvedB c)
def lowMeanCertificateRatioHigh (c : LowMeanCertificateInput) (rho : lowMeanFraction) : LowMeanIntegerShape :=
  lowMeanShapeSub (.div (lowMeanShapeRate (.atom c.h)) (.atom c.h)) (.atom rho)
def lowMeanCertificateRatioSwitch (rho : lowMeanFraction) : LowMeanIntegerShape :=
  lowMeanShapeSub (.add (.div (lowMeanShapeRateBase (.atom (3, 7))) (.atom (3, 7)))
    (.div (.atom (-1, 125)) (.atom (3, 7)))) (.atom rho)

@[simp] theorem lowMean_certificate_curvedB_real (c : LowMeanCertificateInput) :
    lowMeanIntegerShapeReal (lowMeanCertificateCurvedB c) = lowMeanCurvedB (lowMeanFractionReal c.beta)
      (lowMeanFractionReal c.gamma) (lowMeanFractionReal c.m0) (lowMeanFractionReal c.D) := by
  simp [lowMeanCertificateCurvedB, lowMeanIntegerShapeReal, lowMeanCurvedB]
@[simp] theorem lowMean_certificate_curvedH_real (c : LowMeanCertificateInput) (q : LowMeanIntegerShape) :
    lowMeanIntegerShapeReal (lowMeanCertificateCurvedH c q) = lowMeanCurvedH (lowMeanFractionReal c.beta)
      (lowMeanFractionReal c.gamma) (lowMeanFractionReal c.m0) (lowMeanFractionReal c.eta)
      (lowMeanFractionReal c.theta) (lowMeanFractionReal c.D) (lowMeanIntegerShapeReal q) := by
  simp [lowMeanCertificateCurvedH, lowMeanIntegerShapeReal, lowMeanCurvedH]
@[simp] theorem lowMean_certificate_curvedHD_real (c : LowMeanCertificateInput) (q : LowMeanIntegerShape) :
    lowMeanIntegerShapeReal (lowMeanCertificateCurvedHD c q) = lowMeanCurvedHD (lowMeanFractionReal c.beta)
      (lowMeanFractionReal c.gamma) (lowMeanFractionReal c.m0) (lowMeanFractionReal c.eta)
      (lowMeanFractionReal c.theta) (lowMeanFractionReal c.D) (lowMeanIntegerShapeReal q) := by
  simp [lowMeanCertificateCurvedHD, lowMeanIntegerShapeReal, lowMeanCurvedHD]
@[simp] theorem lowMean_certificate_ratioHigh_real (c : LowMeanCertificateInput) (rho : lowMeanFraction) :
    lowMeanIntegerShapeReal (lowMeanCertificateRatioHigh c rho) =
      lowMeanRate (lowMeanFractionReal c.h) / lowMeanFractionReal c.h - lowMeanFractionReal rho := by
  simp [lowMeanCertificateRatioHigh, lowMeanIntegerShapeReal]
@[simp] theorem lowMean_certificate_ratioSwitch_real (rho : lowMeanFraction) :
    lowMeanIntegerShapeReal (lowMeanCertificateRatioSwitch rho) =
      lowMeanRateRatioBase (3 / 7) + (-1 / 125) / (3 / 7) - lowMeanFractionReal rho := by
  have hq : (3 / 7 : ℝ) ≠ 0 := by norm_num
  have he : lowMeanRateBase (3 / 7) / (3 / 7) = lowMeanRateRatioBase (3 / 7) := by
    unfold lowMeanRateBase lowMeanRateRatioBase
    field_simp
  simp [lowMeanCertificateRatioSwitch, lowMeanIntegerShapeReal, lowMeanFractionReal, he]

end Erdos993Lean.Analytic.V213
