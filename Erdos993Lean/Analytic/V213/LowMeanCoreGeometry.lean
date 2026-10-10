module

public import Erdos993Lean.Analytic.V213.LowMeanCoreShape
public import Erdos993Lean.Analytic.V213.LowMeanBudgetShape
public import Erdos993Lean.Analytic.V213.LowMeanScalarShape

/-!
The exact two core tests and tail boundary formulas. The first
kernel bound uses separately certified exact finite maxima, so these large
maximum formulas need be checked once per fiber rather than once per rank.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

def lowMeanShapeCoreShift (c : LowMeanCertificateInput) (j : ℤ) : LowMeanIntegerShape :=
  .add (lowMeanShapeInt j) (.div (.atom c.xi) (.mul (lowMeanShapeInt 2) (.atom c.eta)))
def lowMeanShapeCoreDistance (c : LowMeanCertificateInput) (M : ℕ) (j : ℤ) : LowMeanIntegerShape :=
  .maximum (lowMeanShapeInt 0)
    (.maximum (lowMeanShapeSub (.mul (lowMeanShapeInt M) (.atom c.l)) (lowMeanShapeCoreShift c j))
      (lowMeanShapeSub (lowMeanShapeCoreShift c j) (.mul (lowMeanShapeInt M) (.atom c.h))))
def lowMeanShapeCoreH (c : LowMeanCertificateInput) (M : ℕ) (zeta : lowMeanFraction) : LowMeanIntegerShape :=
  .add (lowMeanShapeSub
    (.add (lowMeanShapePsi (.atom c.alpha) (.atom c.beta) (.atom c.gamma) (.atom c.m0) (lowMeanShapeInt M))
      (.div (.pow (.atom c.xi) 2) (.mul (lowMeanShapeInt 4) (.atom c.eta))))
    (.mul (.atom c.z) (.pow (lowMeanShapeSub (lowMeanShapeInt 1) (.atom c.h)) M))) (.atom zeta)
def lowMeanShapeKernelKValues (c : LowMeanCertificateInput) (M : ℕ) (j : ℤ) (gL gR : lowMeanFraction) : LowMeanIntegerShape :=
  if -1 ≤ j ∧ 2 * j < (M : ℤ) - 1 then .mul (.atom c.wR) (.atom gL)
  else if j ≤ (M : ℤ) + 1 ∧ (M : ℤ) + 1 < 2 * j then .mul (.atom c.wL) (.atom gR)
  else lowMeanShapeInt 0

def lowMeanShapeCoreFirst (c : LowMeanCertificateInput) (M : ℕ) (j : ℤ) (zeta gL gR : lowMeanFraction) : LowMeanIntegerShape :=
  lowMeanShapeSub (.add (lowMeanShapeCoreH c M zeta) (lowMeanShapeKernelKValues c M j gL gR))
    (.mul (.atom c.eta) (.pow (lowMeanShapeCoreDistance c M j) 2))
def lowMeanShapeCoreSecond (c : LowMeanCertificateInput) (M : ℕ) (j : ℤ) (zeta : lowMeanFraction) : LowMeanIntegerShape :=
  lowMeanShapeSub (lowMeanShapeSub (lowMeanShapeCoreH c M zeta)
    (.mul (.atom c.eta) (.pow (lowMeanShapeCoreDistance c M j) 2)))
    (lowMeanShapeKernelLInt M j (.atom c.wL) (.atom c.wR) (.atom c.l) (.atom c.h))

def lowMeanShapeCoreLeftSide (c : LowMeanCertificateInput) (M : ℕ) (lo : ℤ) : LowMeanIntegerShape :=
  lowMeanShapeSub (.mul (lowMeanShapeInt M) (.atom c.l)) (lowMeanShapeCoreShift c lo)
def lowMeanShapeCoreRightSide (c : LowMeanCertificateInput) (M : ℕ) (hi : ℤ) : LowMeanIntegerShape :=
  lowMeanShapeSub (lowMeanShapeCoreShift c hi) (.mul (lowMeanShapeInt M) (.atom c.h))
def lowMeanShapeCoreLeftTail (c : LowMeanCertificateInput) (M : ℕ) (lo : ℤ) (zeta : lowMeanFraction) : LowMeanIntegerShape :=
  lowMeanShapeSub (.mul (.atom c.eta) (.pow (lowMeanShapeCoreLeftSide c M lo) 2)) (lowMeanShapeCoreH c M zeta)
def lowMeanShapeCoreRightTail (c : LowMeanCertificateInput) (M : ℕ) (hi : ℤ) (zeta : lowMeanFraction) : LowMeanIntegerShape :=
  lowMeanShapeSub (.mul (.atom c.eta) (.pow (lowMeanShapeCoreRightSide c M hi) 2)) (lowMeanShapeCoreH c M zeta)

@[simp] theorem lowMean_shape_coreShift (c : LowMeanCertificateInput) (j : ℤ) :
    lowMeanIntegerShapeReal (lowMeanShapeCoreShift c j) = (j : ℝ) + lowMeanFractionReal c.xi / (2 * lowMeanFractionReal c.eta) := by
  simp [lowMeanShapeCoreShift, lowMeanIntegerShapeReal]
@[simp] theorem lowMean_shape_coreDistance (c : LowMeanCertificateInput) (M : ℕ) (j : ℤ) :
    lowMeanIntegerShapeReal (lowMeanShapeCoreDistance c M j) =
      lowMeanCoreDistance M j (lowMeanFractionReal c.xi) (lowMeanFractionReal c.eta) (lowMeanFractionReal c.l) (lowMeanFractionReal c.h) := by
  simp [lowMeanShapeCoreDistance, lowMeanIntegerShapeReal, lowMeanCoreDistance]
@[simp] theorem lowMean_shape_coreH (c : LowMeanCertificateInput) (M : ℕ) (zeta : lowMeanFraction) :
    lowMeanIntegerShapeReal (lowMeanShapeCoreH c M zeta) =
      lowMeanCoreH M (lowMeanFractionReal c.xi) (lowMeanFractionReal c.eta) (lowMeanFractionReal c.alpha)
        (lowMeanFractionReal c.beta) (lowMeanFractionReal c.gamma) (lowMeanFractionReal c.m0)
        (lowMeanFractionReal c.z) (lowMeanFractionReal zeta) (lowMeanFractionReal c.h) := by
  simp [lowMeanShapeCoreH, lowMeanIntegerShapeReal, lowMeanCoreH]

theorem lowMean_shape_kernelK_values (c : LowMeanCertificateInput) (M : ℕ) (j : ℤ) (gL gR : lowMeanFraction)
    (hL : lowMeanFractionReal gL = lowMeanClosedMaximum M (lowMeanFractionReal c.l))
    (hR : lowMeanFractionReal gR = lowMeanClosedMaximum M (1 - lowMeanFractionReal c.h)) :
    lowMeanIntegerShapeReal (lowMeanShapeKernelKValues c M j gL gR) =
      lowMeanKernelK M j (lowMeanFractionReal c.wL) (lowMeanFractionReal c.wR) (lowMeanFractionReal c.l) (lowMeanFractionReal c.h) := by
  unfold lowMeanShapeKernelKValues lowMeanKernelK
  split_ifs <;> simp [lowMeanIntegerShapeReal, hL, hR]

theorem lowMean_shape_coreFirst (c : LowMeanCertificateInput) (M : ℕ) (j : ℤ) (zeta gL gR : lowMeanFraction)
    (hL : lowMeanFractionReal gL = lowMeanClosedMaximum M (lowMeanFractionReal c.l))
    (hR : lowMeanFractionReal gR = lowMeanClosedMaximum M (1 - lowMeanFractionReal c.h)) :
    lowMeanIntegerShapeReal (lowMeanShapeCoreFirst c M j zeta gL gR) =
      lowMeanCoreH M (lowMeanFractionReal c.xi) (lowMeanFractionReal c.eta) (lowMeanFractionReal c.alpha)
        (lowMeanFractionReal c.beta) (lowMeanFractionReal c.gamma) (lowMeanFractionReal c.m0)
        (lowMeanFractionReal c.z) (lowMeanFractionReal zeta) (lowMeanFractionReal c.h) +
      lowMeanKernelK M j (lowMeanFractionReal c.wL) (lowMeanFractionReal c.wR) (lowMeanFractionReal c.l) (lowMeanFractionReal c.h) -
      lowMeanFractionReal c.eta * lowMeanCoreDistance M j (lowMeanFractionReal c.xi) (lowMeanFractionReal c.eta)
        (lowMeanFractionReal c.l) (lowMeanFractionReal c.h) ^ 2 := by
  simp [lowMeanShapeCoreFirst, lowMeanIntegerShapeReal, lowMean_shape_kernelK_values c M j gL gR hL hR]
@[simp] theorem lowMean_shape_coreSecond (c : LowMeanCertificateInput) (M : ℕ) (j : ℤ) (zeta : lowMeanFraction) :
    lowMeanIntegerShapeReal (lowMeanShapeCoreSecond c M j zeta) =
      lowMeanCoreH M (lowMeanFractionReal c.xi) (lowMeanFractionReal c.eta) (lowMeanFractionReal c.alpha)
        (lowMeanFractionReal c.beta) (lowMeanFractionReal c.gamma) (lowMeanFractionReal c.m0)
        (lowMeanFractionReal c.z) (lowMeanFractionReal zeta) (lowMeanFractionReal c.h) -
      lowMeanFractionReal c.eta * lowMeanCoreDistance M j (lowMeanFractionReal c.xi) (lowMeanFractionReal c.eta)
        (lowMeanFractionReal c.l) (lowMeanFractionReal c.h) ^ 2 -
      lowMeanKernelLInt M j (lowMeanFractionReal c.wL) (lowMeanFractionReal c.wR) (lowMeanFractionReal c.l) (lowMeanFractionReal c.h) := by
  simp [lowMeanShapeCoreSecond, lowMeanIntegerShapeReal]

@[simp] theorem lowMean_shape_coreLeftSide (c : LowMeanCertificateInput) (M : ℕ) (lo : ℤ) :
    lowMeanIntegerShapeReal (lowMeanShapeCoreLeftSide c M lo) =
      M * lowMeanFractionReal c.l - ((lo : ℝ) + lowMeanFractionReal c.xi / (2 * lowMeanFractionReal c.eta)) := by
  simp [lowMeanShapeCoreLeftSide, lowMeanIntegerShapeReal]
@[simp] theorem lowMean_shape_coreRightSide (c : LowMeanCertificateInput) (M : ℕ) (hi : ℤ) :
    lowMeanIntegerShapeReal (lowMeanShapeCoreRightSide c M hi) =
      ((hi : ℝ) + lowMeanFractionReal c.xi / (2 * lowMeanFractionReal c.eta)) - M * lowMeanFractionReal c.h := by
  simp [lowMeanShapeCoreRightSide, lowMeanIntegerShapeReal]
@[simp] theorem lowMean_shape_coreLeftTail (c : LowMeanCertificateInput) (M : ℕ) (lo : ℤ) (zeta : lowMeanFraction) :
    lowMeanIntegerShapeReal (lowMeanShapeCoreLeftTail c M lo zeta) =
      lowMeanFractionReal c.eta * (M * lowMeanFractionReal c.l - ((lo : ℝ) + lowMeanFractionReal c.xi / (2 * lowMeanFractionReal c.eta))) ^ 2 -
      lowMeanCoreH M (lowMeanFractionReal c.xi) (lowMeanFractionReal c.eta) (lowMeanFractionReal c.alpha)
        (lowMeanFractionReal c.beta) (lowMeanFractionReal c.gamma) (lowMeanFractionReal c.m0)
        (lowMeanFractionReal c.z) (lowMeanFractionReal zeta) (lowMeanFractionReal c.h) := by
  simp [lowMeanShapeCoreLeftTail, lowMeanIntegerShapeReal]
@[simp] theorem lowMean_shape_coreRightTail (c : LowMeanCertificateInput) (M : ℕ) (hi : ℤ) (zeta : lowMeanFraction) :
    lowMeanIntegerShapeReal (lowMeanShapeCoreRightTail c M hi zeta) =
      lowMeanFractionReal c.eta * (((hi : ℝ) + lowMeanFractionReal c.xi / (2 * lowMeanFractionReal c.eta)) - M * lowMeanFractionReal c.h) ^ 2 -
      lowMeanCoreH M (lowMeanFractionReal c.xi) (lowMeanFractionReal c.eta) (lowMeanFractionReal c.alpha)
        (lowMeanFractionReal c.beta) (lowMeanFractionReal c.gamma) (lowMeanFractionReal c.m0)
        (lowMeanFractionReal c.z) (lowMeanFractionReal zeta) (lowMeanFractionReal c.h) := by
  simp [lowMeanShapeCoreRightTail, lowMeanIntegerShapeReal]

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMean_shape_coreFirst
