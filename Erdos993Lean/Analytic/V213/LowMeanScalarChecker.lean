module

public import Erdos993Lean.Analytic.V213.LowMeanScalarData

/-!
Reviewed finite scalar checks. Each grouped kernel decision uses
only Int/Nat fractions and an exact formula shape.

-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

def lowMeanCutoffAt (i : ℕ) : LowMeanCertificateInput × LowMeanIntegerExpr × lowMeanFraction :=
  lowMeanCutoffRecords.getD i (lowMeanCertificate01, .atom (0, 1), (0, 1))
def lowMeanSlopeAt (i : ℕ) : LowMeanCertificateInput × LowMeanIntegerExpr × lowMeanFraction × ℕ :=
  lowMeanSlopeRecords.getD i (lowMeanCertificate01, .atom (0, 1), (0, 1), 0)
def lowMeanMeanAt (i : ℕ) : LowMeanCertificateInput × LowMeanIntegerExpr × lowMeanFraction × Bool × ℕ :=
  lowMeanMeanRecords.getD i (lowMeanCertificate01, .atom (0, 1), (0, 1), false, 0)

def lowMeanMeanRecordShape
    (r : LowMeanCertificateInput × LowMeanIntegerExpr × lowMeanFraction × Bool × ℕ) : LowMeanIntegerShape :=
  let c := r.1
  let lower := r.2.2.2.1
  let index := r.2.2.2.2
  if lower then
    if index = 1 then lowMeanCertificateCurvedMean c c.h (51356, 53625)
    else if index = 2 then lowMeanCertificateCurvedMean c c.h (3823, 4125)
    else if index = 24 then lowMeanCertificateCurvedMean c c.l (3998483, 5557500)
    else lowMeanCertificateMean c (.atom c.muA)
  else lowMeanCertificateMean c (.atom c.muB)

def lowMeanCutoffCheck (i : ℕ) : Bool :=
  let r := lowMeanCutoffAt i
  lowMeanIntegerPositiveCheck r.2.1 (lowMeanCertificateCutoff r.1) r.2.2 &&
    decide (lowMeanFractionValid r.2.2 ∧ lowMeanFractionLT (1, 100000) r.2.2)
def lowMeanSlopeCheck (i : ℕ) : Bool :=
  let r := lowMeanSlopeAt i
  lowMeanIntegerPositiveCheck r.2.1 (lowMeanCertificateSlope r.1 r.2.2.2) r.2.2.1 &&
    decide (lowMeanFractionValid r.2.2.1 ∧ lowMeanFractionLT (0, 1) r.2.2.1)
def lowMeanMeanCheck (i : ℕ) : Bool :=
  let r := lowMeanMeanAt i
  lowMeanIntegerPositiveCheck r.2.1 (lowMeanMeanRecordShape r) r.2.2.1 &&
    decide (lowMeanFractionValid r.2.2.1 ∧ lowMeanFractionLT (1, 5000) r.2.2.1)


def lowMeanCertificateAt (i : ℕ) : LowMeanCertificateInput :=
  lowMeanCertificates.getD i lowMeanCertificate01

def lowMeanCertificateIntervalCheck (i : ℕ) : Bool :=
  let c := lowMeanCertificateAt i
  decide (lowMeanFractionValid c.l ∧ lowMeanFractionValid c.h ∧
    lowMeanFractionLE (1, 4) c.l ∧ lowMeanFractionLE c.h (7, 10) ∧ lowMeanFractionLT c.l c.h)


noncomputable def lowMeanCertificateRationalMargin (c : LowMeanCertificateInput) (mu : ℝ) : ℝ :=
  lowMeanPsi (lowMeanFractionReal c.alpha) (lowMeanFractionReal c.beta) (lowMeanFractionReal c.gamma)
    (lowMeanFractionReal c.m0) mu - lowMeanFractionReal c.gamma * lowMeanFractionReal c.D * mu -
    lowMeanFractionReal c.eta * lowMeanFractionReal c.theta *
      lowMeanVarianceMaximum (lowMeanFractionReal c.l) (lowMeanFractionReal c.h) * mu -
    lowMeanFractionReal c.z / lowMeanE60
      (min (lowMeanRate (lowMeanFractionReal c.l)) (lowMeanRate (lowMeanFractionReal c.h)) * mu)
noncomputable def lowMeanCertificateCurvedEndpoint (c : LowMeanCertificateInput) (q rho : lowMeanFraction) : ℝ :=
  lowMeanCurvedA (lowMeanFractionReal c.alpha) (lowMeanFractionReal c.beta) (lowMeanFractionReal c.gamma)
    (lowMeanFractionReal c.m0) (lowMeanFractionReal c.eta) (lowMeanFractionReal c.theta) (lowMeanFractionReal c.D)
    (lowMeanFractionReal q) - lowMeanFractionReal c.z / lowMeanE60 (4 * lowMeanFractionReal rho)
noncomputable def lowMeanMeanRecordValue
    (r : LowMeanCertificateInput × LowMeanIntegerExpr × lowMeanFraction × Bool × ℕ) : ℝ :=
  let c := r.1
  let lower := r.2.2.2.1
  let index := r.2.2.2.2
  if lower then
    if index = 1 then lowMeanCertificateCurvedEndpoint c c.h (51356, 53625)
    else if index = 2 then lowMeanCertificateCurvedEndpoint c c.h (3823, 4125)
    else if index = 24 then lowMeanCertificateCurvedEndpoint c c.l (3998483, 5557500)
    else lowMeanCertificateRationalMargin c (lowMeanFractionReal c.muA)
  else lowMeanCertificateRationalMargin c (lowMeanFractionReal c.muB)

@[simp] theorem lowMean_meanRecord_shape_real
    (r : LowMeanCertificateInput × LowMeanIntegerExpr × lowMeanFraction × Bool × ℕ) :
    lowMeanIntegerShapeReal (lowMeanMeanRecordShape r) = lowMeanMeanRecordValue r := by
  unfold lowMeanMeanRecordShape lowMeanMeanRecordValue
  dsimp only
  split_ifs <;> simp [lowMeanCertificateCurvedEndpoint, lowMeanCertificateRationalMargin, lowMeanIntegerShapeReal]

end Erdos993Lean.Analytic.V213
