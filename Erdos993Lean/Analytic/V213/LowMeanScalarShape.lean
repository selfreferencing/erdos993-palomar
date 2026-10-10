module

public import Erdos993Lean.Analytic.V213.LowMeanBudgetShape
public import Erdos993Lean.Analytic.V213.LowMeanCurvedMean
public import Erdos993Lean.Analytic.V213.LowMeanVarianceMaximum

/-!
Exact scalar formula syntax for the reviewed finite records. Cutoffs,
width slopes, fixed and curved mean comparisons, and the printed rate use
the same certificate leaves. The E60 syntax is exactly a sum through 60.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

structure LowMeanCertificateInput where
  wL : lowMeanFraction
  wR : lowMeanFraction
  eta : lowMeanFraction
  xi : lowMeanFraction
  alpha : lowMeanFraction
  beta : lowMeanFraction
  gamma : lowMeanFraction
  m0 : lowMeanFraction
  z : lowMeanFraction
  l : lowMeanFraction
  h : lowMeanFraction
  D : lowMeanFraction
  theta : lowMeanFraction
  muA : lowMeanFraction
  muB : lowMeanFraction
  T : ℕ

def lowMeanShapeVarianceMaximum (l h : LowMeanIntegerShape) : LowMeanIntegerShape :=
  let half := .atom (1, 2)
  let ends := .maximum (.mul l (lowMeanShapeSub (lowMeanShapeInt 1) l))
    (.mul h (lowMeanShapeSub (lowMeanShapeInt 1) h))
  .selectLE l half (.selectLE half h (.atom (1, 4)) ends) ends

def lowMeanShapeRateBase (q : LowMeanIntegerShape) : LowMeanIntegerShape :=
  .div (.mul (.mul (.mul (lowMeanShapeInt 2) q) (.add (lowMeanShapeInt 1) (.mul (lowMeanShapeInt 2) q)))
    (lowMeanShapeSub (lowMeanShapeInt 1) q))
    (.mul (.add (lowMeanShapeInt 1) q) (lowMeanShapeSub (lowMeanShapeInt 2) q))
def lowMeanShapeRate (q : LowMeanIntegerShape) : LowMeanIntegerShape :=
  .add (lowMeanShapeRateBase q) (.selectLT q (.atom (3, 7)) (.atom (-1, 125)) (.atom (3, 1250)))
def lowMeanCertificateRateFloor (c : LowMeanCertificateInput) : LowMeanIntegerShape :=
  .minimum (lowMeanShapeRate (.atom c.l)) (lowMeanShapeRate (.atom c.h))
def lowMeanCertificateVariance (c : LowMeanCertificateInput) : LowMeanIntegerShape :=
  lowMeanShapeVarianceMaximum (.atom c.l) (.atom c.h)
def lowMeanShapeE60 (x : LowMeanIntegerShape) : LowMeanIntegerShape :=
  lowMeanShapeSum ((List.range 61).map fun r => .div (.pow x r) (lowMeanShapeInt r.factorial))
def lowMeanCertificatePsi (c : LowMeanCertificateInput) (m : LowMeanIntegerShape) : LowMeanIntegerShape :=
  lowMeanShapePsi (.atom c.alpha) (.atom c.beta) (.atom c.gamma) (.atom c.m0) m

def lowMeanCertificateCutoff (c : LowMeanCertificateInput) : LowMeanIntegerShape :=
  lowMeanShapeSub (lowMeanShapeSub (lowMeanShapeSub
    (.add (.mul (.mul (lowMeanShapeInt 2) (.atom c.gamma)) (lowMeanShapeSub (lowMeanShapeInt c.T) (.atom c.m0)))
      (.atom c.gamma)) (.atom c.beta)) (.mul (.atom c.eta) (lowMeanCertificateVariance c)))
    (.mul (.atom c.z) (.pow (lowMeanShapeSub (lowMeanShapeInt 1) (.atom c.l)) c.T))
def lowMeanCertificateSlope (c : LowMeanCertificateInput) (r : ℕ) : LowMeanIntegerShape :=
  lowMeanShapeSub (.add (.add (.atom c.beta) (.atom c.gamma)) (.mul (.atom c.eta) (lowMeanCertificateVariance c)))
    (.mul (.mul (lowMeanShapeInt 2) (.atom c.gamma)) (lowMeanShapeSub (lowMeanShapeInt r) (.atom c.m0)))
def lowMeanCertificateMean (c : LowMeanCertificateInput) (mu : LowMeanIntegerShape) : LowMeanIntegerShape :=
  lowMeanShapeSub (lowMeanShapeSub (lowMeanShapeSub (lowMeanCertificatePsi c mu)
    (.mul (.mul (.atom c.gamma) (.atom c.D)) mu))
    (.mul (.mul (.mul (.atom c.eta) (.atom c.theta)) (lowMeanCertificateVariance c)) mu))
    (.div (.atom c.z) (lowMeanShapeE60 (.mul (lowMeanCertificateRateFloor c) mu)))
def lowMeanCertificateCurvedA (c : LowMeanCertificateInput) (q : LowMeanIntegerShape) : LowMeanIntegerShape :=
  lowMeanShapeSub (lowMeanShapeSub (lowMeanCertificatePsi c (.div (lowMeanShapeInt 4) q))
    (.div (.mul (.mul (lowMeanShapeInt 4) (.atom c.gamma)) (.atom c.D)) q))
    (.mul (.mul (.mul (lowMeanShapeInt 4) (.atom c.eta)) (.atom c.theta)) (lowMeanShapeSub (lowMeanShapeInt 1) q))
def lowMeanCertificateCurvedMean (c : LowMeanCertificateInput) (q rho : lowMeanFraction) : LowMeanIntegerShape :=
  lowMeanShapeSub (lowMeanCertificateCurvedA c (.atom q))
    (.div (.atom c.z) (lowMeanShapeE60 (.mul (lowMeanShapeInt 4) (.atom rho))))

@[simp] theorem lowMean_shape_varianceMaximum (l h : LowMeanIntegerShape) :
    lowMeanIntegerShapeReal (lowMeanShapeVarianceMaximum l h) =
      lowMeanVarianceMaximum (lowMeanIntegerShapeReal l) (lowMeanIntegerShapeReal h) := by
  simp only [lowMeanShapeVarianceMaximum, lowMeanIntegerShapeReal, lowMean_shape_sub, lowMean_shape_int,
    lowMeanFractionReal, Int.cast_one, Int.cast_ofNat, Nat.cast_ofNat, lowMeanVarianceMaximum]
  split_ifs <;> simp_all <;> linarith
@[simp] theorem lowMean_shape_rateBase (q : LowMeanIntegerShape) :
    lowMeanIntegerShapeReal (lowMeanShapeRateBase q) = lowMeanRateBase (lowMeanIntegerShapeReal q) := by
  simp [lowMeanShapeRateBase, lowMeanIntegerShapeReal, lowMeanRateBase]
@[simp] theorem lowMean_shape_rate (q : LowMeanIntegerShape) :
    lowMeanIntegerShapeReal (lowMeanShapeRate q) = lowMeanRate (lowMeanIntegerShapeReal q) := by
  simp [lowMeanShapeRate, lowMeanIntegerShapeReal, lowMeanFractionReal, lowMeanRate]
@[simp] theorem lowMean_shape_E60 (x : LowMeanIntegerShape) :
    lowMeanIntegerShapeReal (lowMeanShapeE60 x) = lowMeanE60 (lowMeanIntegerShapeReal x) := by
  have hr (n : ℕ) (f : ℕ → ℝ) : (List.map f (List.range n)).sum = ∑ r ∈ Finset.range n, f r := by
    induction n with
    | zero => simp
    | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]
  simp [lowMeanShapeE60, List.map_map, Function.comp_def, lowMeanIntegerShapeReal, lowMeanE60, hr]


@[simp] theorem lowMean_certificate_rateFloor_real (c : LowMeanCertificateInput) :
    lowMeanIntegerShapeReal (lowMeanCertificateRateFloor c) =
      min (lowMeanRate (lowMeanFractionReal c.l)) (lowMeanRate (lowMeanFractionReal c.h)) := by
  simp [lowMeanCertificateRateFloor, lowMeanIntegerShapeReal]
@[simp] theorem lowMean_certificate_variance_real (c : LowMeanCertificateInput) :
    lowMeanIntegerShapeReal (lowMeanCertificateVariance c) =
      lowMeanVarianceMaximum (lowMeanFractionReal c.l) (lowMeanFractionReal c.h) := by
  simp [lowMeanCertificateVariance, lowMeanIntegerShapeReal]
@[simp] theorem lowMean_certificate_psi_real (c : LowMeanCertificateInput) (mu : LowMeanIntegerShape) :
    lowMeanIntegerShapeReal (lowMeanCertificatePsi c mu) = lowMeanPsi (lowMeanFractionReal c.alpha)
      (lowMeanFractionReal c.beta) (lowMeanFractionReal c.gamma) (lowMeanFractionReal c.m0)
      (lowMeanIntegerShapeReal mu) := by
  simp [lowMeanCertificatePsi, lowMeanIntegerShapeReal]
@[simp] theorem lowMean_certificate_cutoff_real (c : LowMeanCertificateInput) :
    lowMeanIntegerShapeReal (lowMeanCertificateCutoff c) =
      2 * lowMeanFractionReal c.gamma * ((c.T : ℝ) - lowMeanFractionReal c.m0) + lowMeanFractionReal c.gamma -
      lowMeanFractionReal c.beta - lowMeanFractionReal c.eta *
        lowMeanVarianceMaximum (lowMeanFractionReal c.l) (lowMeanFractionReal c.h) -
      lowMeanFractionReal c.z * (1 - lowMeanFractionReal c.l) ^ c.T := by
  simp [lowMeanCertificateCutoff, lowMeanIntegerShapeReal]
@[simp] theorem lowMean_certificate_slope_real (c : LowMeanCertificateInput) (r : ℕ) :
    lowMeanIntegerShapeReal (lowMeanCertificateSlope c r) =
      lowMeanFractionReal c.beta + lowMeanFractionReal c.gamma + lowMeanFractionReal c.eta *
        lowMeanVarianceMaximum (lowMeanFractionReal c.l) (lowMeanFractionReal c.h) -
      2 * lowMeanFractionReal c.gamma * ((r : ℝ) - lowMeanFractionReal c.m0) := by
  simp [lowMeanCertificateSlope, lowMeanIntegerShapeReal]
@[simp] theorem lowMean_certificate_mean_real (c : LowMeanCertificateInput) (mu : LowMeanIntegerShape) :
    lowMeanIntegerShapeReal (lowMeanCertificateMean c mu) =
      lowMeanPsi (lowMeanFractionReal c.alpha) (lowMeanFractionReal c.beta) (lowMeanFractionReal c.gamma)
        (lowMeanFractionReal c.m0) (lowMeanIntegerShapeReal mu) -
      lowMeanFractionReal c.gamma * lowMeanFractionReal c.D * lowMeanIntegerShapeReal mu -
      lowMeanFractionReal c.eta * lowMeanFractionReal c.theta *
        lowMeanVarianceMaximum (lowMeanFractionReal c.l) (lowMeanFractionReal c.h) * lowMeanIntegerShapeReal mu -
      lowMeanFractionReal c.z / lowMeanE60
        (min (lowMeanRate (lowMeanFractionReal c.l)) (lowMeanRate (lowMeanFractionReal c.h)) * lowMeanIntegerShapeReal mu) := by
  simp [lowMeanCertificateMean, lowMeanIntegerShapeReal]
@[simp] theorem lowMean_certificate_curvedA_real (c : LowMeanCertificateInput) (q : LowMeanIntegerShape) :
    lowMeanIntegerShapeReal (lowMeanCertificateCurvedA c q) =
      lowMeanCurvedA (lowMeanFractionReal c.alpha) (lowMeanFractionReal c.beta) (lowMeanFractionReal c.gamma)
        (lowMeanFractionReal c.m0) (lowMeanFractionReal c.eta) (lowMeanFractionReal c.theta) (lowMeanFractionReal c.D)
        (lowMeanIntegerShapeReal q) := by
  simp [lowMeanCertificateCurvedA, lowMeanIntegerShapeReal, lowMeanCurvedA]
@[simp] theorem lowMean_certificate_curvedMean_real (c : LowMeanCertificateInput) (q rho : lowMeanFraction) :
    lowMeanIntegerShapeReal (lowMeanCertificateCurvedMean c q rho) =
      lowMeanCurvedA (lowMeanFractionReal c.alpha) (lowMeanFractionReal c.beta) (lowMeanFractionReal c.gamma)
        (lowMeanFractionReal c.m0) (lowMeanFractionReal c.eta) (lowMeanFractionReal c.theta) (lowMeanFractionReal c.D)
        (lowMeanFractionReal q) - lowMeanFractionReal c.z / lowMeanE60 (4 * lowMeanFractionReal rho) := by
  simp [lowMeanCertificateCurvedMean, lowMeanIntegerShapeReal]

/-- The rate-floor premise used by the rational mean bridge is proved from
explicit equation 61 and the printed interval range. Finite interval checks
will discharge these endpoint inequalities for every certificate. -/
theorem lowMean_certificate_rateFloor {c : LowMeanCertificateInput} {q : ℝ}
    (hl : (1 / 4 : ℝ) ≤ lowMeanFractionReal c.l)
    (hh : lowMeanFractionReal c.h ≤ (7 / 10 : ℝ))
    (hq : q ∈ Set.Icc (lowMeanFractionReal c.l) (lowMeanFractionReal c.h)) :
    lowMeanIntegerShapeReal (lowMeanCertificateRateFloor c) ≤ lowMeanRate q := by
  rw [lowMean_certificate_rateFloor_real]
  exact lowMean_rate_endpoint_min hl hh hq

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMean_shape_E60
