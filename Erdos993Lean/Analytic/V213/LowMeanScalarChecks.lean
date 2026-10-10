module

public import Erdos993Lean.Analytic.V213.LowMeanScalarChecker

/-! Grouped Int/Nat kernel checks of the reviewed finite scalar records. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

theorem lowMean_cutoffs_kernel : (List.range 28).all lowMeanCutoffCheck = true := by
  decide +kernel

theorem lowMean_slopes_kernel : (List.range 12).all lowMeanSlopeCheck = true := by
  decide +kernel

theorem lowMean_means_kernel : (List.range 56).all lowMeanMeanCheck = true := by
  decide +kernel

/-- The 28 exact discharge budgets exceed the printed b_T/10^6, and hence
also exceed the paper's epsilon=1/100000. -/
theorem lowMean_cutoffs_positive (i : ℕ) (hi : i < 28) :
    (1 / 100000 : ℝ) < lowMeanIntegerShapeReal (lowMeanCertificateCutoff (lowMeanCutoffAt i).1) := by
  have h := Erdos993Lean.F4Fast.forall_lt_of_range_all lowMean_cutoffs_kernel i hi
  simp only [lowMeanCutoffCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  have hp := lowMean_integerPositive_sound h.1
  have hb := (lowMean_fraction_lt_iff (x := (1, 100000)) (by decide) h.2.1).mp h.2.2
  exact lt_trans (by simpa [lowMeanFractionReal] using hb) hp

/-- Twelve exact slope comparisons from Table 3, rather than 43 repeated
slope calculations. -/
theorem lowMean_slopes_positive (i : ℕ) (hi : i < 12) :
    0 < lowMeanIntegerShapeReal (lowMeanCertificateSlope (lowMeanSlopeAt i).1 (lowMeanSlopeAt i).2.2.2) := by
  have h := Erdos993Lean.F4Fast.forall_lt_of_range_all lowMean_slopes_kernel i hi
  simp only [lowMeanSlopeCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  have hp := lowMean_integerPositive_sound h.1
  have hb := (lowMean_fraction_lt_iff (x := (0, 1)) (by decide) h.2.1).mp h.2.2
  exact lt_trans (by simpa [lowMeanFractionReal] using hb) hp

/-- The 56 Table 4 endpoint expressions, indexed by (certificate,side) in
the data, each exceed 1/5000. The three lower curved endpoints use eq63. -/
theorem lowMean_means_positive (i : ℕ) (hi : i < 56) :
    (1 / 5000 : ℝ) < lowMeanIntegerShapeReal (lowMeanMeanRecordShape (lowMeanMeanAt i)) := by
  have h := Erdos993Lean.F4Fast.forall_lt_of_range_all lowMean_means_kernel i hi
  simp only [lowMeanMeanCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  have hp := lowMean_integerPositive_sound h.1
  have hb := (lowMean_fraction_lt_iff (x := (1, 5000)) (by decide) h.2.1).mp h.2.2
  exact lt_trans (by simpa [lowMeanFractionReal] using hb) hp


theorem lowMean_certificateIntervals_kernel : (List.range 28).all lowMeanCertificateIntervalCheck = true := by
  decide +kernel

/-- On every certificate interval (the eleven printed group intervals),
equation 61 dominates the exact endpoint rate floor. This discharges the
ellK <= ell premise of the rational mean comparison. -/
theorem lowMean_all_certificate_rateFloors (i : ℕ) (hi : i < 28) {q : ℝ}
    (hq : q ∈ Set.Icc (lowMeanFractionReal (lowMeanCertificateAt i).l)
      (lowMeanFractionReal (lowMeanCertificateAt i).h)) :
    lowMeanIntegerShapeReal (lowMeanCertificateRateFloor (lowMeanCertificateAt i)) ≤ lowMeanRate q := by
  have h := Erdos993Lean.F4Fast.forall_lt_of_range_all lowMean_certificateIntervals_kernel i hi
  simp only [lowMeanCertificateIntervalCheck, decide_eq_true_eq] at h
  have hl := (lowMean_fraction_le_iff (x := (1, 4)) (by decide) h.1).mp h.2.2.1
  have hh := (lowMean_fraction_le_iff (y := (7, 10)) h.2.1 (by decide)).mp h.2.2.2.1
  apply lowMean_certificate_rateFloor
    (by simpa [lowMeanFractionReal] using hl) (by simpa [lowMeanFractionReal] using hh) hq


/-- The exact tail discharge formula, with v equal to max_Q q(1-q). -/
theorem lowMean_cutoffs_explicit (i : ℕ) (hi : i < 28) :
    let c := (lowMeanCutoffAt i).1
    (1 / 100000 : ℝ) < 2 * lowMeanFractionReal c.gamma * ((c.T : ℝ) - lowMeanFractionReal c.m0) +
      lowMeanFractionReal c.gamma - lowMeanFractionReal c.beta - lowMeanFractionReal c.eta *
        lowMeanVarianceMaximum (lowMeanFractionReal c.l) (lowMeanFractionReal c.h) -
      lowMeanFractionReal c.z * (1 - lowMeanFractionReal c.l) ^ c.T := by
  simpa only [lowMean_certificate_cutoff_real] using lowMean_cutoffs_positive i hi

/-- Table 3's twelve exact positive lower slope formulas. -/
theorem lowMean_slopes_explicit (i : ℕ) (hi : i < 12) :
    let c := (lowMeanSlopeAt i).1
    let r := (lowMeanSlopeAt i).2.2.2
    (0 : ℝ) < lowMeanFractionReal c.beta + lowMeanFractionReal c.gamma + lowMeanFractionReal c.eta *
      lowMeanVarianceMaximum (lowMeanFractionReal c.l) (lowMeanFractionReal c.h) -
      2 * lowMeanFractionReal c.gamma * ((r : ℝ) - lowMeanFractionReal c.m0) := by
  simpa only [lowMean_certificate_slope_real] using lowMean_slopes_positive i hi

/-- All Table 4 lower and upper comparisons, with eq63 at the three
curved lower boundaries. This is a real mathematical formula statement. -/
theorem lowMean_means_explicit (i : ℕ) (hi : i < 56) :
    (1 / 5000 : ℝ) < lowMeanMeanRecordValue (lowMeanMeanAt i) := by
  simpa only [lowMean_meanRecord_shape_real] using lowMean_means_positive i hi

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMean_cutoffs_positive
#print axioms Erdos993Lean.Analytic.V213.lowMean_slopes_positive
#print axioms Erdos993Lean.Analytic.V213.lowMean_means_positive

#print axioms Erdos993Lean.Analytic.V213.lowMean_all_certificate_rateFloors
