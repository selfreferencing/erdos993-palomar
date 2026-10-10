module

public import Erdos993Lean.Analytic.V213.LowMeanScalarChecks

/-!
Signs and interval facts for the reviewed certificate parameters.
Equation 61 is strictly positive throughout the common interval range;
its endpoint floor and exact variance maximum feed the actual mean margin.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

deriving instance DecidableEq for LowMeanCertificateInput

def lowMeanCertificateFractions (c : LowMeanCertificateInput) : List lowMeanFraction :=
  [c.wL, c.wR, c.eta, c.xi, c.alpha, c.beta, c.gamma, c.m0, c.z, c.l, c.h, c.D, c.theta, c.muA, c.muB]
def lowMeanCertificateFactsCheck (i : ℕ) : Bool :=
  let c := lowMeanCertificateAt i
  (lowMeanCertificateFractions c).all (fun f => decide (lowMeanFractionValid f)) &&
    decide (0 ≤ c.wL.1 ∧ 0 ≤ c.wR.1 ∧ 0 < c.eta.1 ∧ 0 ≤ c.gamma.1 ∧ 0 ≤ c.z.1 ∧
      0 ≤ c.theta.1 ∧ 0 ≤ c.D.1 ∧ 0 ≤ c.muA.1 ∧ 0 ≤ c.muB.1 ∧ lowMeanFractionLE c.muA c.muB)

theorem lowMean_certificateFacts_kernel : (List.range 28).all lowMeanCertificateFactsCheck = true := by
  decide +kernel

theorem lowMean_rate_positive {q : ℝ} (hq : q ∈ Set.Icc (1 / 4 : ℝ) (7 / 10 : ℝ)) : 0 < lowMeanRate q := by
  have hb := lowMean_concave_endpoint_min lowMean_rateBase_concave hq
  norm_num [lowMeanRateBase] at hb
  change (9 / 35 : ℝ) ≤ lowMeanRateBase q at hb
  have hc : (-1 / 125 : ℝ) ≤ if q < 3 / 7 then -1 / 125 else 3 / 1250 := by
    split_ifs <;> norm_num
  unfold lowMeanRate
  linarith

theorem lowMean_certificate_interval_facts (i : ℕ) (hi : i < 28) :
    let c := lowMeanCertificateAt i
    (1 / 4 : ℝ) ≤ lowMeanFractionReal c.l ∧ lowMeanFractionReal c.h ≤ (7 / 10 : ℝ) ∧
      lowMeanFractionReal c.l < lowMeanFractionReal c.h := by
  have h := Erdos993Lean.F4Fast.forall_lt_of_range_all lowMean_certificateIntervals_kernel i hi
  simp only [lowMeanCertificateIntervalCheck, decide_eq_true_eq] at h
  refine ⟨?_, ?_, (lowMean_fraction_lt_iff h.1 h.2.1).mp h.2.2.2.2⟩
  · simpa [lowMeanFractionReal] using (lowMean_fraction_le_iff (x := (1, 4)) (by decide) h.1).mp h.2.2.1
  · simpa [lowMeanFractionReal] using (lowMean_fraction_le_iff (y := (7, 10)) h.2.1 (by decide)).mp h.2.2.2.1

theorem lowMean_certificate_fraction_valid (i : ℕ) (hi : i < 28) (f : lowMeanFraction)
    (hf : f ∈ lowMeanCertificateFractions (lowMeanCertificateAt i)) : lowMeanFractionValid f := by
  have h := Erdos993Lean.F4Fast.forall_lt_of_range_all lowMean_certificateFacts_kernel i hi
  simp only [lowMeanCertificateFactsCheck, Bool.and_eq_true] at h
  exact of_decide_eq_true (List.all_eq_true.mp h.1 f hf)

theorem lowMean_certificate_signs (i : ℕ) (hi : i < 28) :
    let c := lowMeanCertificateAt i
    0 ≤ lowMeanFractionReal c.wL ∧ 0 ≤ lowMeanFractionReal c.wR ∧ 0 < lowMeanFractionReal c.eta ∧
      0 ≤ lowMeanFractionReal c.gamma ∧ 0 ≤ lowMeanFractionReal c.z ∧ 0 ≤ lowMeanFractionReal c.theta ∧
      0 ≤ lowMeanFractionReal c.D ∧ 0 ≤ lowMeanFractionReal c.muA ∧ 0 ≤ lowMeanFractionReal c.muB := by
  have h := Erdos993Lean.F4Fast.forall_lt_of_range_all lowMean_certificateFacts_kernel i hi
  simp only [lowMeanCertificateFactsCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  have hv f (hf : f ∈ lowMeanCertificateFractions (lowMeanCertificateAt i)) :=
    lowMean_fraction_den_pos (lowMean_certificate_fraction_valid i hi f hf)
  have hn (f : lowMeanFraction) (hf : f ∈ lowMeanCertificateFractions (lowMeanCertificateAt i)) (hnum : 0 ≤ f.1) :
      0 ≤ lowMeanFractionReal f := div_nonneg (by exact_mod_cast hnum) (hv f hf).le
  have hp (f : lowMeanFraction) (hf : f ∈ lowMeanCertificateFractions (lowMeanCertificateAt i)) (hnum : 0 < f.1) :
      0 < lowMeanFractionReal f := div_pos (by exact_mod_cast hnum) (hv f hf)
  refine ⟨hn _ (by simp [lowMeanCertificateFractions]) h.2.1,
    hn _ (by simp [lowMeanCertificateFractions]) h.2.2.1,
    hp _ (by simp [lowMeanCertificateFractions]) h.2.2.2.1,
    hn _ (by simp [lowMeanCertificateFractions]) h.2.2.2.2.1,
    hn _ (by simp [lowMeanCertificateFractions]) h.2.2.2.2.2.1,
    hn _ (by simp [lowMeanCertificateFractions]) h.2.2.2.2.2.2.1,
    hn _ (by simp [lowMeanCertificateFractions]) h.2.2.2.2.2.2.2.1,
    hn _ (by simp [lowMeanCertificateFractions]) h.2.2.2.2.2.2.2.2.1,
    hn _ (by simp [lowMeanCertificateFractions]) h.2.2.2.2.2.2.2.2.2.1⟩

theorem lowMean_certificate_rateFloor_positive (i : ℕ) (hi : i < 28) :
    0 < lowMeanIntegerShapeReal (lowMeanCertificateRateFloor (lowMeanCertificateAt i)) := by
  obtain ⟨hl, hh, hlh⟩ := lowMean_certificate_interval_facts i hi
  rw [lowMean_certificate_rateFloor_real]
  exact lt_min (lowMean_rate_positive ⟨hl, le_trans hlh.le hh⟩)
    (lowMean_rate_positive ⟨le_trans hl hlh.le, hh⟩)

/-- The rational margin bridge with its rate and variance premises discharged
by the exact reviewed interval checks and the equation-61 calculus. -/
theorem lowMean_certificate_rationalMargin_le (i : ℕ) (hi : i < 28) {q mu : ℝ}
    (hq : q ∈ Set.Icc (lowMeanFractionReal (lowMeanCertificateAt i).l) (lowMeanFractionReal (lowMeanCertificateAt i).h))
    (hmu : 0 ≤ mu) :
    lowMeanCertificateRationalMargin (lowMeanCertificateAt i) mu ≤
      lowMeanMargin (lowMeanFractionReal (lowMeanCertificateAt i).alpha) (lowMeanFractionReal (lowMeanCertificateAt i).beta)
        (lowMeanFractionReal (lowMeanCertificateAt i).gamma) (lowMeanFractionReal (lowMeanCertificateAt i).m0)
        (lowMeanFractionReal (lowMeanCertificateAt i).eta) (lowMeanFractionReal (lowMeanCertificateAt i).theta)
        (lowMeanFractionReal (lowMeanCertificateAt i).D) (lowMeanFractionReal (lowMeanCertificateAt i).z)
        (lowMeanRate q) q mu := by
  obtain ⟨_, _, heta, _, hz, htheta, _, _, _⟩ := lowMean_certificate_signs i hi
  apply lowMean_rationalMargin_le heta.le htheta hz hmu
  · simpa only [lowMean_certificate_rateFloor_real] using (lowMean_certificate_rateFloor_positive i hi).le
  · simpa only [lowMean_certificate_rateFloor_real] using lowMean_all_certificate_rateFloors i hi hq
  · exact lowMean_varianceMaximum_bound hq

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMean_certificate_rationalMargin_le
