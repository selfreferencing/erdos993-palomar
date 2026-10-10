module

public import Erdos993Lean.Analytic.V213.LowMeanCurvedScalarChecks
public import Erdos993Lean.Analytic.V213.LowMeanMeanKeys

/-!
Actual mean margins on the natural domain. The 56 reviewed endpoint
comparisons, six exact signs, three switch-aware ratio floors, exact v_Q,
and proved equation-61 rate floor are composed without unproved premises.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanCertificateCurvedFunction (c : LowMeanCertificateInput) (q : ℝ) : ℝ :=
  lowMeanCurvedA (lowMeanFractionReal c.alpha) (lowMeanFractionReal c.beta) (lowMeanFractionReal c.gamma)
    (lowMeanFractionReal c.m0) (lowMeanFractionReal c.eta) (lowMeanFractionReal c.theta) (lowMeanFractionReal c.D) q
noncomputable def lowMeanCertificateActualMargin (c : LowMeanCertificateInput) (q mu : ℝ) : ℝ :=
  lowMeanMargin (lowMeanFractionReal c.alpha) (lowMeanFractionReal c.beta) (lowMeanFractionReal c.gamma)
    (lowMeanFractionReal c.m0) (lowMeanFractionReal c.eta) (lowMeanFractionReal c.theta) (lowMeanFractionReal c.D)
    (lowMeanFractionReal c.z) (lowMeanRate q) q mu

theorem lowMean_curve1_antitone :
    AntitoneOn (lowMeanCertificateCurvedFunction lowMeanCertificate01)
      (Set.Icc (lowMeanFractionReal lowMeanCertificate01.l) (lowMeanFractionReal lowMeanCertificate01.h)) := by
  have hs := lowMean_certificate_signs 0 (by decide)
  have hl := (lowMean_certificate_interval_facts 0 (by decide)).1
  rw [show lowMeanCertificateAt 0 = lowMeanCertificate01 by rfl] at hs hl
  have hleft := lowMean_curved_signs 0 (by decide)
  have hright := lowMean_curved_signs 1 (by decide)
  simp only [show (0 : ℕ) < 4 by decide, show (1 : ℕ) < 4 by decide, ite_true] at hleft hright
  apply lowMean_curvedA_antitone (lt_of_lt_of_le (by norm_num) hl) hs.2.2.1.le hs.2.2.2.2.2.1
  · simpa [lowMeanCurvedAt, lowMeanCurvedRecords, lowMeanCurvedRecordValue] using hleft.le
  · simpa [lowMeanCurvedAt, lowMeanCurvedRecords, lowMeanCurvedRecordValue] using hright.le

theorem lowMean_curve2_antitone :
    AntitoneOn (lowMeanCertificateCurvedFunction lowMeanCertificate02)
      (Set.Icc (lowMeanFractionReal lowMeanCertificate02.l) (lowMeanFractionReal lowMeanCertificate02.h)) := by
  have hs := lowMean_certificate_signs 1 (by decide)
  have hl := (lowMean_certificate_interval_facts 1 (by decide)).1
  rw [show lowMeanCertificateAt 1 = lowMeanCertificate02 by rfl] at hs hl
  have hleft := lowMean_curved_signs 2 (by decide)
  have hright := lowMean_curved_signs 3 (by decide)
  simp only [show (2 : ℕ) < 4 by decide, show (3 : ℕ) < 4 by decide, ite_true] at hleft hright
  apply lowMean_curvedA_antitone (lt_of_lt_of_le (by norm_num) hl) hs.2.2.1.le hs.2.2.2.2.2.1
  · simpa [lowMeanCurvedAt, lowMeanCurvedRecords, lowMeanCurvedRecordValue] using hleft.le
  · simpa [lowMeanCurvedAt, lowMeanCurvedRecords, lowMeanCurvedRecordValue] using hright.le

theorem lowMean_curve24_monotone :
    MonotoneOn (lowMeanCertificateCurvedFunction lowMeanCertificate24)
      (Set.Icc (lowMeanFractionReal lowMeanCertificate24.l) (lowMeanFractionReal lowMeanCertificate24.h)) := by
  have hs := lowMean_certificate_signs 23 (by decide)
  have hl := (lowMean_certificate_interval_facts 23 (by decide)).1
  rw [show lowMeanCertificateAt 23 = lowMeanCertificate24 by rfl] at hs hl
  have hleft := lowMean_curved_signs 4 (by decide)
  have hright := lowMean_curved_signs 5 (by decide)
  simp only [show ¬ (4 : ℕ) < 4 by decide, show ¬ (5 : ℕ) < 4 by decide, ite_false] at hleft hright
  apply lowMean_curvedA_monotone (lt_of_lt_of_le (by norm_num) hl) hs.2.2.1.le hs.2.2.2.2.2.1
  · simpa [lowMeanCurvedAt, lowMeanCurvedRecords, lowMeanCurvedRecordValue] using hleft.le
  · simpa [lowMeanCurvedAt, lowMeanCurvedRecords, lowMeanCurvedRecordValue] using hright.le

/-- The selected endpoint is the exact minimum of the curved algebraic
part on each of the three printed intervals. -/
theorem lowMean_curved_endpoint_min (i : ℕ) (hi : i < 3) {q : ℝ}
    (hq : q ∈ Set.Icc (lowMeanFractionReal (lowMeanRatioAt i).1.l) (lowMeanFractionReal (lowMeanRatioAt i).1.h)) :
    lowMeanCertificateCurvedFunction (lowMeanRatioAt i).1
      (lowMeanFractionReal (if i = 2 then (lowMeanRatioAt i).1.l else (lowMeanRatioAt i).1.h)) ≤
      lowMeanCertificateCurvedFunction (lowMeanRatioAt i).1 q := by
  interval_cases i
  · exact lowMean_curve1_antitone hq ⟨le_trans hq.1 hq.2, le_rfl⟩ hq.2
  · exact lowMean_curve2_antitone hq ⟨le_trans hq.1 hq.2, le_rfl⟩ hq.2
  · exact lowMean_curve24_monotone ⟨le_rfl, le_trans hq.1 hq.2⟩ hq hq.1

/-- The three equation-63 lower comparisons bound the actual exponential
margin at 4/q throughout the complete closed probability intervals. -/
theorem lowMean_curved_actual_lower (i : ℕ) (hi : i < 3) {q : ℝ}
    (hq : q ∈ Set.Icc (lowMeanFractionReal (lowMeanRatioAt i).1.l) (lowMeanFractionReal (lowMeanRatioAt i).1.h)) :
    lowMeanCertificateCurvedEndpoint (lowMeanRatioAt i).1
      (if i = 2 then (lowMeanRatioAt i).1.l else (lowMeanRatioAt i).1.h) (lowMeanRatioAt i).2.1 ≤
      lowMeanCertificateActualMargin (lowMeanRatioAt i).1 q (4 / q) := by
  have hk := Erdos993Lean.F4Fast.forall_lt_of_range_all lowMean_ratios_kernel i hi
  simp only [lowMeanRatioCheck, Bool.and_eq_true, decide_eq_true_eq] at hk
  have hidx : (lowMeanRatioAt i).2.2.2.2 - 1 < 28 := by omega
  have hc := hk.1.1.2.2.1
  have hl := (lowMean_certificate_interval_facts _ hidx).1
  have hz := (lowMean_certificate_signs _ hidx).2.2.2.2.1
  rw [← hc] at hl hz
  apply lowMean_curved_margin_lower (lt_of_lt_of_le (lt_of_lt_of_le (by norm_num) hl) hq.1) hz
    (lowMean_ratio_nonnegative i hi) (lowMean_ratio_floors i hi hq)
    (lowMean_curved_endpoint_min i hi hq)


theorem lowMean_certificate_actual_upper (i : ℕ) (hi : i < 28) {q : ℝ}
    (hq : q ∈ Set.Icc (lowMeanFractionReal (lowMeanCertificateAt i).l) (lowMeanFractionReal (lowMeanCertificateAt i).h)) :
    0 < lowMeanCertificateActualMargin (lowMeanCertificateAt i) q (lowMeanFractionReal (lowMeanCertificateAt i).muB) := by
  have hm := (lowMean_meanKey_bounds i hi).2
  have hle := lowMean_certificate_rationalMargin_le i hi hq (lowMean_certificate_signs i hi).2.2.2.2.2.2.2.2
  exact lt_of_lt_of_le (lt_trans (by norm_num) hm) hle

theorem lowMean_certificate_actual_concave (i : ℕ) (hi : i < 28) (q : ℝ) :
    ConcaveOn ℝ Set.univ (lowMeanCertificateActualMargin (lowMeanCertificateAt i) q) := by
  have hs := lowMean_certificate_signs i hi
  exact lowMeanMargin_concave _ _ _ _ _ _ _ _ _ _ hs.2.2.2.1 hs.2.2.2.2.1

/-- Each of the three actual curved lower endpoints is strictly positive. -/
theorem lowMean_curved_actual_positive (i : ℕ) (hi : i < 3) {q : ℝ}
    (hq : q ∈ Set.Icc (lowMeanFractionReal (lowMeanRatioAt i).1.l) (lowMeanFractionReal (lowMeanRatioAt i).1.h)) :
    0 < lowMeanCertificateActualMargin (lowMeanRatioAt i).1 q (4 / q) := by
  have hle := lowMean_curved_actual_lower i hi hq
  apply lt_of_lt_of_le _ hle
  interval_cases i
  · have h := (lowMean_meanKey_bounds 0 (by decide)).1
    change (1 / 5000 : ℝ) < lowMeanCertificateCurvedEndpoint lowMeanCertificate01 lowMeanCertificate01.h (51356, 53625) at h
    exact lt_trans (by norm_num) h
  · have h := (lowMean_meanKey_bounds 1 (by decide)).1
    change (1 / 5000 : ℝ) < lowMeanCertificateCurvedEndpoint lowMeanCertificate02 lowMeanCertificate02.h (3823, 4125) at h
    exact lt_trans (by norm_num) h
  · have h := (lowMean_meanKey_bounds 23 (by decide)).1
    change (1 / 5000 : ℝ) < lowMeanCertificateCurvedEndpoint lowMeanCertificate24 lowMeanCertificate24.l (3998483, 5557500) at h
    exact lt_trans (by norm_num) h

/-- The complete printed natural mean domain for all 28 certificates.
Every numerical, rate, variance, and curved-boundary premise is discharged. -/
theorem lowMean_natural_mean_positive (i : ℕ) (hi : i < 28) {q mu : ℝ}
    (hq : q ∈ Set.Icc (lowMeanFractionReal (lowMeanCertificateAt i).l) (lowMeanFractionReal (lowMeanCertificateAt i).h))
    (hmu : mu ∈ Set.Icc (max (lowMeanFractionReal (lowMeanCertificateAt i).muA) (4 / q))
      (lowMeanFractionReal (lowMeanCertificateAt i).muB)) :
    0 < lowMeanCertificateActualMargin (lowMeanCertificateAt i) q mu := by
  have hup := lowMean_certificate_actual_upper i hi hq
  have hf := lowMean_certificate_actual_concave i hi q
  by_cases h0 : i = 0
  · subst i
    have hlo := lowMean_curved_actual_positive 0 (by decide) hq
    apply lowMean_concave_positive (hf.subset (Set.subset_univ _) (convex_Icc _ _)) hlo hup
    exact ⟨le_trans (le_max_right _ _) hmu.1, hmu.2⟩
  by_cases h1 : i = 1
  · subst i
    have hlo := lowMean_curved_actual_positive 1 (by decide) hq
    apply lowMean_concave_positive (hf.subset (Set.subset_univ _) (convex_Icc _ _)) hlo hup
    exact ⟨le_trans (le_max_right _ _) hmu.1, hmu.2⟩
  by_cases h23 : i = 23
  · subst i
    have hlo := lowMean_curved_actual_positive 2 (by decide) hq
    apply lowMean_concave_positive (hf.subset (Set.subset_univ _) (convex_Icc _ _)) hlo hup
    exact ⟨le_trans (le_max_right _ _) hmu.1, hmu.2⟩
  have hn1 : i + 1 ≠ 1 := by omega
  have hn2 : i + 1 ≠ 2 := by omega
  have hn24 : i + 1 ≠ 24 := by omega
  have hlo := (lowMean_meanKey_bounds i hi).1
  simp only [lowMeanCertificateLowerValue, hn1, hn2, hn24, ite_false] at hlo
  have hle := lowMean_certificate_rationalMargin_le i hi hq (lowMean_certificate_signs i hi).2.2.2.2.2.2.2.1
  have hpos : 0 < lowMeanCertificateActualMargin (lowMeanCertificateAt i) q (lowMeanFractionReal (lowMeanCertificateAt i).muA) :=
    lt_of_lt_of_le (lt_trans (by norm_num) hlo) hle
  apply lowMean_concave_positive (hf.subset (Set.subset_univ _) (convex_Icc _ _)) hpos hup
  exact ⟨le_trans (le_max_left _ _) hmu.1, hmu.2⟩

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMean_curved_actual_lower

#print axioms Erdos993Lean.Analytic.V213.lowMean_natural_mean_positive
