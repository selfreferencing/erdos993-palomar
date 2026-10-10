module

public import Erdos993Lean.Analytic.V213.LowMeanWidthRoutes

/-!
Complete equation-51 direct-width coverage, strong-seed propagation through
every printed cutoff, and the unpriced tail above it. No seed, slope,
cutoff, finite-window or target equality remains as an end-to-end premise.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

theorem lowMean_coreAt_nodup (i : ℕ) (hi : i < 564) : (lowMeanCoreFiberAt i).core.Nodup := by
  have h := lowMean_coreAt_checked i hi
  simp only [lowMeanFiberCheck, Bool.and_eq_true] at h
  have hm := h.1.1
  simp only [lowMeanFiberMetaCheck, Bool.and_eq_true, decide_eq_true_eq] at hm
  rcases hm.1 with ⟨_, _, _, _, _, _, _, hn⟩
  exact hn

theorem lowMean_direct_set_complete (i : ℕ) (hi : i < 28) (M : ℕ)
    (hM : M ≤ (lowMeanCertificateAt i).T) :
    lowMeanDirectWidth lowMeanWidthPairs (i + 1) M = true ↔
      ∃ k < 564, (lowMeanCoreFiberAt k).certificate = i + 1 ∧ (lowMeanCoreFiberAt k).M = M := by
  constructor
  · intro hd
    have hw := lowMean_widthRoute_checked i hi M hM
    simp only [lowMeanWidthRouteCheck, Bool.and_eq_true, decide_eq_true_eq] at hw
    by_cases hm : (lowMeanWidthRouteAt i M).mode = 0
    · simp only [hm, ite_true, decide_eq_true_eq] at hw
      exact ⟨(lowMeanWidthRouteAt i M).source, hw.1.1, hw.1.2, hw.2.1⟩
    · simp only [hm, ite_false, decide_eq_true_eq] at hw
      have hf := hw.2.2.2.2.2.2.2.2
      rw [hd] at hf
      contradiction
  · rintro ⟨k, hk, hc, hFM⟩
    have hs := lowMean_seedAt_checked k hk
    simp only [lowMeanDirectSeedCheck, Bool.and_eq_true] at hs
    have ht := hs.2
    simp only [lowMeanDirectTargetCheck, Bool.and_eq_true, decide_eq_true_eq] at ht
    simpa only [hc, hFM] using ht.1.1

theorem lowMean_all_width_seeds (i : ℕ) (hi : i < 28) (M : ℕ)
    (hM : M ≤ (lowMeanCertificateAt i).T) {q : ℝ}
    (hq : q ∈ Set.Icc (lowMeanFractionReal (lowMeanCertificateAt i).l)
      (lowMeanFractionReal (lowMeanCertificateAt i).h)) (j : ℤ) :
    (1 / 100000 : ℝ) ≤ lowMeanCertificateSlack (lowMeanCertificateAt i) M j q :=
  lowMean_widthRoute_slack i hi M (lowMeanWidthRouteAt i M) (lowMean_widthRoute_checked i hi M hM) hq j

/-- All 43 closed propagation intervals with their actual closed natural-
mean endpoint transitions, including the curved 4/q lower endpoints. -/
theorem lowMean_all_propagation_intervals (k : ℕ) (hk : k < 43) (M : ℕ)
    (hM : (lowMeanWidthPairAt k).t ≤ M ∧ M ≤ (lowMeanWidthPairAt k).r) {q : ℝ}
    (hq : q ∈ Set.Icc
      (lowMeanFractionReal (lowMeanCertificateAt ((lowMeanWidthPairAt k).certificate - 1)).l)
      (lowMeanFractionReal (lowMeanCertificateAt ((lowMeanWidthPairAt k).certificate - 1)).h)) (j : ℤ) :
    let c := lowMeanCertificateAt ((lowMeanWidthPairAt k).certificate - 1)
    (1 / 100000 : ℝ) ≤ lowMeanCertificateSlack c M j q ∧
      0 < lowMeanCertificateActualMargin c q (max (lowMeanFractionReal c.muA) (4 / q)) ∧
      0 < lowMeanCertificateActualMargin c q (lowMeanFractionReal c.muB) := by
  have hp := lowMean_widthPair_checked k hk
  simp only [lowMeanWidthPairCheck, decide_eq_true_eq] at hp
  exact ⟨lowMean_all_width_seeds _ (by omega) M (le_trans hM.2 hp.2.2.2.2.1) hq j,
    lowMean_widthPair_endpoint_means k hk hq⟩

theorem lowMean_cutoff_certificate (i : ℕ) (hi : i < 28) :
    (1 / 100000 : ℝ) < lowMeanIntegerShapeReal (lowMeanCertificateCutoff (lowMeanCertificateAt i)) := by
  have hk : (lowMeanCutoffAt i).1 = lowMeanCertificateAt i :=
    of_decide_eq_true (Erdos993Lean.F4Fast.forall_lt_of_range_all lowMean_cutoff_certificate_keys i hi)
  simpa only [hk] using lowMean_cutoffs_positive i hi

/-- In particular this uses the propagated T seed for the eleven pairs
ending at T; it never presumes a direct fiber at those endpoints. -/
theorem lowMean_all_unpriced_tail (i : ℕ) (hi : i < 28) (M : ℕ)
    (hM : (lowMeanCertificateAt i).T < M) {q : ℝ}
    (hq : q ∈ Set.Icc (lowMeanFractionReal (lowMeanCertificateAt i).l)
      (lowMeanFractionReal (lowMeanCertificateAt i).h)) (j : ℤ) :
    lowMeanPsi (lowMeanFractionReal (lowMeanCertificateAt i).alpha)
      (lowMeanFractionReal (lowMeanCertificateAt i).beta) (lowMeanFractionReal (lowMeanCertificateAt i).gamma)
      (lowMeanFractionReal (lowMeanCertificateAt i).m0) M + (1 / 100000 : ℝ) ≤
      lowMeanH q (lowMeanFractionReal (lowMeanCertificateAt i).wL)
        (lowMeanFractionReal (lowMeanCertificateAt i).wR) (lowMeanFractionReal (lowMeanCertificateAt i).xi)
        (lowMeanFractionReal (lowMeanCertificateAt i).eta) M j := by
  obtain ⟨hl, hh, _⟩ := lowMean_certificate_interval_facts i hi
  obtain ⟨_, _, heta, hgamma, hz, _⟩ := lowMean_certificate_signs i hi
  have hb := lowMean_cutoff_certificate i hi
  rw [lowMean_certificate_cutoff_real] at hb
  apply lowMean_tail (T := (lowMeanCertificateAt i).T) (l := lowMeanFractionReal (lowMeanCertificateAt i).l)
    (le_trans (le_trans (by norm_num) hl) hq.1) (le_trans hq.2 (le_trans hh (by norm_num)))
    hq.1 heta.le hgamma hz (lowMean_varianceMaximum_bound hq) (le_trans (by norm_num) hb.le) ?_ hM j
  intro a
  have hs := lowMean_all_width_seeds i hi (lowMeanCertificateAt i).T le_rfl hq a
  unfold lowMeanCertificateSlack at hs
  linarith

theorem lowMean_all_width_slack (i : ℕ) (hi : i < 28) (M : ℕ) {q : ℝ}
    (hq : q ∈ Set.Icc (lowMeanFractionReal (lowMeanCertificateAt i).l)
      (lowMeanFractionReal (lowMeanCertificateAt i).h)) (j : ℤ) :
    (1 / 100000 : ℝ) ≤ lowMeanCertificateSlack (lowMeanCertificateAt i) M j q := by
  by_cases hM : M ≤ (lowMeanCertificateAt i).T
  · exact lowMean_all_width_seeds i hi M hM hq j
  · have ht := lowMean_all_unpriced_tail i hi M (Nat.lt_of_not_ge hM) hq j
    have hz := (lowMean_certificate_signs i hi).2.2.2.2.1
    have hh := (lowMean_certificate_interval_facts i hi).2.1
    have hp := mul_nonneg hz (pow_nonneg (by linarith [hq.2] : 0 ≤ 1 - q) M)
    unfold lowMeanCertificateSlack
    linarith

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMean_direct_set_complete
#print axioms Erdos993Lean.Analytic.V213.lowMean_all_width_seeds
#print axioms Erdos993Lean.Analytic.V213.lowMean_all_unpriced_tail
