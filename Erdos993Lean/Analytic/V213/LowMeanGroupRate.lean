module

public import Erdos993Lean.Analytic.V213.LowMeanGroupMaximum

/-! Actual equation-31 rate and the group parameters used by printed Theorem 6.2. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

theorem lowMean_probability_inverse {q : ℝ} (hq : q < 1) :
    ZeroTiltLaplace.q (q / (1 - q)) = q := by
  have hd : 1 - q ≠ 0 := by linarith
  unfold ZeroTiltLaplace.q
  field_simp [hd] <;> ring

/-- This includes the actual high branch at q=3/7. -/
theorem lowMean_rate_eq_ellH {q : ℝ} (hq : q < 1) :
    lowMeanRate q = ZeroTiltLaplace.ellH (q / (1 - q)) := by
  unfold ZeroTiltLaplace.ellH
  rw [lowMean_probability_inverse hq]
  rfl

theorem lowMean_rate_eq_ellH_activity (lam : ℝ) :
    lowMeanRate (FreeCountVariance.q lam) = ZeroTiltLaplace.ellH lam := by
  rfl

theorem lowMean_Dhat_monotone : Monotone FreeCountVariance.Dhat := by
  intro a b hab
  unfold FreeCountVariance.Dhat FreeCountVariance.selectedCap
  split_ifs <;> norm_num [FreeCountVariance.Cap.value] at * <;> linarith

/-- The printed D(iota) is exactly max Dhat on the actual full closed input. -/
theorem lowMean_input_Dhat_maximum (i : ℕ) (hi : i < 55) :
    IsGreatest (FreeCountVariance.Dhat '' Set.Icc
      (Erdos993Lean.Analytic.N44.Data.pieceLo.getD i 0 : ℝ)
      (Erdos993Lean.Analytic.N44.Data.pieceHi.getD i 0 : ℝ))
      (lowMeanFractionReal (lowMeanInputRowAt i).D) := by
  have h := lowMean_n44_endpoint_facts i hi
  refine ⟨⟨(Erdos993Lean.Analytic.N44.Data.pieceHi.getD i 0 : ℝ),
    ⟨h.2.2.1.le, le_rfl⟩, h.2.2.2.2.2.1⟩, ?_⟩
  intro y hy
  obtain ⟨lam, hlam, rfl⟩ := hy
  rw [← h.2.2.2.2.2.1]
  exact lowMean_Dhat_monotone hlam.2

theorem lowMean_input_Dhat_bound (i : ℕ) (hi : i < 55) {lam : ℝ}
    (hlam : lam ∈ Set.Icc (Erdos993Lean.Analytic.N44.Data.pieceLo.getD i 0 : ℝ)
      (Erdos993Lean.Analytic.N44.Data.pieceHi.getD i 0 : ℝ)) :
    FreeCountVariance.Dhat lam ≤ lowMeanFractionReal (lowMeanInputRowAt i).D := by
  exact (lowMean_input_Dhat_maximum i hi).2 ⟨lam, hlam, rfl⟩


noncomputable def lowMeanGroupEllK (k : ℕ) : ℝ :=
  min (ZeroTiltLaplace.ellH (lowMeanFractionReal (lowMeanGroupAt k).l /
        (1 - lowMeanFractionReal (lowMeanGroupAt k).l)))
    (ZeroTiltLaplace.ellH (lowMeanFractionReal (lowMeanGroupAt k).h /
        (1 - lowMeanFractionReal (lowMeanGroupAt k).h)))

/-- The exact group endpoint rate floor is below the actual rate on all of Q. -/
theorem lowMean_group_ellK_le_ell (k : ℕ) (hk : k < 11) {q : ℝ}
    (hq : q ∈ Set.Icc (lowMeanFractionReal (lowMeanGroupAt k).l)
      (lowMeanFractionReal (lowMeanGroupAt k).h)) :
    lowMeanGroupEllK k ≤ ZeroTiltLaplace.ellH (q / (1 - q)) := by
  have hb := lowMean_group_bounds k hk
  have hc := lowMean_group_certificate_fields k (lowMeanGroupAt k).certLo hk ⟨le_rfl, hb.2.2.1⟩
  have hqc : q ∈ Set.Icc (lowMeanFractionReal (lowMeanCertificateAt (lowMeanGroupAt k).certLo).l)
      (lowMeanFractionReal (lowMeanCertificateAt (lowMeanGroupAt k).certLo).h) := by
    simpa only [hc.2.1, hc.2.2.1] using hq
  have h := lowMean_all_certificate_rateFloors _ hc.1 hqc
  rw [lowMean_certificate_rateFloor_real, hc.2.1, hc.2.2.1] at h
  have hg := lowMean_group_real_facts k hk
  have hhi := hg.2.2.2.2.2.2.2.1
  have hlo : lowMeanFractionReal (lowMeanGroupAt k).l < 1 := by
    exact lt_of_le_of_lt (le_trans hq.1 hq.2) hhi
  simpa only [lowMeanGroupEllK, lowMean_rate_eq_ellH hlo,
    lowMean_rate_eq_ellH hhi, lowMean_rate_eq_ellH (lt_of_le_of_lt hq.2 hhi)] using h

end Erdos993Lean.Analytic.V213
