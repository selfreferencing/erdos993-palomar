module

public import Erdos993Lean.Analytic.V213.LowMeanGroupRate
public import Erdos993Lean.Analytic.V213.LowMeanCertificateSynthesis

/-! Printed Theorem 6.2 with the exact group maxima and actual ell_H rate.
All numerical seed, cutoff and natural-domain mean obligations are discharged.
Only the printed probability-mixture moment/tail hypotheses are retained. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

theorem lowMean_group_margin_positive (k i : ℕ) (hk : k < 11)
    (hi : (lowMeanGroupAt k).certLo ≤ i ∧ i ≤ (lowMeanGroupAt k).certHi) {q mu : ℝ}
    (hq : q ∈ Set.Icc (lowMeanFractionReal (lowMeanGroupAt k).l)
      (lowMeanFractionReal (lowMeanGroupAt k).h))
    (hmu : mu ∈ Set.Icc (max (lowMeanFractionReal (lowMeanCertificateAt i).muA) (4 / q))
      (lowMeanFractionReal (lowMeanCertificateAt i).muB)) :
    lowMeanPsi (lowMeanFractionReal (lowMeanCertificateAt i).alpha)
      (lowMeanFractionReal (lowMeanCertificateAt i).beta)
      (lowMeanFractionReal (lowMeanCertificateAt i).gamma)
      (lowMeanFractionReal (lowMeanCertificateAt i).m0) mu -
      lowMeanFractionReal (lowMeanCertificateAt i).gamma * lowMeanGroupDbar k * mu -
      lowMeanFractionReal (lowMeanCertificateAt i).eta * lowMeanGroupThetaBar k *
        (q * (1 - q)) * mu -
      lowMeanFractionReal (lowMeanCertificateAt i).z *
        Real.exp (-ZeroTiltLaplace.ellH (q / (1 - q)) * mu) > 0 := by
  have hc := lowMean_group_certificate_fields k i hk hi
  have hqc : q ∈ Set.Icc (lowMeanFractionReal (lowMeanCertificateAt i).l)
      (lowMeanFractionReal (lowMeanCertificateAt i).h) := by
    simpa only [hc.2.1, hc.2.2.1] using hq
  have hq1 : q < 1 := lt_of_le_of_lt hqc.2
    (lt_of_le_of_lt (lowMean_certificate_interval_facts i hc.1).2.1 (by norm_num))
  have h := lowMean_natural_mean_positive i hc.1 hqc hmu
  simpa only [lowMeanCertificateActualMargin, lowMeanMargin, lowMean_group_Dbar_value k hk,
    lowMean_group_thetaBar_value k hk, hc.2.2.2.1, hc.2.2.2.2.1,
    lowMean_rate_eq_ellH hq1, mul_assoc] using h

/-- Literal low-mean synthesis: Dbar and thetaBar are actual finite maxima,
ell is actual ell_H(q/(1-q)), and every numerical premise is proved. -/
theorem lowMean_synthesis_natural_domain (k i : ℕ) (hk : k < 11)
    (hi : (lowMeanGroupAt k).certLo ≤ i ∧ i ≤ (lowMeanGroupAt k).certHi)
    {σ : Type} (X : Mixture σ) (j : ℤ) {q mu : ℝ}
    (hq : q ∈ Set.Icc (lowMeanFractionReal (lowMeanGroupAt k).l)
      (lowMeanFractionReal (lowMeanGroupAt k).h))
    (hmu : mu ∈ Set.Icc (max (lowMeanFractionReal (lowMeanCertificateAt i).muA) (4 / q))
      (lowMeanFractionReal (lowMeanCertificateAt i).muB))
    (hX : X.IsProb) (hmean : X.meanM = mu)
    (hdelta : X.expect (fun M Y => delta q j M Y) = 0)
    (hvar : X.varM ≤ lowMeanGroupDbar k * mu)
    (hdelta2 : X.expect (fun M Y => delta q j M Y ^ 2) ≤
      lowMeanGroupThetaBar k * (q * (1 - q)) * mu)
    (htail : X.expect (fun M _ => (1 - q) ^ M) ≤
      Real.exp (-ZeroTiltLaplace.ellH (q / (1 - q)) * mu)) : ¬ X.WeakValley q j := by
  have hc := lowMean_group_certificate_fields k i hk hi
  have hqc : q ∈ Set.Icc (lowMeanFractionReal (lowMeanCertificateAt i).l)
      (lowMeanFractionReal (lowMeanCertificateAt i).h) := by
    simpa only [hc.2.1, hc.2.2.1] using hq
  have hq1 : q < 1 := lt_of_le_of_lt hqc.2
    (lt_of_le_of_lt (lowMean_certificate_interval_facts i hc.1).2.1 (by norm_num))
  apply lowMean_certificate_noValley i hc.1 X j hqc hmu hX hmean hdelta
  · simpa only [lowMean_group_Dbar_value k hk, hc.2.2.2.1] using hvar
  · simpa only [lowMean_group_thetaBar_value k hk, hc.2.2.2.2.1] using hdelta2
  · simpa only [lowMean_rate_eq_ellH hq1] using htail

/-- Combining exact coverage and synthesis on each actual closed input. -/
theorem lowMean_input_noValley (i : ℕ) (hi : i < 55)
    {σ : Type} (X : Mixture σ) (j : ℤ) {lam mu : ℝ}
    (hlam : lam ∈ Set.Icc (Erdos993Lean.Analytic.N44.Data.pieceLo.getD i 0 : ℝ)
      (Erdos993Lean.Analytic.N44.Data.pieceHi.getD i 0 : ℝ))
    (hmu : mu ∈ Set.Icc (4 / FreeCountVariance.q lam)
      (lowMeanFractionReal (lowMeanInputRowAt i).mu0))
    (hX : X.IsProb) (hmean : X.meanM = mu)
    (hdelta : X.expect (fun M Y => delta (FreeCountVariance.q lam) j M Y) = 0)
    (hvar : X.varM ≤ lowMeanFractionReal (lowMeanInputRowAt i).D * mu)
    (hdelta2 : X.expect (fun M Y => delta (FreeCountVariance.q lam) j M Y ^ 2) ≤
      lowMeanFractionReal (lowMeanInputRowAt i).theta *
        (FreeCountVariance.q lam * (1 - FreeCountVariance.q lam)) * mu)
    (htail : X.expect (fun M _ => (1 - FreeCountVariance.q lam) ^ M) ≤
      Real.exp (-ZeroTiltLaplace.ellH lam * mu)) : ¬ X.WeakValley (FreeCountVariance.q lam) j := by
  obtain ⟨c, hc, hcg, hq, _, hm⟩ := lowMean_coverage_activity i hi hlam hmu
  let k := (lowMeanInputRowAt i).group
  have hcaps := lowMean_input_real_caps i hi
  have hcf := lowMean_certificate_group_checked c hc
  simp only [lowMeanCertificateGroupFacts, hcg] at hcf
  have hq0 : 0 < FreeCountVariance.q lam := by
    apply FreeCountVariance.q_pos
    linarith [(lowMean_n44_endpoint_facts i hi).1, hlam.1]
  have hmnonneg : 0 ≤ mu :=
    le_trans (div_nonneg (by norm_num) hq0.le) hmu.1
  have hq1 : FreeCountVariance.q lam < 1 := FreeCountVariance.q_lt_one (by
    linarith [(lowMean_n44_endpoint_facts i hi).1, hlam.1])
  apply lowMean_synthesis_natural_domain k c hcaps.1 ⟨hcf.2.1, hcf.2.2.1⟩ X j
    (lowMean_input_probability_group i hi hlam) hm hX hmean hdelta
  · rw [lowMean_group_Dbar_value k hcaps.1]
    exact le_trans hvar (mul_le_mul_of_nonneg_right hcaps.2.1 hmnonneg)
  · rw [lowMean_group_thetaBar_value k hcaps.1]
    apply le_trans hdelta2
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hcaps.2.2.1
      (mul_nonneg (mul_nonneg hq0.le (by linarith)) hmnonneg)
  · rw [← lowMean_rate_eq_ellH hq1, lowMean_rate_eq_ellH_activity lam]
    exact htail


/-- The strict printed cutoff comparison uses the actual maximum v_Q. -/
theorem lowMean_group_cutoff (k i : ℕ) (hk : k < 11)
    (hi : (lowMeanGroupAt k).certLo ≤ i ∧ i ≤ (lowMeanGroupAt k).certHi) :
    let c := lowMeanCertificateAt i
    (1 / 100000 : ℝ) < 2 * lowMeanFractionReal c.gamma * ((c.T : ℝ) - lowMeanFractionReal c.m0) +
      lowMeanFractionReal c.gamma - lowMeanFractionReal c.beta -
      lowMeanFractionReal c.eta * lowMeanGroupVQ k -
      lowMeanFractionReal c.z * (1 - lowMeanFractionReal c.l) ^ c.T := by
  have hc := lowMean_group_certificate_fields k i hk hi
  have h := lowMean_cutoff_certificate i hc.1
  rw [lowMean_certificate_cutoff_real] at h
  simpa only [lowMeanGroupVQ, hc.2.1, hc.2.2.1] using h

end Erdos993Lean.Analytic.V213
