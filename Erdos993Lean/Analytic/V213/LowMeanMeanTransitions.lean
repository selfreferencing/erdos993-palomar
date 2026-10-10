module

public import Erdos993Lean.Analytic.V213.LowMeanSeedAssertions
public import Erdos993Lean.Analytic.V213.LowMeanNaturalMean

/-!
Closed natural-mean endpoints for all certificates and each of the 43
propagation intervals. Curved lower endpoints use the actual 4/q value.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

def lowMeanNaturalEndpointsCheck (i : ℕ) : Bool :=
  let c := lowMeanCertificateAt i
  decide (lowMeanFractionLE c.muA c.muB ∧
    lowMeanFractionLE (4, 1) (lowMeanFractionMul c.muB c.l))

theorem lowMean_naturalEndpoints_kernel : (List.range 28).all lowMeanNaturalEndpointsCheck = true := by
  decide +kernel

theorem lowMean_naturalEndpoints_order (i : ℕ) (hi : i < 28) {q : ℝ}
    (hq : q ∈ Set.Icc (lowMeanFractionReal (lowMeanCertificateAt i).l)
      (lowMeanFractionReal (lowMeanCertificateAt i).h)) :
    max (lowMeanFractionReal (lowMeanCertificateAt i).muA) (4 / q) ≤
      lowMeanFractionReal (lowMeanCertificateAt i).muB := by
  have h := Erdos993Lean.F4Fast.forall_lt_of_range_all lowMean_naturalEndpoints_kernel i hi
  simp only [lowMeanNaturalEndpointsCheck, decide_eq_true_eq] at h
  have hv (f : lowMeanFraction) (hf : f ∈ lowMeanCertificateFractions (lowMeanCertificateAt i)) :=
    lowMean_certificate_fraction_valid i hi f hf
  have hlv := hv (lowMeanCertificateAt i).l (by simp [lowMeanCertificateFractions])
  have hav := hv (lowMeanCertificateAt i).muA (by simp [lowMeanCertificateFractions])
  have hbv := hv (lowMeanCertificateAt i).muB (by simp [lowMeanCertificateFractions])
  have hprod : lowMeanFractionValid (lowMeanFractionMul (lowMeanCertificateAt i).muB (lowMeanCertificateAt i).l) := Nat.mul_pos hbv hlv
  have hb := (lowMean_fraction_le_iff (x := (4, 1)) (by decide) hprod).mp h.2
  rw [lowMean_fraction_mul] at hb
  have hl : 0 < lowMeanFractionReal (lowMeanCertificateAt i).l :=
    lt_of_lt_of_le (by norm_num) (lowMean_certificate_interval_facts i hi).1
  apply max_le ((lowMean_fraction_le_iff hav hbv).mp h.1)
  apply le_trans (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 4) hl hq.1)
  apply (div_le_iff₀ hl).mpr
  simpa [lowMeanFractionReal] using hb

theorem lowMean_certificate_endpoint_means (i : ℕ) (hi : i < 28) {q : ℝ}
    (hq : q ∈ Set.Icc (lowMeanFractionReal (lowMeanCertificateAt i).l)
      (lowMeanFractionReal (lowMeanCertificateAt i).h)) :
    0 < lowMeanCertificateActualMargin (lowMeanCertificateAt i) q
      (max (lowMeanFractionReal (lowMeanCertificateAt i).muA) (4 / q)) ∧
    0 < lowMeanCertificateActualMargin (lowMeanCertificateAt i) q
      (lowMeanFractionReal (lowMeanCertificateAt i).muB) := by
  have ho := lowMean_naturalEndpoints_order i hi hq
  exact ⟨lowMean_natural_mean_positive i hi hq ⟨le_rfl, ho⟩,
    lowMean_natural_mean_positive i hi hq ⟨ho, le_rfl⟩⟩

theorem lowMean_widthPair_endpoint_means (k : ℕ) (hk : k < 43) {q : ℝ}
    (hq : q ∈ Set.Icc
      (lowMeanFractionReal (lowMeanCertificateAt ((lowMeanWidthPairAt k).certificate - 1)).l)
      (lowMeanFractionReal (lowMeanCertificateAt ((lowMeanWidthPairAt k).certificate - 1)).h)) :
    let c := lowMeanCertificateAt ((lowMeanWidthPairAt k).certificate - 1)
    0 < lowMeanCertificateActualMargin c q (max (lowMeanFractionReal c.muA) (4 / q)) ∧
      0 < lowMeanCertificateActualMargin c q (lowMeanFractionReal c.muB) := by
  have hp := lowMean_widthPair_checked k hk
  simp only [lowMeanWidthPairCheck, decide_eq_true_eq] at hp
  exact lowMean_certificate_endpoint_means _ (by omega) hq

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMean_widthPair_endpoint_means
