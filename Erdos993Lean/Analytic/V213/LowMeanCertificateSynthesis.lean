module

public import Erdos993Lean.Analytic.V213.LowMeanPrintedSeeds
public import Erdos993Lean.Analytic.V213.LowMeanNaturalMean
public import Erdos993Lean.Analytic.V213.LowMeanSynthesis

/-!
Concrete reviewed low-mean certificates: all scalar, seed and mean premises
are discharged. Only the actual probability mixture's moment conditions
remain. Their forest identifications are made in a later module.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

theorem lowMean_certificate_noValley (i : ℕ) (hi : i < 28)
    {ι : Type} (X : Mixture ι) (k : ℤ) {q mu : ℝ}
    (hq : q ∈ Set.Icc (lowMeanFractionReal (lowMeanCertificateAt i).l)
      (lowMeanFractionReal (lowMeanCertificateAt i).h))
    (hmu : mu ∈ Set.Icc (max (lowMeanFractionReal (lowMeanCertificateAt i).muA) (4 / q))
      (lowMeanFractionReal (lowMeanCertificateAt i).muB))
    (hX : X.IsProb) (hmean : X.meanM = mu)
    (hdelta : X.expect (fun M Y => delta q k M Y) = 0)
    (hvar : X.varM ≤ lowMeanFractionReal (lowMeanCertificateAt i).D * mu)
    (hdelta2 : X.expect (fun M Y => delta q k M Y ^ 2) ≤
      lowMeanFractionReal (lowMeanCertificateAt i).theta * (q * (1 - q)) * mu)
    (htail : X.expect (fun M _ => (1 - q) ^ M) ≤ Real.exp (-lowMeanRate q * mu)) :
    ¬ X.WeakValley q k := by
  obtain ⟨hl, hh, _⟩ := lowMean_certificate_interval_facts i hi
  obtain ⟨hwL, hwR, heta, hgamma, hz, _⟩ := lowMean_certificate_signs i hi
  have hb := lowMean_cutoff_certificate i hi
  rw [lowMean_certificate_cutoff_real] at hb
  apply lowMean_noValley X k (lowMeanCertificateAt i).T
    (alpha := lowMeanFractionReal (lowMeanCertificateAt i).alpha)
    (xi := lowMeanFractionReal (lowMeanCertificateAt i).xi)
    (lt_of_lt_of_le (lt_of_lt_of_le (by norm_num) hl) hq.1)
    (lt_of_le_of_lt (le_trans hq.2 hh) (by norm_num)) hq.1
    heta hgamma hwL hwR hz (lowMean_varianceMaximum_bound hq) (le_trans (by norm_num) hb.le)
    ?_ ?_ hX hmean hdelta hvar hdelta2 htail
  · intro M hM j
    exact le_trans (by norm_num : (0 : ℝ) ≤ 1 / 100000) (lowMean_all_width_seeds i hi M hM hq j)
  · simpa only [lowMeanCertificateActualMargin, lowMeanMargin, mul_assoc] using
      lowMean_natural_mean_positive i hi hq hmu

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMean_certificate_noValley
