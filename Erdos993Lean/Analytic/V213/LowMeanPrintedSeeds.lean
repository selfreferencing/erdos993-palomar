module

public import Erdos993Lean.Analytic.V213.LowMeanWidthComposition
public import Erdos993Lean.Analytic.V213.LowMeanSeedAssertions

/-!
Printed direct seeds and cores, quantified by certificate and actual width
in equation-51's direct set. The exported index is obtained from proved
coverage; the target is the printed potential difference, not a premise.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanPrintedTarget (i M : ℕ) : ℝ :=
  (1 / 100000 : ℝ) + lowMeanCertificatePotential (lowMeanCertificateAt i)
    (lowMeanDirectTargetR lowMeanWidthPairs (i + 1) M) -
    lowMeanCertificatePotential (lowMeanCertificateAt i) M

noncomputable def lowMeanPrintedCore (i M : ℕ) : Set ℤ :=
  let c := lowMeanCertificateAt i
  lowMeanCore M (lowMeanFractionReal c.wL) (lowMeanFractionReal c.wR) (lowMeanFractionReal c.xi)
    (lowMeanFractionReal c.eta) (lowMeanFractionReal c.alpha) (lowMeanFractionReal c.beta)
    (lowMeanFractionReal c.gamma) (lowMeanFractionReal c.m0) (lowMeanFractionReal c.z)
    (lowMeanPrintedTarget i M) (lowMeanFractionReal c.l) (lowMeanFractionReal c.h)

theorem lowMean_printed_direct_seed (i : ℕ) (hi : i < 28) (M : ℕ)
    (hdirect : lowMeanDirectWidth lowMeanWidthPairs (i + 1) M = true) {q : ℝ}
    (hq : q ∈ Set.Icc (lowMeanFractionReal (lowMeanCertificateAt i).l)
      (lowMeanFractionReal (lowMeanCertificateAt i).h)) (j : ℤ) :
    lowMeanPrintedTarget i M ≤ lowMeanCertificateSlack (lowMeanCertificateAt i) M j q := by
  have hd := hdirect
  simp only [lowMeanDirectWidth, Bool.and_eq_true, decide_eq_true_eq] at hd
  have hM : M ≤ (lowMeanCertificateAt i).T := by simpa only [Nat.add_sub_cancel] using hd.1
  obtain ⟨k, hk, hc, hFM⟩ := (lowMean_direct_set_complete i hi M hM).mp hdirect
  have hcf : lowMeanFiberCertificate (lowMeanCoreFiberAt k) = lowMeanCertificateAt i := by
    simp only [lowMeanFiberCertificate, hc, Nat.add_sub_cancel]
  have hqf : q ∈ Set.Icc (lowMeanFractionReal (lowMeanFiberCertificate (lowMeanCoreFiberAt k)).l)
      (lowMeanFractionReal (lowMeanFiberCertificate (lowMeanCoreFiberAt k)).h) := by simpa only [hcf] using hq
  have hs := lowMean_all_direct_seeds k hk hqf j
  rw [lowMean_all_direct_target_exact k hk] at hs
  simpa only [hcf, hc, hFM, lowMeanPrintedTarget] using hs

theorem lowMean_coreAt_printed (i M k : ℕ) (hk : k < 564)
    (hc : (lowMeanCoreFiberAt k).certificate = i + 1) (hM : (lowMeanCoreFiberAt k).M = M) :
    lowMeanFiberCore (lowMeanCoreFiberAt k) = lowMeanPrintedCore i M := by
  have ht := lowMean_all_direct_target_exact k hk
  unfold lowMeanFiberCore lowMeanPrintedCore
  rw [ht]
  simp only [lowMeanFiberCertificate, hc, hM, Nat.add_sub_cancel, lowMeanPrintedTarget]

theorem lowMean_printed_core_position (i : ℕ) (hi : i < 28) (M : ℕ)
    (hdirect : lowMeanDirectWidth lowMeanWidthPairs (i + 1) M = true) (j : ℤ)
    (hj : j ∈ lowMeanPrintedCore i M) :
    ∃ k < 564, (lowMeanCoreFiberAt k).certificate = i + 1 ∧ (lowMeanCoreFiberAt k).M = M ∧
      ∃ w ∈ (lowMeanSeedAt k).positions, w.j = j := by
  have hd := hdirect
  simp only [lowMeanDirectWidth, Bool.and_eq_true, decide_eq_true_eq] at hd
  have hM : M ≤ (lowMeanCertificateAt i).T := by simpa only [Nat.add_sub_cancel] using hd.1
  obtain ⟨k, hk, hc, hFM⟩ := (lowMean_direct_set_complete i hi M hM).mp hdirect
  refine ⟨k, hk, hc, hFM, lowMean_core_position_choice k hk j ?_⟩
  apply (lowMean_coreAt_exact k hk j).mp
  simpa only [lowMean_coreAt_printed i M k hk hc hFM] using hj

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMean_printed_direct_seed
#print axioms Erdos993Lean.Analytic.V213.lowMean_printed_core_position
