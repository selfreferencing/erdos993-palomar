module

public import Erdos993Lean.Analytic.V213.LowMeanMeanTransitions

/-!
Sound routes for each width through T: either its own direct fiber or the
stronger left-endpoint seed of a printed pair. Pair endpoints are included.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

structure LowMeanWidthRoute where
  mode : ℕ
  source : ℕ
  pair : ℕ
  deriving DecidableEq

noncomputable def lowMeanWidthRouteCheck (i M : ℕ) (w : LowMeanWidthRoute) : Bool :=
  let f := lowMeanCoreFiberAt w.source
  let p := lowMeanWidthPairAt w.pair
  decide (w.source < 564 ∧ f.certificate = i + 1) &&
  (if w.mode = 0 then decide (f.M = M ∧ lowMeanDirectWidth lowMeanWidthPairs (i + 1) M = true)
   else decide (w.mode = 1 ∧ w.pair < 43 ∧ p.certificate = i + 1 ∧ f.M = p.t ∧
     (lowMeanSeedAt w.source).target.R = p.r ∧ p.t ≤ M ∧ M ≤ p.r ∧
     lowMeanDirectWidth lowMeanWidthPairs (i + 1) M = false))

theorem lowMean_widthRoute_slack (i : ℕ) (hi : i < 28) (M : ℕ) (w : LowMeanWidthRoute)
    (hw : lowMeanWidthRouteCheck i M w = true) {q : ℝ}
    (hq : q ∈ Set.Icc (lowMeanFractionReal (lowMeanCertificateAt i).l)
      (lowMeanFractionReal (lowMeanCertificateAt i).h)) (j : ℤ) :
    (1 / 100000 : ℝ) ≤ lowMeanCertificateSlack (lowMeanCertificateAt i) M j q := by
  simp only [lowMeanWidthRouteCheck, Bool.and_eq_true, decide_eq_true_eq] at hw
  have hsource : w.source < 564 := hw.1.1
  have hcf : lowMeanFiberCertificate (lowMeanCoreFiberAt w.source) = lowMeanCertificateAt i := by
    simp only [lowMeanFiberCertificate, hw.1.2, Nat.add_sub_cancel]
  have hqf : q ∈ Set.Icc (lowMeanFractionReal (lowMeanFiberCertificate (lowMeanCoreFiberAt w.source)).l)
      (lowMeanFractionReal (lowMeanFiberCertificate (lowMeanCoreFiberAt w.source)).h) := by
    simpa only [hcf] using hq
  by_cases hmode : w.mode = 0
  · simp only [hmode, ite_true, decide_eq_true_eq] at hw
    have hs := lowMean_all_direct_epsilon w.source hsource hqf j
    simpa only [hcf, hw.2.1] using hs
  · simp only [hmode, ite_false, decide_eq_true_eq] at hw
    rcases hw.2 with ⟨_, hpair, hpc, hft, hR, htm, hmr, _⟩
    have hp := lowMean_widthPair_checked w.pair hpair
    have hcond := lowMean_widthPair_conditions (lowMeanWidthPairAt w.pair) hp
    simp only [hpc, Nat.add_sub_cancel] at hcond
    have htr : (lowMeanWidthPairAt w.pair).t < (lowMeanWidthPairAt w.pair).r := by
      simp only [lowMeanWidthPairCheck, decide_eq_true_eq] at hp
      exact hp.2.2.2.1
    apply lowMean_certificate_strongSeed i hi hq htr hcond.1 hcond.2 ?_ htm hmr j
    intro a
    have hs := lowMean_directSeed_strong lowMeanWidthPairs (lowMeanCoreFiberAt w.source)
      (lowMeanSeedAt w.source) (lowMean_coreAt_checked w.source hsource)
      (lowMean_seedAt_checked w.source hsource) hqf a
    simpa only [hcf, hft, hR] using hs

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMean_widthRoute_slack
