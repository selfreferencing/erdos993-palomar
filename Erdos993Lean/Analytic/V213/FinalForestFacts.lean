module

public import Erdos993Lean.Analytic.HardCore.Mixture
public import Erdos993Lean.Analytic.Translate
public import Erdos993Lean.Analytic.V213.Foundation
public import Erdos993Lean.Analytic.V213.FreeCountVarianceDefs

/-! The forest inputs to Lemma 2.5 of version 2.13 of the manuscript and equation (2.3).
The maximum marginal weight set is chosen separately at each activity.
No pending input or numerical certificate is used in these bridges. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Finset

/-- A forest's two color classes bound the total marginal weight. -/
theorem hardCoreMean_le_two_weightW (F : FiniteForest) (lam : ℝ)
    (A : Finset (Fin F.n)) (hA : IsMaxWeight F lam A) :
    hardCoreMean F lam ≤ 2 * weightW F lam A := by
  classical
  obtain ⟨c⟩ := F.isForest.isBipartite
  let B : Finset (Fin F.n) := univ.filter (fun v => c v = 0)
  have hB : F.graph.IsIndepSet (B : Set (Fin F.n)) := by
    intro v hv w hw _ hvw
    have hv0 : c v = 0 := (mem_filter.mp hv).2
    have hw0 : c w = 0 := (mem_filter.mp hw).2
    exact c.valid hvw (hv0.trans hw0.symm)
  have hC : F.graph.IsIndepSet ((Bᶜ : Finset (Fin F.n)) : Set (Fin F.n)) := by
    intro v hv w hw _ hvw
    have hv0 : c v ≠ 0 := by simpa [B] using hv
    have hw0 : c w ≠ 0 := by simpa [B] using hw
    have hv1 : c v = 1 := by omega
    have hw1 : c w = 1 := by omega
    exact c.valid hvw (hv1.trans hw1.symm)
  have hsum : weightW F lam B + weightW F lam Bᶜ = hardCoreMean F lam := by
    simp only [weightW]
    rw [sum_add_sum_compl, HardCore.sum_univ_marginal]
  have hb := hA.2 B hB
  have hc := hA.2 Bᶜ hC
  linarith

/-- Lemma 2.5 of version 2.13 of the manuscript, lower-edge conclusion on the natural-rank window.
The upper window and activity bounds are retained to match the requested interface. -/
theorem lemma25_lower_edge (F : FiniteForest) (hn : 25 ≤ F.n) (k : ℕ)
    (hklo : (F.n + 3) / 4 < k) (_hkhi : k < hB F) {lam : ℝ}
    (hlamlo : 1 / 3 < lam) (_hlamhi : lam < 7 / 3)
    (hmean : hardCoreMean F lam = k) (A : Finset (Fin F.n))
    (hA : IsMaxWeight F lam A) :
    8 ≤ k ∧ 4 / FreeCountVariance.q lam ≤ (forestMixture F A lam).meanM := by
  have hk : 8 ≤ k := by omega
  refine ⟨hk, ?_⟩
  have hlam : 0 < lam := by linarith
  have hq : 0 < FreeCountVariance.q lam := FreeCountVariance.q_pos hlam
  apply (div_le_iff₀ hq).mpr
  have hw := hardCoreMean_le_two_weightW F lam A hA
  have he := HardCore.forestMixture_weight_eq F hA.1 hlam
  have hkr : (8 : ℝ) ≤ k := by exact_mod_cast hk
  change actQ lam * (forestMixture F A lam).meanM = weightW F lam A at he
  change 4 ≤ (forestMixture F A lam).meanM * actQ lam
  rw [hmean] at hw
  nlinarith [he]

/-- Equation (2.3), with the q spelling consumed by the final assembly. -/
theorem forest_equation23 (F : FiniteForest) (A : Finset (Fin F.n)) {lam : ℝ}
    (hlam : 0 < lam) (hA : IsMaxWeight F lam A) (k : ℕ)
    (hk : hardCoreMean F lam = k) :
    (forestMixture F A lam).expect (fun M Y => delta (FreeCountVariance.q lam) k M Y) = 0 ∧
    (forestMixture F A lam).expect (fun M Y => delta (FreeCountVariance.q lam) k M Y ^ 2) =
      hardCoreVar F lam - FreeCountVariance.q lam * (1 - FreeCountVariance.q lam) *
        (forestMixture F A lam).meanM ∧
    FreeCountVariance.q lam * (forestMixture F A lam).meanM = weightW F lam A := by
  exact ⟨HardCore.forestMixture_mean_delta F hA.1 hlam k hk,
    HardCore.forestMixture_var_delta F hA.1 hlam k hk,
    HardCore.forestMixture_weight_eq F hA.1 hlam⟩

/-- A coefficient valley at a natural positive rank transfers to the forest mixture. -/
theorem forest_valley_transfer (F : FiniteForest) (A : Finset (Fin F.n)) {lam : ℝ}
    (hlam : 0 < lam) (hA : IsMaxWeight F lam A) (k : ℕ)
    (hv : CoefficientValley F k) :
    (forestMixture F A lam).WeakValley (FreeCountVariance.q lam) k := by
  have hk : 1 ≤ k := by exact_mod_cast hv.1
  have hp : (k : ℤ) - 1 = ((k - 1 : ℕ) : ℤ) := by omega
  have hs : (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) := by omega
  have hprev : independenceCount F k ≤ independenceCount F (k - 1) := by
    simpa only [hp, coefficient_nat] using hv.2.1
  have hnext : independenceCount F k ≤ independenceCount F (k + 1) := by
    simpa only [hs, coefficient_nat] using hv.2.2
  exact weakValley_of_le (forestMixture F A lam) hlam (HardCore.partitionFn_pos F hlam.le)
    (fun j => (independenceCount F j : ℝ)) hk
    (HardCore.forestMixture_prob_eq F hA.1 hlam (k - 1))
    (HardCore.forestMixture_prob_eq F hA.1 hlam k)
    (HardCore.forestMixture_prob_eq F hA.1 hlam (k + 1))
    (by exact_mod_cast hprev) (by exact_mod_cast hnext)

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.hardCoreMean_le_two_weightW
#print axioms Erdos993Lean.Analytic.V213.lemma25_lower_edge
#print axioms Erdos993Lean.Analytic.V213.forest_equation23
#print axioms Erdos993Lean.Analytic.V213.forest_valley_transfer
