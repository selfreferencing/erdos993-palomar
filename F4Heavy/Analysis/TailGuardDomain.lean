module

public import F4Heavy.Analysis.TailThresholdBounds
public import F4Heavy.Analysis.TailParentMass
public import F4Heavy.Analysis.TailZeroEndpoint

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem tail_threshold_lower_of_guard (r : Row) (lam : ℝ) (hr : InRow r lam)
    (h2 : 0 < tailGuard r lam 2) : 3 / 2 < tailTau r lam := by
  have hb := (tail_threshold_bounds r lam hr).1
  change 0 < tailTauLo r lam - 3 / 2 at h2
  linarith only [h2, hb]

theorem tail_probability_mass_bound_of_guards (r : Row) (lam Y : ℝ) (hr : InRow r lam)
    (h1 : 0 < tailGuard r lam 1) (h2 : 0 < tailGuard r lam 2)
    (hY : tailTau r lam ≤ Y) : p lam Y * Y ≤ tailPStar r lam * tailTauHi r lam := by
  apply tail_probability_mass_bound r lam Y (inRow_activity_pos r lam hr)
    (tail_threshold_lower_of_guard r lam hr h2).le (tail_threshold_bounds r lam hr).2 _ hY
  change 0 < 1 / 6 - tailPStar r lam at h1
  linarith only [h1]

theorem tail_zero_endpoint_positive_of_guards (r : Row) (lam Y u y : ℝ)
    (hr : InRow r lam) (hY : tailTau r lam ≤ Y)
    (hguards : ∀ i, 1 ≤ i → i ≤ 5 → 0 < tailGuard r lam i)
    (hJ : 0 < childJ lam u) : 0 < tailEndpointZero r lam Y u y := by
  have ht := tail_threshold_lower_of_guard r lam hr (hguards 2 (by omega) (by omega))
  have hpstar : p lam Y ≤ tailPStar r lam := by
    rw [← tail_probability_at_threshold r lam (inRow_activity_pos r lam hr)]
    exact tail_probability_antitone lam (tailTau r lam) Y (inRow_activity_pos r lam hr) hY
  exact tail_zero_endpoint_positive_of_bounds r lam Y u y hr (by linarith only [ht, hY]) hpstar
    (tail_probability_mass_bound_of_guards r lam Y hr (hguards 1 (by omega) (by omega))
      (hguards 2 (by omega) (by omega)) hY)
    (hguards 3 (by omega) (by omega)) (hguards 4 (by omega) (by omega))
    (hguards 5 (by omega) (by omega)) hJ

end F4Heavy.Analysis
