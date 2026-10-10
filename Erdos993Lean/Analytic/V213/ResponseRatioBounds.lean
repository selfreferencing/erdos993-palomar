module

public import Erdos993Lean.Analytic.V213.ResponseRatioIntegral
public import Erdos993Lean.Analytic.V213.FreeCountRealScalarBounds

/-!
# Current Lemma 5.3: elementary logarithm and ratio bounds

The two displayed logarithm inequalities already have generic Real proofs in
the accepted scalar module. Only these scalar facts are reused. The stronger
ratio lower bound and its strict comparison are proved here, and the assigned
zero value is shown to be continuous from the paper's domain.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse

open Set Filter FreeCountVariance.Envelopes
open scoped Topology

theorem elementary_log_bounds {z : ℝ} (hz : 0 ≤ z) :
    2 * z / (2 + z) ≤ Real.log (1 + z) ∧
      Real.log (1 + z) ≤ z * (2 + z) / (2 * (1 + z)) :=
  log_star hz

theorem messageRatio_eq_scalarH {u : ℝ} (hu : u ≠ 0) :
    messageRatio u = scalarH u := by
  simp only [messageRatio_of_ne_zero hu, scalarH, scalarLog]

theorem scalarLog_sharp_upper {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    scalarLog u ≤ u * (2 - u) / (2 * (1 - u)) := by
  have hb : 0 < 1 - u := by linarith
  have hz : 0 ≤ u / (1 - u) := div_nonneg hu0.le hb.le
  have h := (elementary_log_bounds hz).2
  rw [log_odds_eq hu1] at h
  have heq : (u / (1 - u)) * (2 + u / (1 - u)) /
      (2 * (1 + u / (1 - u))) = u * (2 - u) / (2 * (1 - u)) := by
    apply (div_eq_div_iff (by positivity) (by positivity)).2
    field_simp [hb.ne'] <;> ring
  rwa [heq] at h

theorem messageRatio_lower {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    2 * (1 - u) / (2 - u) ≤ messageRatio u := by
  by_cases hu : u = 0
  · subst u
    norm_num [messageRatio_zero]
  have hup : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hu)
  have hL := scalarLog_pos hup hu1
  have hb : 0 < 1 - u := by linarith
  have h2 : 0 < 2 - u := by linarith
  have hcross : scalarLog u * (2 * (1 - u)) ≤ u * (2 - u) :=
    (le_div_iff₀ (by positivity)).mp (scalarLog_sharp_upper hup hu1)
  rw [messageRatio_eq_scalarH hu, scalarH]
  apply (le_div_iff₀ hL).2
  rw [div_mul_eq_mul_div]
  exact (div_le_iff₀ h2).2 (by nlinarith [hcross])

theorem messageRatio_weak_bounds {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    1 - u ≤ messageRatio u ∧ messageRatio u ≤ 1 - u / 2 := by
  by_cases hu : u = 0
  · subst u
    norm_num [messageRatio_zero]
  have hup : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hu)
  rw [messageRatio_eq_scalarH hu]
  exact scalarH_bounds hup hu1

theorem messageRatio_strict_lower {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    1 - u < messageRatio u := by
  have hb : 0 < 1 - u := by linarith
  have hr : 0 < u / (1 - u) := div_pos hu0 hb
  have hlog := Real.log_lt_sub_one_of_pos
    (show 0 < 1 + u / (1 - u) by linarith)
    (show 1 + u / (1 - u) ≠ 1 by linarith)
  rw [log_odds_eq hu1] at hlog
  have hlog' : scalarLog u < u / (1 - u) := by linarith
  have hcross := (lt_div_iff₀ hb).mp hlog'
  rw [messageRatio_eq_scalarH hu0.ne', scalarH]
  apply (lt_div_iff₀ (scalarLog_pos hu0 hu1)).2
  nlinarith

theorem messageRatio_continuousWithinAt_zero :
    ContinuousWithinAt messageRatio (Ico 0 1) 0 := by
  change Tendsto messageRatio (𝓝[Ico 0 1] 0) (𝓝 (messageRatio 0))
  rw [messageRatio_zero]
  have hl : ContinuousWithinAt (fun u : ℝ => 1 - u) (Ico 0 1) 0 :=
    (continuous_const.sub continuous_id).continuousWithinAt
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa only [ContinuousWithinAt, sub_zero] using hl)
    (show Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[Ico 0 1] 0) (𝓝 1)
      from tendsto_const_nhds)
  · filter_upwards [self_mem_nhdsWithin] with u hu
    exact (messageRatio_weak_bounds hu.1 hu.2).1
  · filter_upwards [self_mem_nhdsWithin] with u hu
    have h := (messageRatio_weak_bounds hu.1 hu.2).2
    linarith [hu.1]

theorem messageRatio_continuousOn : ContinuousOn messageRatio (Ico 0 1) := by
  intro u hu
  by_cases hz : u = 0
  · subst u
    exact messageRatio_continuousWithinAt_zero
  have hup : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hz)
  have hc : ContinuousAt scalarH u := (hasDerivAt_scalarH hup hu.2).continuousAt
  have heq : messageRatio =ᶠ[𝓝 u] scalarH := by
    filter_upwards [eventually_ne_nhds hz] with x hx
    exact messageRatio_eq_scalarH hx
  exact (hc.congr_of_eventuallyEq heq).continuousWithinAt

end Erdos993Lean.Analytic.V213.VarianceResponse

#check Erdos993Lean.Analytic.V213.VarianceResponse.elementary_log_bounds
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.elementary_log_bounds
#check Erdos993Lean.Analytic.V213.VarianceResponse.messageRatio_eq_scalarH
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.messageRatio_eq_scalarH
#check Erdos993Lean.Analytic.V213.VarianceResponse.scalarLog_sharp_upper
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.scalarLog_sharp_upper
#check Erdos993Lean.Analytic.V213.VarianceResponse.messageRatio_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.messageRatio_lower
#check Erdos993Lean.Analytic.V213.VarianceResponse.messageRatio_weak_bounds
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.messageRatio_weak_bounds
#check Erdos993Lean.Analytic.V213.VarianceResponse.messageRatio_strict_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.messageRatio_strict_lower
#check Erdos993Lean.Analytic.V213.VarianceResponse.messageRatio_continuousWithinAt_zero
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.messageRatio_continuousWithinAt_zero
#check Erdos993Lean.Analytic.V213.VarianceResponse.messageRatio_continuousOn
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.messageRatio_continuousOn

-- Audits of the reused generic scalar facts.
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.log_star
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.log_star
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.log_odds_eq
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.log_odds_eq
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.scalarLog_pos
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.scalarLog_pos
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.scalarH_bounds
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.scalarH_bounds
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.hasDerivAt_scalarH
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.hasDerivAt_scalarH
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.scalarLog
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.scalarLog
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.scalarH
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.scalarH
