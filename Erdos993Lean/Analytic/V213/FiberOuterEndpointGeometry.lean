module

public import Erdos993Lean.Analytic.V213.FiberAffineBranches
public import Erdos993Lean.Analytic.V213.FiberEndpointPrinciple
public import Erdos993Lean.Analytic.V213.FreeCountRealLogEnvelopes

/-!
Endpoint guards on the actual positive size-ratio domain. The strict
supremum bound is global, including arbitrarily small and large t. The
printed logarithm enclosure with tail 1/5 is derived from the accepted
stronger 1/7 artanh enclosure. No generated start data is consumed here.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real Set

noncomputable def fiberOuterLogBound (z : ℝ) : ℝ :=
  2 * (z + z ^ 3 / 3 + z ^ 5 / (5 * (1 - z ^ 2)))

theorem fiber_outer_target_identity {t : ℝ} (ht : 0 < t) (b beta : ℝ) :
    t * fiberEndpointTarget (10 + beta) (9 / 2 + beta - b) t =
      fiberPsi t + b + beta * (t - 1) := by
  unfold fiberEndpointTarget fiberPsi
  field_simp [ht.ne']
  ring

theorem fiber_outer_target_global_cap {b beta : ℝ} (hb : b ≤ 2 / 5)
    (hbeta0 : 0 ≤ beta) (hbetah : beta ≤ 1) {t : ℝ} (ht : 0 < t) :
    fiberEndpointTarget (10 + beta) (9 / 2 + beta - b) t ≤ 1589 / 1080 := by
  have hc : 0 < 9 / 2 + beta - b := by linarith only [hb,hbeta0]
  by_cases ht3 : t ≤ 3
  · have hm := fiber_affine_three_half_margin (t := t) hb hbeta0 hbetah
    rw [← fiber_outer_target_identity ht] at hm
    have hgap : (31 / 1080 : ℝ) * t ≤ 31 / 360 := by linarith only [ht3]
    have he : t * fiberEndpointTarget (10 + beta) (9 / 2 + beta - b) t ≤
        t * (1589 / 1080 : ℝ) := by linarith only [hm,hgap]
    exact (mul_le_mul_iff_right₀ ht).mp (by simpa only [mul_comm] using he)
  · have hlarge : 3 ≤ t := (lt_of_not_ge ht3).le
    have hdiv : 0 ≤ (9 / 2 + beta - b) / t := div_nonneg hc.le ht.le
    unfold fiberEndpointTarget
    linarith only [hlarge,hdiv,hbetah]

theorem fiber_outer_target_supremum {b beta : ℝ} (hb : b ≤ 2 / 5)
    (hbeta0 : 0 ≤ beta) (hbetah : beta ≤ 1) :
    sSup ((fiberEndpointTarget (10 + beta) (9 / 2 + beta - b)) '' Ioi 0) ≤
      1589 / 1080 ∧
      sSup ((fiberEndpointTarget (10 + beta) (9 / 2 + beta - b)) '' Ioi 0) < 3 / 2 := by
  have hn : ((fiberEndpointTarget (10 + beta) (9 / 2 + beta - b)) '' Ioi 0).Nonempty :=
    ⟨_,1,by norm_num,rfl⟩
  have hsup : sSup ((fiberEndpointTarget (10 + beta) (9 / 2 + beta - b)) '' Ioi 0) ≤
      (1589 / 1080 : ℝ) := by
    apply csSup_le hn
    rintro x ⟨t,ht,rfl⟩
    exact fiber_outer_target_global_cap hb hbeta0 hbetah ht
  exact ⟨hsup,hsup.trans_lt (by norm_num)⟩

theorem fiber_outer_log_bound {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    Real.log ((1 + z) / (1 - z)) ≤ fiberOuterLogBound z := by
  have h := (FreeCountVariance.Envelopes.artanh_brackets hz0 hz1).2
  have hd : 0 < 1 - z ^ 2 := by nlinarith only [hz0,hz1]
  have he : fiberOuterLogBound z - FreeCountVariance.Envelopes.seriesT z =
      4 * z ^ 7 / (35 * (1 - z ^ 2)) := by
    unfold fiberOuterLogBound FreeCountVariance.Envelopes.seriesT FreeCountVariance.Envelopes.seriesS
    field_simp [hd.ne']
    ring
  have hp : 0 ≤ 4 * z ^ 7 / (35 * (1 - z ^ 2)) := by positivity
  linarith only [h,he,hp]

theorem fiber_outer_log_sigma {sigma : ℝ} (hs : 0 < sigma) (hsh : sigma ≤ 1) :
    -Real.log sigma ≤ fiberOuterLogBound ((1 - sigma) / (1 + sigma)) := by
  have hd : 0 < 1 + sigma := by linarith only [hs]
  have hz0 : 0 ≤ (1 - sigma) / (1 + sigma) := div_nonneg (by linarith only [hsh]) hd.le
  have hz1 : (1 - sigma) / (1 + sigma) < 1 := (div_lt_one hd).2 (by linarith only [hs])
  have h := fiber_outer_log_bound hz0 hz1
  have he : (1 + (1 - sigma) / (1 + sigma)) / (1 - (1 - sigma) / (1 + sigma)) = sigma⁻¹ := by
    field_simp [hs.ne',hd.ne']
    ring
  rw [he,Real.log_inv] at h
  exact h

end Erdos993Lean.Analytic.V213
