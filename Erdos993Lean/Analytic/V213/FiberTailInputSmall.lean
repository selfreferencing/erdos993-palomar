module

public import Erdos993Lean.Analytic.V213.FiberTailInputParameters

/-!
Actual small-fiber prices on all55 original activity intervals. Ordinary
rows consume the checked geometric branch. Weighted rows consume Eq97
at7 divided by the least table mean, with the original q in the weight.

-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

theorem fiber_input_original_log {lambda : ℝ} (hl : 0 ≤ lambda) :
    -Real.log (1-FreeCountVariance.q lambda) = Real.log (1+lambda) := by
  have hp : 1+lambda ≠ 0 := by linarith only [hl]
  have he : 1-FreeCountVariance.q lambda = (1+lambda)⁻¹ := by
    unfold FreeCountVariance.q
    field_simp [hp] <;> ring
  rw [he,Real.log_inv,neg_neg]

theorem fiber_tail_ordinary_input_binding (id : FiberInputIdentity)
    (hnone : (fiberTailById (fiberInputTail id)).weight = none) :
    lowMeanFractionReal (fiberTailById (fiberInputTail id)).ell ≤
      lowMeanFractionReal (fiberInputRouteById id).ell0 ∧
    1 ≤ lowMeanFractionReal ((fiberTailById (fiberInputTail id)).h_i.getD (1,1)) ∧
    1+lowMeanFractionReal (fiberInputHiFraction id) ≤
      lowMeanFractionReal ((fiberTailById (fiberInputTail id)).h_i.getD (1,1)) := by
  have h := (fiber_tail_input_facts id).2.2.2.2.2.2.2.1
  rw [hnone] at h
  dsimp only at h
  rcases h with ⟨he,hv,h1,hhi⟩
  have hellV : lowMeanFractionValid (fiberTailById (fiberInputTail id)).ell := by cases id <;> decide +kernel
  have hiV : lowMeanFractionValid (fiberInputRouteById id).ell0 := by cases id <;> decide +kernel
  have hhV := (fiber_input_domain_facts id).2.1
  have hsumV : lowMeanFractionValid (lowMeanFractionAdd (1,1) (fiberInputHiFraction id)) :=
    Nat.mul_pos (by norm_num [lowMeanFractionValid]) hhV
  have heR := (lowMean_fraction_le_iff hellV hiV).mp he
  have h1R := (lowMean_fraction_le_iff (by norm_num [lowMeanFractionValid]) hv).mp h1
  have hhR := (lowMean_fraction_le_iff hsumV hv).mp hhi
  rw [lowMean_fraction_add (by norm_num [lowMeanFractionValid]) hhV] at hhR
  norm_num only [show lowMeanFractionReal (1,1) = (1 : ℝ) by norm_num [lowMeanFractionReal]] at h1R hhR
  exact ⟨heR,h1R,hhR⟩

theorem fiber_tail_input_small_price (id : FiberInputIdentity) {lambda mu : ℝ} {M : ℕ}
    (hl : lowMeanFractionReal (fiberInputLoFraction id) ≤ lambda)
    (hh : lambda ≤ lowMeanFractionReal (fiberInputHiFraction id))
    (hmu : lowMeanFractionReal (fiberInputRouteById id).mu0 ≤ mu) (hM : M ≤ 7) :
    fiberSpikeTerm (FreeCountVariance.q lambda) mu
      (lowMeanFractionReal (fiberInputRouteById id).ell0) (fiberInputTarget id) M <
      lowMeanFractionReal (fiberTailById (fiberInputTail id)).Z_a := by
  have hlam := fiber_input_activity_nonneg id hl
  have hq := fiber_input_probability_domain id hl hh
  have hm := fiber_tail_input_mean id hmu
  have hcap := fiber_tail_cap_parameters (fiberInputTail id)
  have hskew := fiber_tail_input_skew id hl hh
  have htarget := fiber_tail_input_target_bounds id
  have hlog := fiber_input_original_log hlam
  cases hw : (fiberTailById (fiberInputTail id)).weight with
  | none =>
    have hb := fiber_tail_ordinary_input_binding id hw
    have hhi : 0 < lowMeanFractionReal ((fiberTailById (fiberInputTail id)).h_i.getD (1,1)) := by
      linarith only [hb.2.1]
    have hL : -Real.log (1-FreeCountVariance.q lambda) ≤
        Real.log (lowMeanFractionReal ((fiberTailById (fiberInputTail id)).h_i.getD (1,1))) := by
      rw [hlog]
      apply Real.log_le_log (by linarith only [hlam])
      exact (show 1+lambda ≤ 1+lowMeanFractionReal (fiberInputHiFraction id) by linarith only [hh]).trans hb.2.2
    exact fiber_tail_ordinary_small_transfer (fiberInputTail id) hw hq hm hM
      hcap.1 hcap.2.1 hskew hcap.2.2 htarget.1 htarget.2 hb.1 hhi hL
  | some wid =>
    rcases fiber_tail_weighted_input_binding id wid hw with ⟨aid,hi,hwid,hgl,hgh,_,_,hlo⟩
    have hg := fiber_input_guard_actual_log aid (by simpa only [hi] using hlam)
      (by simpa only [hi] using hh) (by simpa only [hwid] using hgl) (by simpa only [hwid] using hgh)
    simp only [hi,hwid] at hg
    have hp := fiber_tail_real_parameters (fiberInputTail id)
    have hmup : 0 < lowMeanFractionReal (fiberTailById (fiberInputTail id)).mu := by linarith only [hp.1]
    have hmul := mul_le_mul_of_nonneg_right hg hmup.le
    have hclear :
        lowMeanFractionReal (fiberTailById (fiberInputTail id)).mu*lowMeanFractionReal (fiberWeightById wid).ell_w -
          7*lowMeanFractionReal (fiberWeightById wid).L_w +
          lowMeanFractionReal (fiberTailById (fiberInputTail id)).mu/100000 ≤
        lowMeanFractionReal (fiberInputRouteById id).ell0*lowMeanFractionReal (fiberTailById (fiberInputTail id)).mu -
          7*Real.log (1+lambda) := by
      convert hmul using 1 <;> field_simp [hmup.ne'] <;> ring
    have hx : fiberTailXA (fiberInputTail id) =
        lowMeanFractionReal (fiberTailById (fiberInputTail id)).mu*lowMeanFractionReal (fiberWeightById wid).ell_w -
          7*lowMeanFractionReal (fiberWeightById wid).L_w := by
      simp only [fiberTailXA,hw]
    have hguard : fiberTailXA (fiberInputTail id) ≤
        lowMeanFractionReal (fiberInputRouteById id).ell0*lowMeanFractionReal (fiberTailById (fiberInputTail id)).mu -
          7*Real.log (1+lambda) := by rw [hx]; linarith only [hclear,hmup]
    have hgeom : 1 ≤ (27/40 : ℝ)*Real.exp (Real.log (1+lambda)) := by
      rw [Real.exp_log (by linarith only [hlam])]
      linarith only [hlo.trans hl]
    exact fiber_tail_weighted_small_transfer (fiberInputTail id) wid hw hq hm hM
      hcap.1 hcap.2.1 hskew hcap.2.2 htarget.1 htarget.2 hlog.le hgeom hguard

end Erdos993Lean.Analytic.V213
