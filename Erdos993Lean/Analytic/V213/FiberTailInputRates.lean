module

public import Erdos993Lean.Analytic.V213.FiberTailInputSmall
public import Erdos993Lean.Analytic.V213.FiberCoupledInputRates

/-!
Actual large-tail decay rates over all55 closed activity intervals.
The first six rows use the coupled functions at the actual upper
endpoint; .279 and .3384 are not asserted to be common input rates.
The four weighted rows use the checked guard at the actual cut c.

-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

theorem fiber_tail_coupled_cut_rate (id : FiberCornerRateIdentity) {lambda : ℝ}
    (hlambda : 0 ≤ lambda)
    (hh : lambda ≤ lowMeanFractionReal (fiberInputHiFraction (fiberCornerRateById id).input)) :
    lowMeanFractionReal (fiberTailById (fiberInputTail (fiberCornerRateById id).input)).d ≤
      lowMeanFractionReal (fiberInputRouteById (fiberCornerRateById id).input).ell0 -
        lowMeanFractionReal (fiberTailById (fiberInputTail (fiberCornerRateById id).input)).c * Real.log (1+lambda) := by
  have hslack := (fiber_corner_rate_bound id).le
  rcases fiber_corner_rate_facts id with ⟨_,_,_,hhi,_,_,_,_,_,_⟩
  have hhiR := congrArg lowMeanFractionReal hhi
  rw [← hhiR] at hh hslack
  have hc0 : 0 ≤ lowMeanFractionReal (fiberTailById (fiberInputTail (fiberCornerRateById id).input)).c := by
    cases id <;> norm_num [fiberCornerRateById,fiberInputTail,fiberInputTailIdentity,fiberInputRouteById,fiberTailById,lowMeanFractionReal]
  have htransfer := fiber_coupled_input_transfer hslack hlambda hh hc0 (le_refl _)
  cases id with
  | iota0 =>
    have h := fiber_c1_coupled_lower (z := 9/25) (c := 13/25) (by norm_num) (Or.inl rfl)
    norm_num [fiberCornerRateById,fiberInputTail,fiberInputTailIdentity,fiberInputRouteById,fiberTailById,lowMeanFractionReal] at htransfer ⊢
    norm_num at h
    simpa only [mul_comm] using h.trans htransfer
  | iota1 =>
    have h := fiber_c1_coupled_lower (z := 2/5) (c := 13/25) (by norm_num) (Or.inl rfl)
    norm_num [fiberCornerRateById,fiberInputTail,fiberInputTailIdentity,fiberInputRouteById,fiberTailById,lowMeanFractionReal] at htransfer ⊢
    norm_num at h
    simpa only [mul_comm] using h.trans htransfer
  | iota2 =>
    have h := fiber_c1_coupled_lower (z := 9/20) (c := 13/25) (by norm_num) (Or.inl rfl)
    norm_num [fiberCornerRateById,fiberInputTail,fiberInputTailIdentity,fiberInputRouteById,fiberTailById,lowMeanFractionReal] at htransfer ⊢
    norm_num at h
    simpa only [mul_comm] using h.trans htransfer
  | iota3 =>
    have h := fiber_c2_cut_coupled_lower (z := 1/2) (by norm_num)
    norm_num [fiberCornerRateById,fiberInputTail,fiberInputTailIdentity,fiberInputRouteById,fiberTailById,lowMeanFractionReal] at htransfer ⊢
    norm_num at h
    simpa only [mul_comm] using h.trans htransfer
  | iota4 =>
    have h := fiber_c2_cut_coupled_lower (z := 11/20) (by norm_num)
    norm_num [fiberCornerRateById,fiberInputTail,fiberInputTailIdentity,fiberInputRouteById,fiberTailById,lowMeanFractionReal] at htransfer ⊢
    norm_num at h
    simpa only [mul_comm] using h.trans htransfer
  | iota5 =>
    have h := fiber_c2_cut_coupled_lower (z := 3/5) (by norm_num)
    norm_num [fiberCornerRateById,fiberInputTail,fiberInputTailIdentity,fiberInputRouteById,fiberTailById,lowMeanFractionReal] at htransfer ⊢
    norm_num at h
    simpa only [mul_comm] using h.trans htransfer

theorem fiber_tail_ordinary_log_parameters (id : FiberInputIdentity) (lid : FiberCornerLogIdentity)
    (hlog : fiberTailOrdinaryLog (fiberInputTail id) = some lid) :
    (fiberTailById (fiberInputTail id)).h_i = some (fiberCornerLogById lid).y ∧
      lowMeanFractionReal (fiberTailById (fiberInputTail id)).d =
        lowMeanFractionReal (fiberTailById (fiberInputTail id)).ell -
          lowMeanFractionReal (fiberTailById (fiberInputTail id)).c*lowMeanFractionReal (fiberCornerLogById lid).L := by
  have hf := (fiber_tail_input_facts id).2.2.2.2.2.2.2.2
  rw [hlog] at hf
  dsimp only at hf
  refine ⟨hf.1,?_⟩
  have hd : lowMeanFractionValid (fiberTailById (fiberInputTail id)).d := by cases id <;> decide +kernel
  have he : lowMeanFractionValid (fiberTailById (fiberInputTail id)).ell := by cases id <;> decide +kernel
  have hc : lowMeanFractionValid (fiberTailById (fiberInputTail id)).c := by cases id <;> decide +kernel
  have hL : lowMeanFractionValid (fiberCornerLogById lid).L := by cases lid <;> decide +kernel
  have hp : lowMeanFractionValid (lowMeanFractionMul (fiberTailById (fiberInputTail id)).c
      (fiberCornerLogById lid).L) := Nat.mul_pos hc hL
  have hv := fiber_fraction_sub_valid he hp
  have hr := (lowMean_fraction_eq_iff hd hv).mp hf.2
  rw [fiber_fraction_sub_real he hp,lowMean_fraction_mul] at hr
  exact hr

theorem fiber_tail_input_large_rate (id : FiberInputIdentity) {lambda : ℝ}
    (hl : lowMeanFractionReal (fiberInputLoFraction id) ≤ lambda)
    (hh : lambda ≤ lowMeanFractionReal (fiberInputHiFraction id)) :
    lowMeanFractionReal (fiberTailById (fiberInputTail id)).d ≤
      lowMeanFractionReal (fiberInputRouteById id).ell0 -
        lowMeanFractionReal (fiberTailById (fiberInputTail id)).c*Real.log (1+lambda) := by
  have hlam := fiber_input_activity_nonneg id hl
  cases hw : (fiberTailById (fiberInputTail id)).weight with
  | some wid =>
    rcases fiber_tail_weighted_input_binding id wid hw with ⟨aid,hi,hwid,_,_,hcl,hch,_⟩
    have hg := fiber_input_guard_actual_log aid (by simpa only [hi] using hlam)
      (by simpa only [hi] using hh) (by simpa only [hwid] using hcl) (by simpa only [hwid] using hch)
    simp only [hi,hwid] at hg
    rw [(fiber_tail_weighted_parameters (fiberInputTail id) wid hw).2]
    linarith only [hg]
  | none =>
    cases hlog : fiberTailOrdinaryLog (fiberInputTail id) with
    | some lid =>
      have hb := fiber_tail_ordinary_input_binding id hw
      have hp := fiber_tail_ordinary_log_parameters id lid hlog
      have hhi : 0 < lowMeanFractionReal ((fiberTailById (fiberInputTail id)).h_i.getD (1,1)) := by
        linarith only [hb.2.1]
      have hlogle : Real.log (1+lambda) ≤ lowMeanFractionReal (fiberCornerLogById lid).L := by
        have h := (Real.log_le_log (by linarith only [hlam] : 0 < 1+lambda)
          ((show 1+lambda ≤ 1+lowMeanFractionReal (fiberInputHiFraction id) by linarith only [hh]).trans hb.2.2))
        rw [hp.1] at h
        exact h.trans (fiber_corner_log_upper lid)
      have hc0 := (fiber_tail_real_parameters (fiberInputTail id)).2.2.1.le
      have hm := mul_le_mul_of_nonneg_left hlogle hc0
      rw [hp.2]
      linarith only [hb.1,hm]
    | none =>
      cases id <;> norm_num [fiberInputTail,fiberInputTailIdentity,fiberInputRouteById,
        fiberTailById,fiberTailOrdinaryLog] at hw <;>
          norm_num [fiberInputTail,fiberInputTailIdentity,fiberInputRouteById,
            fiberTailById,fiberTailOrdinaryLog] at hlog <;>
              norm_num [fiberInputTail,fiberInputTailIdentity,fiberInputRouteById,
                fiberTailById,fiberTailOrdinaryLog]
      all_goals first
        | exact fiber_tail_coupled_cut_rate .iota0 hlam hh
        | exact fiber_tail_coupled_cut_rate .iota1 hlam hh
        | exact fiber_tail_coupled_cut_rate .iota2 hlam hh
        | exact fiber_tail_coupled_cut_rate .iota3 hlam hh
        | exact fiber_tail_coupled_cut_rate .iota4 hlam hh
        | exact fiber_tail_coupled_cut_rate .iota5 hlam hh

end Erdos993Lean.Analytic.V213
