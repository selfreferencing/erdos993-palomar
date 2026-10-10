module

public import Erdos993Lean.Analytic.V213.FiberTailInputDomain
public import Erdos993Lean.Analytic.V213.FiberTailWeightedTransfer
public import Erdos993Lean.Analytic.V213.FiberInputRateInterval
public import Erdos993Lean.Analytic.V213.FiberTailConstants

/-!
Real-domain consequences of all55 checked tail associations.
The actual endpoint, mean and target fields remain accepted F06 values.
The four weighted small guards use7/least-mu; the large guard uses the
actual cut c. The whole original activity interval is retained.

-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

theorem fiber_tail_input_mean (id : FiberInputIdentity) {mu : ℝ}
    (hmu : lowMeanFractionReal (fiberInputRouteById id).mu0 ≤ mu) :
    lowMeanFractionReal (fiberTailById (fiberInputTail id)).mu ≤ mu := by
  have hf := fiber_tail_input_facts id
  have hv : lowMeanFractionValid (fiberTailById (fiberInputTail id)).mu := by
    cases id <;> decide +kernel
  have hi := (fiber_input_domain_facts id).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact ((lowMean_fraction_le_iff hv hi).mp hf.2.1).trans hmu

theorem fiber_tail_input_cut (id : FiberInputIdentity) :
    lowMeanFractionReal (fiberTailById (fiberInputTail id)).c =
      lowMeanFractionReal (fiberInputRouteById id).c :=
  congrArg lowMeanFractionReal (fiber_tail_input_facts id).2.2.1

theorem fiber_tail_input_target_bounds (id : FiberInputIdentity) :
    lowMeanFractionReal (fiberInputClassB (fiberInputRouteById id).kind) ≤ 2/5 ∧
      0 ≤ lowMeanFractionReal (fiberInputClassBeta (fiberInputRouteById id).kind) := by
  have h := fiber_tail_input_facts id
  have hb : lowMeanFractionValid (fiberInputClassB (fiberInputRouteById id).kind) := by cases id <;> decide +kernel
  have hbeta : lowMeanFractionValid (fiberInputClassBeta (fiberInputRouteById id).kind) := by cases id <;> decide +kernel
  have h1 := (lowMean_fraction_le_iff hb (by norm_num [lowMeanFractionValid])).mp h.2.2.2.2.2.1
  have h2 := (lowMean_fraction_le_iff (by norm_num [lowMeanFractionValid]) hbeta).mp h.2.2.2.2.2.2.1
  norm_num only [show lowMeanFractionReal (2,5) = (2/5 : ℝ) by norm_num [lowMeanFractionReal],
    show lowMeanFractionReal (0,1) = (0 : ℝ) by norm_num [lowMeanFractionReal]] at h1 h2
  exact ⟨h1,h2⟩

theorem fiber_tail_input_skew (id : FiberInputIdentity) {lambda : ℝ}
    (hl : lowMeanFractionReal (fiberInputLoFraction id) ≤ lambda)
    (hh : lambda ≤ lowMeanFractionReal (fiberInputHiFraction id)) :
    |fiberSkew (FreeCountVariance.q lambda)| ≤ lowMeanFractionReal (fiberTailSkewCapFraction (fiberInputTail id)) := by
  have h := fiber_tail_input_facts id
  have hd := fiber_input_domain_facts id
  have hloV : lowMeanFractionValid (fiberInputSignedSkewFraction (fiberInputQloFraction id)) :=
    fiber_fraction_sub_valid (Nat.mul_pos (by norm_num [lowMeanFractionValid]) hd.2.2.1) (by norm_num [lowMeanFractionValid])
  have hhiV : lowMeanFractionValid (fiberInputSignedSkewFraction (fiberInputQhiFraction id)) :=
    fiber_fraction_sub_valid (Nat.mul_pos (by norm_num [lowMeanFractionValid]) hd.2.2.2.1) (by norm_num [lowMeanFractionValid])
  have hloA : lowMeanFractionValid (lowMeanFractionAbs (fiberInputSignedSkewFraction (fiberInputQloFraction id))) := hloV
  have hhiA : lowMeanFractionValid (lowMeanFractionAbs (fiberInputSignedSkewFraction (fiberInputQhiFraction id))) := hhiV
  have hlo := (lowMean_fraction_le_iff hloA h.1).mp h.2.2.2.1
  have hhi := (lowMean_fraction_le_iff hhiA h.1).mp h.2.2.2.2.1
  rw [lowMean_fraction_abs,fiber_input_signed_skew_real hd.2.2.1] at hlo
  rw [lowMean_fraction_abs,fiber_input_signed_skew_real hd.2.2.2.1] at hhi
  exact (fiber_input_whole_skew id hl hh).trans (max_le hlo hhi)

theorem fiber_tail_cap_parameters (id : FiberTailIdentity) :
    let r := lowMeanFractionReal (fiberTailSkewCapFraction id)
    0 ≤ r ∧ r < 1 ∧ fiberTailC r ≤ lowMeanFractionReal (fiberTailById id).C := by
  cases id <;> norm_num [fiberTailSkewCapFraction,fiberTailById,lowMeanFractionReal] <;>
    first | exact fiber_tail_C_central (by norm_num) (le_refl _) | exact fiber_tail_C_outer (by norm_num) (le_refl _)

theorem fiber_tail_weighted_parameters (id : FiberTailIdentity) (wid : FiberWeightIdentity)
    (hw : (fiberTailById id).weight = some wid) :
    lowMeanFractionReal ((fiberTailById id).smallGuard.getD (0,1)) =
      7/lowMeanFractionReal (fiberTailById id).mu ∧
    lowMeanFractionReal (fiberTailById id).d =
      lowMeanFractionReal (fiberWeightById wid).ell_w -
        lowMeanFractionReal (fiberTailById id).c*lowMeanFractionReal (fiberWeightById wid).L_w := by
  cases id <;> cases wid <;> norm_num [fiberTailById,fiberWeightById,lowMeanFractionReal] at hw <;>
    norm_num [fiberTailById,fiberWeightById,lowMeanFractionReal]

theorem fiber_tail_weighted_input_binding (id : FiberInputIdentity) (wid : FiberWeightIdentity)
    (hw : (fiberTailById (fiberInputTail id)).weight = some wid) :
    ∃ aid : FiberAnalyticInputIdentity, fiberAnalyticInput aid = id ∧ fiberAnalyticWeight aid = wid ∧
      lowMeanFractionReal (fiberWeightById wid).guard_lo ≤
        7/lowMeanFractionReal (fiberTailById (fiberInputTail id)).mu ∧
      7/lowMeanFractionReal (fiberTailById (fiberInputTail id)).mu ≤
        lowMeanFractionReal (fiberWeightById wid).guard_hi ∧
      lowMeanFractionReal (fiberWeightById wid).guard_lo ≤ lowMeanFractionReal (fiberTailById (fiberInputTail id)).c ∧
      lowMeanFractionReal (fiberTailById (fiberInputTail id)).c ≤ lowMeanFractionReal (fiberWeightById wid).guard_hi ∧
      (3/5 : ℝ) ≤ lowMeanFractionReal (fiberInputLoFraction id) := by
  have h := (fiber_tail_input_facts id).2.2.2.2.2.2.2.1
  rw [hw] at h
  dsimp only at h
  rcases h with ⟨hlo,hcase⟩
  cases hopt : fiberInputAnalyticOption id with
  | none => simp only [hopt] at hcase
  | some aid =>
    simp only [hopt] at hcase
    rcases hcase with ⟨hindex,heq,hgl,hgh,hcl,hch,_⟩
    have hi : fiberAnalyticInput aid = id := by
      have ha : fiberInputIdentityAt (fiberInputIndex (fiberAnalyticInput aid)) = fiberAnalyticInput aid := by
        cases aid <;> rfl
      have hid : fiberInputIdentityAt (fiberInputIndex id) = id := by cases id <;> rfl
      exact (ha.symm.trans (congrArg fiberInputIdentityAt hindex)).trans hid
    have hgV : lowMeanFractionValid ((fiberTailById (fiberInputTail id)).smallGuard.getD (0,1)) := by
      cases id <;> decide +kernel
    have hclV : lowMeanFractionValid (fiberTailById (fiberInputTail id)).c := by cases id <;> decide +kernel
    have hloV : lowMeanFractionValid (fiberWeightById wid).guard_lo := by cases wid <;> decide +kernel
    have hhiV : lowMeanFractionValid (fiberWeightById wid).guard_hi := by cases wid <;> decide +kernel
    have hg1 := (lowMean_fraction_le_iff hloV hgV).mp hgl
    have hg2 := (lowMean_fraction_le_iff hgV hhiV).mp hgh
    rw [(fiber_tail_weighted_parameters (fiberInputTail id) wid hw).1] at hg1 hg2
    have hc1 := (lowMean_fraction_le_iff hloV hclV).mp hcl
    have hc2 := (lowMean_fraction_le_iff hclV hhiV).mp hch
    have hlV := (fiber_input_domain_facts id).1
    have hlR := (lowMean_fraction_le_iff (by norm_num [lowMeanFractionValid]) hlV).mp hlo
    norm_num only [show lowMeanFractionReal (3,5) = (3/5 : ℝ) by norm_num [lowMeanFractionReal]] at hlR
    exact ⟨aid,hi,heq,hg1,hg2,hc1,hc2,hlR⟩

end Erdos993Lean.Analytic.V213
