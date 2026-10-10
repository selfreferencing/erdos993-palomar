module

public import Erdos993Lean.Analytic.V213.FiberInputDomain
public import Erdos993Lean.Analytic.V213.FiberProfileTransport

/-!
All41 analytic inputs satisfy the named profile's exact lower and
upper skew bounds and starting mean throughout their actual closed N44
interval. The integer-width bridge keeps the separate small-width cut,
including the H record's m_f=14 rather than silently using m_f=8.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

def fiberAnalyticInputDomainTests (id : FiberAnalyticInputIdentity) : Prop :=
  let input := fiberAnalyticInput id
  let p := fiberRationalProfileById (fiberWeightById (fiberAnalyticWeight id)).profile
  let r := fiberRayById (fiberRationalProfileRay (fiberWeightById (fiberAnalyticWeight id)).profile)
  let lo := fiberInputSignedSkewFraction (fiberInputQloFraction input)
  let hi := fiberInputSignedSkewFraction (fiberInputQhiFraction input)
  lowMeanFractionValid p.ra ∧ lowMeanFractionValid p.m ∧ lowMeanFractionValid r.R ∧
  lowMeanFractionLE p.m (fiberInputRouteById input).mu0 ∧
  lowMeanFractionLE (lowMeanFractionAbs lo) r.R ∧ lowMeanFractionLE (lowMeanFractionAbs hi) r.R ∧
  (lowMeanFractionEq p.ra (0,1) ∨ lowMeanFractionLE p.ra lo ∨ lowMeanFractionLE hi (lowMeanFractionNeg p.ra))

instance fiberAnalyticInputDomainTestsDecidable (id : FiberAnalyticInputIdentity) :
    Decidable (fiberAnalyticInputDomainTests id) := by
  unfold fiberAnalyticInputDomainTests
  infer_instance

theorem fiber_analytic_input_domain_checks :
    (List.range 41).all (fun k => decide (fiberAnalyticInputDomainTests (fiberAnalyticInputIdentityAt k))) = true := by
  decide +kernel

theorem fiber_analytic_input_domain_facts (id : FiberAnalyticInputIdentity) :
    fiberAnalyticInputDomainTests id := by
  have hk : fiberAnalyticInputIndex id < 41 := by cases id <;> decide +kernel
  have hi : fiberAnalyticInputIdentityAt (fiberAnalyticInputIndex id) = id := by cases id <;> rfl
  have h := Erdos993Lean.F4Fast.forall_lt_of_range_all fiber_analytic_input_domain_checks (fiberAnalyticInputIndex id) hk
  rw [hi] at h
  exact of_decide_eq_true h

theorem fiber_analytic_input_profile_mean (id : FiberAnalyticInputIdentity) {mu : ℝ}
    (hmu : lowMeanFractionReal (fiberInputRouteById (fiberAnalyticInput id)).mu0 ≤ mu) :
    lowMeanFractionReal (fiberRationalProfileById (fiberWeightById (fiberAnalyticWeight id)).profile).m ≤ mu := by
  have h := fiber_analytic_input_domain_facts id
  have hv := (fiber_input_rate_facts id).1.2.2.2.1
  exact ((lowMean_fraction_le_iff h.2.1 hv).mp h.2.2.2.1).trans hmu

theorem fiber_analytic_input_profile_skew (id : FiberAnalyticInputIdentity) {lambda : ℝ}
    (hl : lowMeanFractionReal (fiberInputLoFraction (fiberAnalyticInput id)) ≤ lambda)
    (hh : lambda ≤ lowMeanFractionReal (fiberInputHiFraction (fiberAnalyticInput id))) :
    lowMeanFractionReal (fiberRationalProfileById (fiberWeightById (fiberAnalyticWeight id)).profile).ra ≤
        |fiberSkew (FreeCountVariance.q lambda)| ∧
    |fiberSkew (FreeCountVariance.q lambda)| ≤ lowMeanFractionReal
        (fiberRayById (fiberRationalProfileRay (fiberWeightById (fiberAnalyticWeight id)).profile)).R := by
  have h := fiber_analytic_input_domain_facts id
  have hd := fiber_input_domain_facts (fiberAnalyticInput id)
  have hq := fiber_input_q_interval (fiberAnalyticInput id) hl hh
  have hloV : lowMeanFractionValid (fiberInputSignedSkewFraction (fiberInputQloFraction (fiberAnalyticInput id))) :=
    fiber_fraction_sub_valid (Nat.mul_pos (by norm_num [lowMeanFractionValid]) hd.2.2.1) (by norm_num [lowMeanFractionValid])
  have hhiV : lowMeanFractionValid (fiberInputSignedSkewFraction (fiberInputQhiFraction (fiberAnalyticInput id))) :=
    fiber_fraction_sub_valid (Nat.mul_pos (by norm_num [lowMeanFractionValid]) hd.2.2.2.1) (by norm_num [lowMeanFractionValid])
  have hloAbsV : lowMeanFractionValid (lowMeanFractionAbs (fiberInputSignedSkewFraction
      (fiberInputQloFraction (fiberAnalyticInput id)))) := hloV
  have hhiAbsV : lowMeanFractionValid (lowMeanFractionAbs (fiberInputSignedSkewFraction
      (fiberInputQhiFraction (fiberAnalyticInput id)))) := hhiV
  have hloR := (lowMean_fraction_le_iff hloAbsV h.2.2.1).mp h.2.2.2.2.1
  have hhiR := (lowMean_fraction_le_iff hhiAbsV h.2.2.1).mp h.2.2.2.2.2.1
  rw [lowMean_fraction_abs,fiber_input_signed_skew_real hd.2.2.1] at hloR
  rw [lowMean_fraction_abs,fiber_input_signed_skew_real hd.2.2.2.1] at hhiR
  have hu := (fiber_input_whole_skew (fiberAnalyticInput id) hl hh).trans (max_le hloR hhiR)
  refine ⟨?_,hu⟩
  rcases h.2.2.2.2.2.2 with hz | hp | hn
  · have he := (lowMean_fraction_eq_iff h.1 (by norm_num [lowMeanFractionValid])).mp hz
    have hzR : lowMeanFractionReal (0,1) = (0 : ℝ) := by norm_num [lowMeanFractionReal]
    rw [hzR] at he
    rw [he]
    exact abs_nonneg _
  · have he := (lowMean_fraction_le_iff h.1 hloV).mp hp
    rw [fiber_input_signed_skew_real hd.2.2.1] at he
    have hmono : fiberSkew (lowMeanFractionReal (fiberInputQloFraction (fiberAnalyticInput id))) ≤
        fiberSkew (FreeCountVariance.q lambda) := by unfold fiberSkew; linarith only [hq.1]
    exact (he.trans hmono).trans (le_abs_self _)
  · have hnegV : lowMeanFractionValid (lowMeanFractionNeg
        (fiberRationalProfileById (fiberWeightById (fiberAnalyticWeight id)).profile).ra) := h.1
    have he := (lowMean_fraction_le_iff hhiV hnegV).mp hn
    rw [fiber_input_signed_skew_real hd.2.2.2.1,lowMean_fraction_neg] at he
    have hmono : fiberSkew (FreeCountVariance.q lambda) ≤
        fiberSkew (lowMeanFractionReal (fiberInputQhiFraction (fiberAnalyticInput id))) := by
      unfold fiberSkew; linarith only [hq.2]
    have hneg := neg_abs_le (fiberSkew (FreeCountVariance.q lambda))
    linarith only [hneg,hmono,he]

theorem fiber_profile_actual_record_width (id : FiberRationalProfileIdentity) {M : ℕ} {mu : ℝ}
    (hmu : lowMeanFractionReal (fiberRationalProfileById id).m ≤ mu)
    (hM : 8 ≤ M) (ht : 1/3 ≤ (M : ℝ)/mu) :
    lowMeanFractionReal (fiberRayById (fiberRationalProfileRay id)).m_f ≤ (M : ℝ) := by
  cases id with
  | a | b | d | g =>
      norm_num [fiberRationalProfileRay,fiberRayById,lowMeanFractionReal]
      exact_mod_cast hM
  | h =>
      norm_num [fiberRationalProfileById,lowMeanFractionReal] at hmu
      have hmup : 0 < mu := by linarith only [hmu]
      have ht' := (le_div_iff₀ hmup).mp ht
      have h14 : 14 ≤ M := by
        by_contra hn
        have h13 : M ≤ 13 := by omega
        have h13r : (M : ℝ) ≤ 13 := by exact_mod_cast h13
        linarith only [ht',hmu,h13r]
      norm_num [fiberRationalProfileRay,fiberRayById,lowMeanFractionReal]
      exact_mod_cast h14

end Erdos993Lean.Analytic.V213
