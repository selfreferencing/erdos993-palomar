module

public import Erdos993Lean.Analytic.V213.FiberWindowInputData
public import Erdos993Lean.Analytic.V213.FiberInputDomain
public import Erdos993Lean.Analytic.V213.FiberInputTarget
public import Erdos993Lean.Analytic.V213.FiberWindowNamedDeficit

/-!
Exact seventeen-input window routing and whole closed activity
interval guards. Absolute-skew extrema, lower skew sign, actual class
mean and exact target identity are discharged from actual F06/Params.

-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

def fiberWindowInputClass (id : FiberWindowInputIdentity) : FiberOuterClassIdentity :=
  (fiberInputOuterClass (fiberInputRouteById (fiberWindowInput id)).kind).getD .c1

def fiberWindowInputDomainTests (id : FiberWindowInputIdentity) : Prop :=
  let input := fiberWindowInput id
  let c := fiberOuterClassById (fiberWindowInputClass id)
  let lo := fiberInputSignedSkewFraction (fiberInputQloFraction input)
  let hi := fiberInputSignedSkewFraction (fiberInputQhiFraction input)
  lowMeanFractionValid c.skew_lower ∧ lowMeanFractionValid c.mu_D ∧ lowMeanFractionValid c.skew_upper ∧
  lowMeanFractionLE c.mu_D (fiberInputRouteById input).mu0 ∧
  lowMeanFractionLE (lowMeanFractionAbs lo) c.skew_upper ∧ lowMeanFractionLE (lowMeanFractionAbs hi) c.skew_upper ∧
  (lowMeanFractionEq c.skew_lower (0,1) ∨ lowMeanFractionLE c.skew_lower lo ∨
    lowMeanFractionLE hi (lowMeanFractionNeg c.skew_lower))

instance fiberWindowInputDomainTestsDecidable (id : FiberWindowInputIdentity) :
    Decidable (fiberWindowInputDomainTests id) := by unfold fiberWindowInputDomainTests; infer_instance

theorem fiber_window_input_domain_checks :
    (List.range 17).all (fun k => decide (fiberWindowInputDomainTests (fiberWindowInputIdentityAt k))) = true := by
  decide +kernel

theorem fiber_window_input_domain_facts (id : FiberWindowInputIdentity) : fiberWindowInputDomainTests id := by
  have hk : fiberWindowInputIndex id < 17 := by cases id <;> decide +kernel
  have hi : fiberWindowInputIdentityAt (fiberWindowInputIndex id) = id := by cases id <;> rfl
  have h := Erdos993Lean.F4Fast.forall_lt_of_range_all fiber_window_input_domain_checks _ hk
  rw [hi] at h
  exact of_decide_eq_true h

theorem fiber_window_input_class (id : FiberWindowInputIdentity) (wid : FiberWindowIdentity)
    (hw : wid ∈ fiberWindowInputWindows id) :
    (fiberWindowById wid).outerClass = fiberWindowInputClass id := by
  cases id <;> cases wid <;> simp [fiberWindowInputWindows] at hw <;> rfl

theorem fiber_window_input_target (id : FiberWindowInputIdentity) (wid : FiberWindowIdentity)
    (hw : wid ∈ fiberWindowInputWindows id) : fiberWindowTarget wid = fiberInputTarget (fiberWindowInput id) := by
  cases id <;> cases wid <;> simp [fiberWindowInputWindows] at hw <;> rfl

theorem fiber_window_input_mean (id : FiberWindowInputIdentity) {mu : ℝ}
    (hmu : lowMeanFractionReal (fiberInputRouteById (fiberWindowInput id)).mu0 ≤ mu) :
    lowMeanFractionReal (fiberOuterClassById (fiberWindowInputClass id)).mu_D ≤ mu := by
  have h := fiber_window_input_domain_facts id
  have hv := (fiber_input_domain_facts (fiberWindowInput id)).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact ((lowMean_fraction_le_iff h.2.1 hv).mp h.2.2.2.1).trans hmu

theorem fiber_window_input_skew (id : FiberWindowInputIdentity) {lambda : ℝ}
    (hl : lowMeanFractionReal (fiberInputLoFraction (fiberWindowInput id)) ≤ lambda)
    (hh : lambda ≤ lowMeanFractionReal (fiberInputHiFraction (fiberWindowInput id))) :
    lowMeanFractionReal (fiberOuterClassById (fiberWindowInputClass id)).skew_lower ≤
        |fiberSkew (FreeCountVariance.q lambda)| ∧
    |fiberSkew (FreeCountVariance.q lambda)| ≤ lowMeanFractionReal
        (fiberOuterClassById (fiberWindowInputClass id)).skew_upper := by
  have h := fiber_window_input_domain_facts id
  have hd := fiber_input_domain_facts (fiberWindowInput id)
  have hq := fiber_input_q_interval (fiberWindowInput id) hl hh
  have hloV : lowMeanFractionValid (fiberInputSignedSkewFraction (fiberInputQloFraction (fiberWindowInput id))) :=
    fiber_fraction_sub_valid (Nat.mul_pos (by norm_num [lowMeanFractionValid]) hd.2.2.1) (by norm_num [lowMeanFractionValid])
  have hhiV : lowMeanFractionValid (fiberInputSignedSkewFraction (fiberInputQhiFraction (fiberWindowInput id))) :=
    fiber_fraction_sub_valid (Nat.mul_pos (by norm_num [lowMeanFractionValid]) hd.2.2.2.1) (by norm_num [lowMeanFractionValid])
  have hloAbsV : lowMeanFractionValid (lowMeanFractionAbs (fiberInputSignedSkewFraction
      (fiberInputQloFraction (fiberWindowInput id)))) := hloV
  have hhiAbsV : lowMeanFractionValid (lowMeanFractionAbs (fiberInputSignedSkewFraction
      (fiberInputQhiFraction (fiberWindowInput id)))) := hhiV
  have hloR := (lowMean_fraction_le_iff hloAbsV h.2.2.1).mp h.2.2.2.2.1
  have hhiR := (lowMean_fraction_le_iff hhiAbsV h.2.2.1).mp h.2.2.2.2.2.1
  rw [lowMean_fraction_abs,fiber_input_signed_skew_real hd.2.2.1] at hloR
  rw [lowMean_fraction_abs,fiber_input_signed_skew_real hd.2.2.2.1] at hhiR
  have hu := (fiber_input_whole_skew (fiberWindowInput id) hl hh).trans (max_le hloR hhiR)
  refine ⟨?_,hu⟩
  rcases h.2.2.2.2.2.2 with hz | hp | hn
  · have he := (lowMean_fraction_eq_iff h.1 (by norm_num [lowMeanFractionValid])).mp hz
    have hzR : lowMeanFractionReal (0,1) = (0 : ℝ) := by norm_num [lowMeanFractionReal]
    rw [hzR] at he
    rw [he]
    exact abs_nonneg _
  · have he := (lowMean_fraction_le_iff h.1 hloV).mp hp
    rw [fiber_input_signed_skew_real hd.2.2.1] at he
    have hmono : fiberSkew (lowMeanFractionReal (fiberInputQloFraction (fiberWindowInput id))) ≤
        fiberSkew (FreeCountVariance.q lambda) := by unfold fiberSkew; linarith only [hq.1]
    exact (he.trans hmono).trans (le_abs_self _)
  · have hnegV : lowMeanFractionValid (lowMeanFractionNeg
        (fiberOuterClassById (fiberWindowInputClass id)).skew_lower) := h.1
    have he := (lowMean_fraction_le_iff hhiV hnegV).mp hn
    rw [fiber_input_signed_skew_real hd.2.2.2.1,lowMean_fraction_neg] at he
    have hmono : fiberSkew (FreeCountVariance.q lambda) ≤
        fiberSkew (lowMeanFractionReal (fiberInputQhiFraction (fiberWindowInput id))) := by
      unfold fiberSkew; linarith only [hq.2]
    have hneg := neg_abs_le (fiberSkew (FreeCountVariance.q lambda))
    linarith only [hneg,hmono,he]

end Erdos993Lean.Analytic.V213
