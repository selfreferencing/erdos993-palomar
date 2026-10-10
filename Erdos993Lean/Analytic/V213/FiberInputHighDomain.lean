module

public import Erdos993Lean.Analytic.V213.FiberInputTarget
public import Erdos993Lean.Analytic.V213.FiberInputDomain
public import Erdos993Lean.Analytic.V213.FiberWingComparison
public import Erdos993Lean.Analytic.V213.FiberOuterComparison

/-!
All55 actual input high-width routes. The selected fields come
from accepted F04/F05 records and actual F06 class identities, never a
replacement endpoint table. Whole closed original activity intervals
satisfy the printed skew and starting-mean ranges. In particular31--32
select W1,33--36 W2,37--39 W3, with equality mu0=mu_W at iota37.
Sources: Theorems 6.14/6.16/6.18.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

inductive FiberInputHighIdentity where
  | central
  | wing (id : FiberWingIdentity)
  | outer (id : FiberOuterClassIdentity)

def fiberInputHighOfClass : FiberInputClass → FiberInputHighIdentity
  | .central => .central
  | .w1 => .wing .w1
  | .w2 => .wing .w2
  | .w3 => .wing .w3
  | .c1 => .outer .c1
  | .c2 => .outer .c2
  | .c3 => .outer .c3
  | .c4 => .outer .c4
  | .c5 => .outer .c5
  | .c6 => .outer .c6
  | .c7 => .outer .c7
  | .c8 => .outer .c8

def fiberInputHighMean : FiberInputHighIdentity → lowMeanFraction
  | .central => (19,1)
  | .wing id => (fiberWingById id).mu_W
  | .outer id => (fiberOuterClassById id).mu_D

def fiberInputHighLo : FiberInputHighIdentity → lowMeanFraction
  | .central => (0,1)
  | .wing id => (fiberWingById id).skew_lower
  | .outer id => (fiberOuterClassById id).skew_lower

def fiberInputHighHi : FiberInputHighIdentity → lowMeanFraction
  | .central => (1,2)
  | .wing id => (fiberWingById id).skew_upper
  | .outer id => (fiberOuterClassById id).skew_upper

def fiberInputHighTau : FiberInputHighIdentity → lowMeanFraction
  | .central => (3,5)
  | .wing id => (fiberWingById id).tau
  | .outer id => (fiberOuterClassById id).tau

def fiberInputHighDomainTests (id : FiberInputIdentity) : Prop :=
  let route := fiberInputHighOfClass (fiberInputRouteById id).kind
  let lo := fiberInputSignedSkewFraction (fiberInputQloFraction id)
  let hi := fiberInputSignedSkewFraction (fiberInputQhiFraction id)
  lowMeanFractionValid (fiberInputHighLo route) ∧ lowMeanFractionValid (fiberInputHighMean route) ∧
  lowMeanFractionValid (fiberInputHighHi route) ∧
  lowMeanFractionLE (fiberInputHighMean route) (fiberInputRouteById id).mu0 ∧
  lowMeanFractionLE (lowMeanFractionAbs lo) (fiberInputHighHi route) ∧
  lowMeanFractionLE (lowMeanFractionAbs hi) (fiberInputHighHi route) ∧
  (lowMeanFractionEq (fiberInputHighLo route) (0,1) ∨
    lowMeanFractionLE (fiberInputHighLo route) lo ∨
    lowMeanFractionLE hi (lowMeanFractionNeg (fiberInputHighLo route)))

instance fiberInputHighDomainTestsDecidable (id : FiberInputIdentity) :
    Decidable (fiberInputHighDomainTests id) := by
  unfold fiberInputHighDomainTests
  infer_instance

theorem fiber_input_high_domain_checks :
    (List.range 55).all (fun k => decide (fiberInputHighDomainTests (fiberInputIdentityAt k))) = true := by
  decide +kernel

theorem fiber_input_high_domain_facts (id : FiberInputIdentity) : fiberInputHighDomainTests id := by
  have hk : fiberInputIndex id < 55 := by cases id <;> decide +kernel
  have hi : fiberInputIdentityAt (fiberInputIndex id) = id := by cases id <;> rfl
  have h := Erdos993Lean.F4Fast.forall_lt_of_range_all fiber_input_high_domain_checks (fiberInputIndex id) hk
  rw [hi] at h
  exact of_decide_eq_true h

theorem fiber_input_high_mean (id : FiberInputIdentity) {mu : ℝ}
    (hmu : lowMeanFractionReal (fiberInputRouteById id).mu0 ≤ mu) :
    lowMeanFractionReal (fiberInputHighMean (fiberInputHighOfClass (fiberInputRouteById id).kind)) ≤ mu := by
  have h := fiber_input_high_domain_facts id
  have hd := fiber_input_domain_facts id
  have hv := hd.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact ((lowMean_fraction_le_iff h.2.1 hv).mp h.2.2.2.1).trans hmu

theorem fiber_input_high_skew (id : FiberInputIdentity) {lambda : ℝ}
    (hl : lowMeanFractionReal (fiberInputLoFraction id) ≤ lambda)
    (hh : lambda ≤ lowMeanFractionReal (fiberInputHiFraction id)) :
    lowMeanFractionReal (fiberInputHighLo (fiberInputHighOfClass (fiberInputRouteById id).kind)) ≤
        |fiberSkew (FreeCountVariance.q lambda)| ∧
    |fiberSkew (FreeCountVariance.q lambda)| ≤ lowMeanFractionReal
        (fiberInputHighHi (fiberInputHighOfClass (fiberInputRouteById id).kind)) := by
  have h := fiber_input_high_domain_facts id
  have hd := fiber_input_domain_facts id
  have hq := fiber_input_q_interval id hl hh
  have hloV : lowMeanFractionValid (fiberInputSignedSkewFraction (fiberInputQloFraction id)) :=
    fiber_fraction_sub_valid (Nat.mul_pos (by norm_num [lowMeanFractionValid]) hd.2.2.1) (by norm_num [lowMeanFractionValid])
  have hhiV : lowMeanFractionValid (fiberInputSignedSkewFraction (fiberInputQhiFraction id)) :=
    fiber_fraction_sub_valid (Nat.mul_pos (by norm_num [lowMeanFractionValid]) hd.2.2.2.1) (by norm_num [lowMeanFractionValid])
  have hloAbsV : lowMeanFractionValid (lowMeanFractionAbs (fiberInputSignedSkewFraction
      (fiberInputQloFraction id))) := hloV
  have hhiAbsV : lowMeanFractionValid (lowMeanFractionAbs (fiberInputSignedSkewFraction
      (fiberInputQhiFraction id))) := hhiV
  have hloR := (lowMean_fraction_le_iff hloAbsV h.2.2.1).mp h.2.2.2.2.1
  have hhiR := (lowMean_fraction_le_iff hhiAbsV h.2.2.1).mp h.2.2.2.2.2.1
  rw [lowMean_fraction_abs,fiber_input_signed_skew_real hd.2.2.1] at hloR
  rw [lowMean_fraction_abs,fiber_input_signed_skew_real hd.2.2.2.1] at hhiR
  have hu := (fiber_input_whole_skew id hl hh).trans (max_le hloR hhiR)
  refine ⟨?_,hu⟩
  rcases h.2.2.2.2.2.2 with hz | hp | hn
  · have he := (lowMean_fraction_eq_iff h.1 (by norm_num [lowMeanFractionValid])).mp hz
    have hzR : lowMeanFractionReal (0,1) = (0 : ℝ) := by norm_num [lowMeanFractionReal]
    rw [hzR] at he
    rw [he]
    exact abs_nonneg _
  · have he := (lowMean_fraction_le_iff h.1 hloV).mp hp
    rw [fiber_input_signed_skew_real hd.2.2.1] at he
    have hmono : fiberSkew (lowMeanFractionReal (fiberInputQloFraction id)) ≤
        fiberSkew (FreeCountVariance.q lambda) := by unfold fiberSkew; linarith only [hq.1]
    exact (he.trans hmono).trans (le_abs_self _)
  · have hnegV : lowMeanFractionValid (lowMeanFractionNeg
        (fiberInputHighLo (fiberInputHighOfClass (fiberInputRouteById id).kind))) := h.1
    have he := (lowMean_fraction_le_iff hhiV hnegV).mp hn
    rw [fiber_input_signed_skew_real hd.2.2.2.1,lowMean_fraction_neg] at he
    have hmono : fiberSkew (FreeCountVariance.q lambda) ≤
        fiberSkew (lowMeanFractionReal (fiberInputQhiFraction id)) := by
      unfold fiberSkew; linarith only [hq.2]
    have hneg := neg_abs_le (fiberSkew (FreeCountVariance.q lambda))
    linarith only [hneg,hmono,he]

theorem fiber_input_high_tau (id : FiberInputIdentity) :
    lowMeanFractionReal (fiberInputHighTau (fiberInputHighOfClass (fiberInputRouteById id).kind)) =
      lowMeanFractionReal (fiberInputRouteById id).ts := by
  cases id <;> norm_num [fiberInputHighTau,fiberInputHighOfClass,fiberInputRouteById,
    fiberWingById,fiberOuterClassById,lowMeanFractionReal]

theorem fiber_input_mean_nineteen (id : FiberInputIdentity) {mu : ℝ}
    (hmu : lowMeanFractionReal (fiberInputRouteById id).mu0 ≤ mu) : 19 ≤ mu := by
  have h : (19 : ℝ) ≤ lowMeanFractionReal (fiberInputRouteById id).mu0 := by
    cases id <;> norm_num [fiberInputRouteById,lowMeanFractionReal]
  exact h.trans hmu

end Erdos993Lean.Analytic.V213
