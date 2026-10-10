module

public import Erdos993Lean.Analytic.V213.FiberInputRateShape

/-!
Int/Nat certification of all41 actual input logarithms and all82
printed Eq97 endpoint guards. The same checked source leaves prove a
strict positive actual-rate lower bound through each analytic endpoint.
No Rat Boolean check or new trusted arithmetic primitive is used.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

instance fiberInputWeightDecidableEq : DecidableEq FiberWeightIdentity := by
  intro a b
  cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)

instance fiberInputProfileDecidableEq : DecidableEq FiberRationalProfileIdentity := by
  intro a b
  cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)

def fiberInputRateValid (id : FiberAnalyticInputIdentity) : Prop :=
  let r := fiberInputRouteById (fiberAnalyticInput id)
  let w := fiberWeightById (fiberAnalyticWeight id)
  let l := fiberInputLogById id
  lowMeanFractionValid r.ell0 ∧ lowMeanFractionValid w.ell_w ∧
  lowMeanFractionValid w.L_w ∧ lowMeanFractionValid r.mu0 ∧
  lowMeanFractionValid w.mu_w ∧ lowMeanFractionValid l.upper ∧
  lowMeanFractionValid (fiberInputHiFraction (fiberAnalyticInput id)) ∧
  lowMeanFractionValid w.guard_lo ∧ lowMeanFractionValid w.guard_hi ∧
  lowMeanFractionValid r.ts ∧ lowMeanFractionValid r.c ∧
  lowMeanFractionValid (fiberAnalyticEndFraction id) ∧
  lowMeanFractionValid l.gap_lo ∧ lowMeanFractionValid l.gap_hi

instance fiberInputRateValidDecidable (id : FiberAnalyticInputIdentity) :
    Decidable (fiberInputRateValid id) := by
  unfold fiberInputRateValid
  infer_instance

def fiberInputRateRoute (id : FiberAnalyticInputIdentity) : Prop :=
  let r := fiberInputRouteById (fiberAnalyticInput id)
  let w := fiberWeightById (fiberAnalyticWeight id)
  r.printed = fiberInputPrinted (fiberAnalyticInput id) ∧
  r.iota = fiberInputIndex (fiberAnalyticInput id) ∧
  r.weight = some (fiberAnalyticWeight id) ∧ r.profile = some w.profile ∧
  w.inputLo ≤ r.iota ∧ r.iota ≤ w.inputHi ∧
  0 ≤ (fiberInputHiFraction (fiberAnalyticInput id)).1 ∧
  0 ≤ (fiberInputLogById id).upper.1 ∧
  lowMeanFractionLE w.mu_w r.mu0 ∧ lowMeanFractionLE (0,1) w.guard_lo ∧
  lowMeanFractionLE w.guard_lo r.c ∧
  lowMeanFractionLE (fiberAnalyticEndFraction id) w.guard_hi

instance fiberInputRateRouteDecidable (id : FiberAnalyticInputIdentity) :
    Decidable (fiberInputRateRoute id) := by
  unfold fiberInputRateRoute
  infer_instance

def fiberInputRateTests (id : FiberAnalyticInputIdentity) : Prop :=
  let l := fiberInputLogById id
  let w := fiberWeightById (fiberAnalyticWeight id)
  let y := lowMeanFractionAdd (1,1) (fiberInputHiFraction (fiberAnalyticInput id))
  lowMeanFractionEq (lowMeanIntegerExprValue (fiberInputLogExpr id)) l.upper ∧
  lowMeanFractionLE ((2 : ℤ)^l.n,1) y ∧ lowMeanFractionLT y ((2 : ℤ)^(l.n+1),1) ∧
  lowMeanFractionEq l.gap_lo (fiberInputGuardFraction id w.guard_lo) ∧
  lowMeanFractionEq l.gap_hi (fiberInputGuardFraction id w.guard_hi) ∧
  lowMeanFractionLE w.guard_gap l.gap_lo ∧ lowMeanFractionLE w.guard_gap l.gap_hi ∧
  w.guard_gap = (1,100000) ∧
  lowMeanFractionLT (0,1) (fiberInputRateFraction id (fiberAnalyticEndFraction id))

instance fiberInputRateTestsDecidable (id : FiberAnalyticInputIdentity) :
    Decidable (fiberInputRateTests id) := by
  unfold fiberInputRateTests
  infer_instance

def fiberInputRateCheck (id : FiberAnalyticInputIdentity) : Bool :=
  lowMeanIntegerShapeCheck (fiberInputLogExpr id) (fiberInputLogShape id) &&
    decide (fiberInputRateValid id ∧ fiberInputRateRoute id ∧ fiberInputRateTests id)

theorem fiber_input_rate_checks :
    (List.range 41).all (fun k => fiberInputRateCheck (fiberAnalyticInputIdentityAt k)) = true := by
  decide +kernel

theorem fiber_input_rate_index_checked {k : ℕ} (hk : k < 41) :
    fiberInputRateCheck (fiberAnalyticInputIdentityAt k) = true :=
  Erdos993Lean.F4Fast.forall_lt_of_range_all fiber_input_rate_checks k hk

theorem fiber_input_rate_named_checked (id : FiberAnalyticInputIdentity) :
    fiberInputRateCheck id = true := by
  have hk : fiberAnalyticInputIndex id < 41 := by cases id <;> decide +kernel
  have hi : fiberAnalyticInputIdentityAt (fiberAnalyticInputIndex id) = id := by
    cases id <;> rfl
  have h := fiber_input_rate_index_checked hk
  rw [hi] at h
  exact h

theorem fiber_input_rate_facts (id : FiberAnalyticInputIdentity) :
    fiberInputRateValid id ∧ fiberInputRateRoute id ∧ fiberInputRateTests id := by
  have h := fiber_input_rate_named_checked id
  simp only [fiberInputRateCheck,Bool.and_eq_true] at h
  exact of_decide_eq_true h.2

theorem fiber_input_log_value (id : FiberAnalyticInputIdentity) :
    fiberInputLogValue id = lowMeanFractionReal (fiberInputLogById id).upper := by
  have h := fiber_input_rate_named_checked id
  simp only [fiberInputRateCheck,Bool.and_eq_true] at h
  have hs := lowMean_integerShape_sound h.1
  rw [fiber_input_log_shape_real] at hs
  have hf := fiber_input_rate_facts id
  have hv : lowMeanFractionValid (fiberInputLogById id).upper := hf.1.2.2.2.2.2.1
  have he := hf.2.2.1
  exact hs.2.trans ((lowMean_fraction_eq_iff hs.1 hv).mp he)

theorem fiber_input_log_upper (id : FiberAnalyticInputIdentity) :
    Real.log (1 + lowMeanFractionReal (fiberInputHiFraction (fiberAnalyticInput id))) ≤
      lowMeanFractionReal (fiberInputLogById id).upper := by
  have hf := fiber_input_rate_facts id
  have hyV : lowMeanFractionValid
      (lowMeanFractionAdd (1,1) (fiberInputHiFraction (fiberAnalyticInput id))) :=
    Nat.mul_pos (by norm_num [lowMeanFractionValid]) hf.1.2.2.2.2.2.2.1
  have hpV : lowMeanFractionValid ((2 : ℤ)^(fiberInputLogById id).n,1) := by
    norm_num [lowMeanFractionValid]
  have hbound := (lowMean_fraction_le_iff hpV hyV).mp hf.2.2.2.1
  rw [lowMean_fraction_add (by norm_num [lowMeanFractionValid]) hf.1.2.2.2.2.2.2.1] at hbound
  norm_num [lowMeanFractionReal] at hbound
  have h := fiber_dyadic_log_bound (fiberInputLogById id).n hbound
  exact h.trans_eq (fiber_input_log_value id)

theorem fiber_input_guard_endpoints (id : FiberAnalyticInputIdentity) :
    let r := fiberInputRouteById (fiberAnalyticInput id)
    let w := fiberWeightById (fiberAnalyticWeight id)
    (1 / 100000 : ℝ) ≤ lowMeanFractionReal r.ell0 - lowMeanFractionReal w.ell_w +
      (lowMeanFractionReal w.L_w - lowMeanFractionReal (fiberInputLogById id).upper) * lowMeanFractionReal w.guard_lo ∧
    (1 / 100000 : ℝ) ≤ lowMeanFractionReal r.ell0 - lowMeanFractionReal w.ell_w +
      (lowMeanFractionReal w.L_w - lowMeanFractionReal (fiberInputLogById id).upper) * lowMeanFractionReal w.guard_hi := by
  have hf := fiber_input_rate_facts id
  rcases hf.1 with ⟨he,hl,hL,hm,hmw,hU,hhi,htl,hth,hts,hc,hend,hgl,hgh⟩
  rcases hf.2.2 with ⟨hval,hylo,hyhi,heql,heqh,hbelow,hbehi,hgap,hpositive⟩
  have hguardV (t : lowMeanFraction) (ht : lowMeanFractionValid t) :
      lowMeanFractionValid (fiberInputGuardFraction id t) :=
    Nat.mul_pos (fiber_fraction_sub_valid he hl) (Nat.mul_pos (fiber_fraction_sub_valid hL hU) ht)
  have hglr := (lowMean_fraction_eq_iff hgl (hguardV _ htl)).mp heql
  have hghr := (lowMean_fraction_eq_iff hgh (hguardV _ hth)).mp heqh
  have hgapV : lowMeanFractionValid (fiberWeightById (fiberAnalyticWeight id)).guard_gap := by
    rw [hgap]; norm_num [lowMeanFractionValid]
  have hb1 := (lowMean_fraction_le_iff hgapV hgl).mp hbelow
  have hb2 := (lowMean_fraction_le_iff hgapV hgh).mp hbehi
  rw [hglr,fiber_input_guard_fraction_real id he hl hL hU htl,hgap] at hb1
  rw [hghr,fiber_input_guard_fraction_real id he hl hL hU hth,hgap] at hb2
  simpa only [lowMeanFractionReal,Int.cast_one,Nat.cast_ofNat] using And.intro hb1 hb2

theorem fiber_input_rate_endpoint_positive (id : FiberAnalyticInputIdentity) :
    0 < lowMeanFractionReal (fiberInputRouteById (fiberAnalyticInput id)).ell0 -
      lowMeanFractionReal (fiberInputLogById id).upper * lowMeanFractionReal (fiberAnalyticEndFraction id) := by
  have hf := fiber_input_rate_facts id
  rcases hf.1 with ⟨he,hl,hL,hm,hmw,hU,hhi,htl,hth,hts,hc,hend,hgl,hgh⟩
  have hv : lowMeanFractionValid (fiberInputRateFraction id (fiberAnalyticEndFraction id)) :=
    fiber_fraction_sub_valid he (Nat.mul_pos hU hend)
  have h := (lowMean_fraction_lt_iff (by norm_num [lowMeanFractionValid]) hv).mp hf.2.2.2.2.2.2.2.2.2.2
  rw [fiber_input_rate_fraction_real id he hU hend] at h
  simpa only [lowMeanFractionReal,Int.cast_zero,Nat.cast_one,zero_div] using h

end Erdos993Lean.Analytic.V213
