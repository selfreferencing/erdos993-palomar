module

public import Erdos993Lean.Analytic.V213.FiberPriceData

/-!
F16 exhaustive maximum checks on actual accepted component prices.
Every component is valid and at most the printed z, and an actual
component attains z.  Int/Nat cross-products are checked with
decide +kernel; the real consumers use the cast soundness theorem.

-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

def fiberPriceCheck (id : FiberInputIdentity) : Bool :=
  decide (lowMeanFractionValid (fiberInputPriceFraction id) ∧
    (fiberPriceGroupById (fiberInputPriceGroup id)).inputLo ≤ (fiberInputRouteById id).iota ∧
    (fiberInputRouteById id).iota ≤ (fiberPriceGroupById (fiberInputPriceGroup id)).inputHi) &&
  (fiberInputPriceComponents id).all (fun x =>
    decide (lowMeanFractionValid x ∧ lowMeanFractionLE x (fiberInputPriceFraction id))) &&
  (fiberInputPriceComponents id).any (fun x =>
    decide (lowMeanFractionEq x (fiberInputPriceFraction id)))

theorem fiber_price_checks :
    (List.range 55).all (fun k => fiberPriceCheck (fiberInputIdentityAt k)) = true := by
  decide +kernel

theorem fiber_price_named_checked (id : FiberInputIdentity) : fiberPriceCheck id = true := by
  have hk : fiberInputIndex id < 55 := by cases id <;> decide +kernel
  have he : fiberInputIdentityAt (fiberInputIndex id) = id := by cases id <;> rfl
  simpa only [he] using
    Erdos993Lean.F4Fast.forall_lt_of_range_all fiber_price_checks (fiberInputIndex id) hk

theorem fiber_price_valid (id : FiberInputIdentity) :
    lowMeanFractionValid (fiberInputPriceFraction id) := by
  have h := fiber_price_named_checked id
  simp only [fiberPriceCheck, Bool.and_eq_true] at h
  exact (of_decide_eq_true h.1.1).1

theorem fiber_price_component_le (id : FiberInputIdentity) {x : lowMeanFraction}
    (hx : x ∈ fiberInputPriceComponents id) :
    lowMeanFractionReal x ≤ lowMeanFractionReal (fiberInputPriceFraction id) := by
  have h := fiber_price_named_checked id
  simp only [fiberPriceCheck, Bool.and_eq_true] at h
  have ha := List.all_eq_true.mp h.1.2 x hx
  have hf := of_decide_eq_true ha
  exact (lowMean_fraction_le_iff hf.1 (fiber_price_valid id)).mp hf.2

theorem fiber_price_maximum_attained (id : FiberInputIdentity) :
    ∃ x ∈ fiberInputPriceComponents id,
      lowMeanFractionReal x = lowMeanFractionReal (fiberInputPriceFraction id) := by
  have h := fiber_price_named_checked id
  simp only [fiberPriceCheck, Bool.and_eq_true] at h
  rcases List.any_eq_true.mp h.2 with ⟨x,hx,he⟩
  have ha := List.all_eq_true.mp h.1.2 x hx
  have hv := (of_decide_eq_true ha).1
  exact ⟨x,hx,(lowMean_fraction_eq_iff hv (fiber_price_valid id)).mp (of_decide_eq_true he)⟩

theorem fiber_price_small_tail_le (id : FiberInputIdentity) :
    lowMeanFractionReal (fiberTailById (fiberInputTail id)).Z_a ≤
      lowMeanFractionReal (fiberInputPriceFraction id) := by
  apply fiber_price_component_le
  simp only [fiberInputPriceComponents, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, true_or, or_true]

theorem fiber_price_large_tail_le (id : FiberInputIdentity) :
    lowMeanFractionReal (fiberTailById (fiberInputTail id)).Z_small ≤
      lowMeanFractionReal (fiberInputPriceFraction id) := by
  apply fiber_price_component_le
  simp only [fiberInputPriceComponents, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, true_or, or_true]

theorem fiber_price_analytic_le (id : FiberAnalyticInputIdentity) :
    lowMeanFractionReal (fiberWeightById (fiberAnalyticWeight id)).eta_w ≤
      lowMeanFractionReal (fiberInputPriceFraction (fiberAnalyticInput id)) := by
  apply fiber_price_component_le
  cases id <;> simp [fiberInputPriceComponents, fiberAnalyticInput, fiberAnalyticWeight,
    fiberInputRouteById]

theorem fiber_price_window_le (id : FiberWindowInputIdentity) (wid : FiberWindowIdentity)
    (hw : wid ∈ fiberWindowInputWindows id) :
    lowMeanFractionReal (fiberWindowPriceFraction wid) ≤
      lowMeanFractionReal (fiberInputPriceFraction (fiberWindowInput id)) := by
  apply fiber_price_component_le
  cases id <;> cases wid <;>
    simp_all [fiberWindowInputWindows, fiberInputPriceComponents, fiberWindowInput]

end Erdos993Lean.Analytic.V213
