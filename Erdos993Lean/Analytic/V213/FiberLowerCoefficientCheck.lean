module

public import Erdos993Lean.Analytic.V213.FiberLowerCoefficientData

/-!
Accepted F02: explicit Int/Nat cross-products bind each leaf to the
literal Eq83 coefficient at sqrt(t0)=11/10,z=1/19 and its printed bound.
The six checks use Range.all, decide +kernel and the accepted F4Fast bridge.
Typed printed identities remain authoritative; positions only enumerate checks.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

def fiberLowerCoefficientCanonical : FiberLowerCoefficientIdentity → lowMeanFraction
  | .a0 => lowMeanFractionAdd
      (lowMeanFractionMul (9, 2) (lowMeanFractionPow (lowMeanFractionAdd (121, 100) (-1, 1)) 2))
      (2, 19)
  | .a1 => lowMeanFractionAdd (lowMeanFractionAdd (lowMeanFractionAdd
      (lowMeanFractionAdd (-121, 100) (-2, 19)) (lowMeanFractionPow (10, 11) 3))
      (lowMeanFractionMul (-3, 19) (lowMeanFractionPow (10, 11) 5)))
      (lowMeanFractionMul (-10, 361) (lowMeanFractionPow (10, 11) 7))
  | .a2 => lowMeanFractionMul (1, 2) (lowMeanFractionAdd (lowMeanFractionPow (10, 11) 3)
      (lowMeanFractionMul (2, 19) (lowMeanFractionPow (10, 11) 5)))
  | .v0 => lowMeanFractionMul (9, 1) (lowMeanFractionAdd (121, 100) (-1, 1))
  | .v1 => lowMeanFractionAdd (lowMeanFractionAdd (lowMeanFractionAdd (-1, 1)
      (lowMeanFractionMul (-3, 2) (lowMeanFractionPow (10, 11) 5)))
      (lowMeanFractionMul (15, 38) (lowMeanFractionPow (10, 11) 7)))
      (lowMeanFractionMul (35, 361) (lowMeanFractionPow (10, 11) 9))
  | .v2 => lowMeanFractionMul (1, 2) (lowMeanFractionAdd
      (lowMeanFractionMul (-3, 2) (lowMeanFractionPow (10, 11) 5))
      (lowMeanFractionMul (-5, 19) (lowMeanFractionPow (10, 11) 7)))

def fiberLowerCoefficientRelation (id : FiberLowerCoefficientIdentity) (x : lowMeanFraction) : Bool :=
  match id with
  | .a0 | .a1 | .a2 => decide ((0 : ℤ) * (x.2 : ℤ) < x.1 * 1)
  | .v0 => decide (x.1 * 1 = (0 : ℤ) * (x.2 : ℤ))
  | .v1 => decide ((0 : ℤ) * (x.2 : ℤ) ≤ x.1 * 1 ∧ x.1 * 10000 ≤ 3 * (x.2 : ℤ))
  | .v2 => decide ((-3 : ℤ) * (x.2 : ℤ) ≤ x.1 * 10000 ∧ x.1 * 1 ≤ (0 : ℤ) * (x.2 : ℤ))

def fiberLowerCoefficientCheck (id : FiberLowerCoefficientIdentity) : Bool :=
  let x := fiberLowerCoefficientById id
  let c := fiberLowerCoefficientCanonical id
  let d := lowMeanFractionAdd x.actual (lowMeanFractionNeg x.bound)
  decide (0 < x.actual.2 ∧ 0 < x.bound.2 ∧
    0 < x.difference.2 ∧ 0 < c.2 ∧ 0 < d.2 ∧
    x.actual.1 * (c.2 : ℤ) = c.1 * (x.actual.2 : ℤ) ∧
    x.difference.1 * (d.2 : ℤ) = d.1 * (x.difference.2 : ℤ) ∧
    x.sqrtPoint = (11, 10) ∧ x.reciprocalMean = (1, 19) ∧
    fiberLowerCoefficientRelation id x.difference = true)

theorem fiber_lower_coefficient_checks :
    (List.range 6).all (fun k => fiberLowerCoefficientCheck (fiberLowerCoefficientIdentityAt k)) = true := by
  decide +kernel

theorem fiber_lower_coefficient_checked {k : ℕ} (hk : k < 6) :
    fiberLowerCoefficientCheck (fiberLowerCoefficientIdentityAt k) = true :=
  Erdos993Lean.F4Fast.forall_lt_of_range_all fiber_lower_coefficient_checks k hk

theorem fiber_lower_named_coefficient_checked (id : FiberLowerCoefficientIdentity) :
    fiberLowerCoefficientCheck id = true := by
  cases id with
  | a0 => exact fiber_lower_coefficient_checked (k := 0) (by decide +kernel)
  | a1 => exact fiber_lower_coefficient_checked (k := 1) (by decide +kernel)
  | a2 => exact fiber_lower_coefficient_checked (k := 2) (by decide +kernel)
  | v0 => exact fiber_lower_coefficient_checked (k := 3) (by decide +kernel)
  | v1 => exact fiber_lower_coefficient_checked (k := 4) (by decide +kernel)
  | v2 => exact fiber_lower_coefficient_checked (k := 5) (by decide +kernel)

theorem fiber_lower_coefficient_canonical_sound (id : FiberLowerCoefficientIdentity) :
    lowMeanFractionReal (fiberLowerCoefficientById id).actual =
      lowMeanFractionReal (fiberLowerCoefficientCanonical id) := by
  have h := of_decide_eq_true (fiber_lower_named_coefficient_checked id)
  exact (lowMean_fraction_eq_iff h.1 h.2.2.2.1).mp h.2.2.2.2.2.1

theorem fiber_lower_coefficient_difference_sound (id : FiberLowerCoefficientIdentity) :
    lowMeanFractionReal (fiberLowerCoefficientById id).difference =
      lowMeanFractionReal (fiberLowerCoefficientById id).actual -
        lowMeanFractionReal (fiberLowerCoefficientById id).bound := by
  have h := of_decide_eq_true (fiber_lower_named_coefficient_checked id)
  have he := (lowMean_fraction_eq_iff h.2.2.1 h.2.2.2.2.1).mp h.2.2.2.2.2.2.1
  rw [he, lowMean_fraction_add h.1]
  · rw [lowMean_fraction_neg]
    ring
  · exact h.2.1

theorem fiber_lower_coefficient_points :
    ∀ id, (fiberLowerCoefficientById id).sqrtPoint = (11, 10) ∧
      (fiberLowerCoefficientById id).reciprocalMean = (1, 19) := by
  intro id
  have h := of_decide_eq_true (fiber_lower_named_coefficient_checked id)
  exact ⟨h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1⟩

end Erdos993Lean.Analytic.V213
