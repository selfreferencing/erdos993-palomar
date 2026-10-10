module

public import Erdos993Lean.Analytic.V213.FiberAffineScalarData

/-!
Reviewed F03 exponent budgets and squared root comparisons. The actual
record is keyed by its printed identity and checked against the independently
written five-term/slope formulas, named leaves and argument metadata. All
comparisons and equalities are Int/Nat cross-products; Range.all is proved
with decide +kernel and consumed through F4Fast. Real soundness follows.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

def fiberAffineExpectedTerms : FiberAffineScalarIdentity → List (String × lowMeanFraction)
  | .constant22 => [("F03:N>=22:constant:mean_correction", (1, 46)),
      ("F03:N>=22:constant:amplitude_h", (87, 460)),
      ("F03:N>=22:constant:xi_correction", (32, 14375)),
      ("F03:N>=22:constant:mass_error", (1, 40)),
      ("F03:N>=22:constant:root_correction", lowMeanFractionMul (3, 2) (47, 1725))]
  | .slope22 => [("F03:N>=22:slope:base_slope", (1, 2)),
      ("F03:N>=22:slope:root_correction", (47, 1725))]
  | .constant32 => [("F03:N>=32:constant:mean_correction", (1, 66)),
      ("F03:N>=32:constant:amplitude_h", (251, 1980)),
      ("F03:N>=32:constant:xi_correction", (32, 20625)),
      ("F03:N>=32:constant:mass_error", (1, 60)),
      ("F03:N>=32:constant:root_correction", lowMeanFractionMul (3, 2) (4, 165))]
  | .slope32 => [("F03:N>=32:slope:base_slope", (1, 2)),
      ("F03:N>=32:slope:root_correction", (4, 165))]
  | _ => []

def fiberAffineCanonicalLeft : FiberAffineScalarIdentity → lowMeanFraction
  | .root22 => (22, 23 ^ 2)
  | .root32 => (32, 33 ^ 2)
  | .inverseRootW => (2, 3)
  | id => (fiberAffineExpectedTerms id).foldr (fun x acc => lowMeanFractionAdd x.2 acc) (0, 1)

def fiberAffineCanonicalRight : FiberAffineScalarIdentity → lowMeanFraction
  | .constant22 => (3, 10)
  | .slope22 => (8, 15)
  | .constant32 => (1, 5)
  | .slope32 => (21, 40)
  | .root22 => lowMeanFractionPow (47, 230) 2
  | .root32 => lowMeanFractionPow (2, 11) 2
  | .inverseRootW => lowMeanFractionPow (5, 6) 2

def fiberAffineExpectedMinimum : FiberAffineScalarIdentity → Option ℕ
  | .constant22 | .slope22 | .root22 => some 22
  | .constant32 | .slope32 | .root32 => some 32
  | .inverseRootW => none

def fiberAffineExpectedArgument : FiberAffineScalarIdentity → Option lowMeanFraction
  | .root22 => some (22, 1)
  | .root32 => some (32, 1)
  | .inverseRootW => some (3, 2)
  | _ => none

def fiberAffineExpectedRoot : FiberAffineScalarIdentity → Option lowMeanFraction
  | .root22 => some (47, 230)
  | .root32 => some (2, 11)
  | .inverseRootW => some (5, 6)
  | _ => none

def fiberAffineStrict : FiberAffineScalarIdentity → Bool
  | .constant22 | .slope22 | .constant32 | .slope32 => true
  | _ => false

def fiberAffineTermCheck (x y : String × lowMeanFraction) : Bool :=
  decide (x.1 = y.1 ∧ 0 < x.2.2 ∧ 0 < y.2.2 ∧
    x.2.1 * (y.2.2 : ℤ) = y.2.1 * (x.2.2 : ℤ))

def fiberAffineScalarCheck (id : FiberAffineScalarIdentity) : Bool :=
  let x := fiberAffineScalarById id
  let a := fiberAffineCanonicalLeft id
  let b := fiberAffineCanonicalRight id
  decide (x.printed = fiberAffineScalarPrinted id ∧
    x.minimumN = fiberAffineExpectedMinimum id ∧
    x.argument = fiberAffineExpectedArgument id ∧ x.rootBound = fiberAffineExpectedRoot id ∧
    x.terms.length = (fiberAffineExpectedTerms id).length ∧
    (x.terms.zip (fiberAffineExpectedTerms id)).all (fun p => fiberAffineTermCheck p.1 p.2) = true ∧
    0 < x.left.2 ∧ 0 < x.right.2 ∧ 0 < a.2 ∧ 0 < b.2 ∧
    x.left.1 * (a.2 : ℤ) = a.1 * (x.left.2 : ℤ) ∧
    x.right.1 * (b.2 : ℤ) = b.1 * (x.right.2 : ℤ) ∧
    (if fiberAffineStrict id then x.left.1 * (x.right.2 : ℤ) < x.right.1 * (x.left.2 : ℤ)
      else x.left.1 * (x.right.2 : ℤ) ≤ x.right.1 * (x.left.2 : ℤ)))

theorem fiber_affine_scalar_checks :
    (List.range 7).all (fun k => fiberAffineScalarCheck (fiberAffineScalarIdentityAt k)) = true := by
  decide +kernel

theorem fiber_affine_scalar_checked {k : ℕ} (hk : k < 7) :
    fiberAffineScalarCheck (fiberAffineScalarIdentityAt k) = true :=
  Erdos993Lean.F4Fast.forall_lt_of_range_all fiber_affine_scalar_checks k hk

theorem fiber_affine_named_scalar_checked (id : FiberAffineScalarIdentity) :
    fiberAffineScalarCheck id = true := by
  cases id with
  | constant22 => exact fiber_affine_scalar_checked (k := 0) (by decide +kernel)
  | slope22 => exact fiber_affine_scalar_checked (k := 1) (by decide +kernel)
  | constant32 => exact fiber_affine_scalar_checked (k := 2) (by decide +kernel)
  | slope32 => exact fiber_affine_scalar_checked (k := 3) (by decide +kernel)
  | root22 => exact fiber_affine_scalar_checked (k := 4) (by decide +kernel)
  | root32 => exact fiber_affine_scalar_checked (k := 5) (by decide +kernel)
  | inverseRootW => exact fiber_affine_scalar_checked (k := 6) (by decide +kernel)

theorem fiber_affine_scalar_shape (id : FiberAffineScalarIdentity) :
    (fiberAffineScalarById id).printed = fiberAffineScalarPrinted id ∧
    (fiberAffineScalarById id).minimumN = fiberAffineExpectedMinimum id ∧
    (fiberAffineScalarById id).argument = fiberAffineExpectedArgument id ∧
    (fiberAffineScalarById id).rootBound = fiberAffineExpectedRoot id ∧
    (fiberAffineScalarById id).terms.length = (fiberAffineExpectedTerms id).length ∧
    ((fiberAffineScalarById id).terms.zip (fiberAffineExpectedTerms id)).all
      (fun p => fiberAffineTermCheck p.1 p.2) = true := by
  have h := of_decide_eq_true (fiber_affine_named_scalar_checked id)
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1⟩

theorem fiber_affine_scalar_sound (id : FiberAffineScalarIdentity) :
    if fiberAffineStrict id then
      lowMeanFractionReal (fiberAffineCanonicalLeft id) < lowMeanFractionReal (fiberAffineCanonicalRight id)
    else lowMeanFractionReal (fiberAffineCanonicalLeft id) ≤ lowMeanFractionReal (fiberAffineCanonicalRight id) := by
  have h := of_decide_eq_true (fiber_affine_named_scalar_checked id)
  rcases h with ⟨_,_,_,_,_,_,hl,hr,ha,hb,heL,heR,hcmp⟩
  have he1 := (lowMean_fraction_eq_iff hl ha).mp heL
  have he2 := (lowMean_fraction_eq_iff hr hb).mp heR
  cases hs : fiberAffineStrict id
  · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hcmp ⊢
    rw [←he1,←he2]
    exact (lowMean_fraction_le_iff hl hr).mp hcmp
  · simp only [hs, ↓reduceIte] at hcmp ⊢
    rw [←he1,←he2]
    exact (lowMean_fraction_lt_iff hl hr).mp hcmp

theorem fiber_affine_constant22 :
    (1/46 + 87/460 + 32/14375 + 1/40 + (3/2)*(47/1725) : ℝ) < 3/10 := by
  have h := fiber_affine_scalar_sound .constant22
  convert h using 1 <;> norm_num [fiberAffineStrict, fiberAffineCanonicalLeft,
    fiberAffineExpectedTerms, fiberAffineCanonicalRight, lowMeanFractionAdd, lowMeanFractionMul, lowMeanFractionReal]

theorem fiber_affine_slope22 : (1/2 + 47/1725 : ℝ) < 8/15 := by
  have h := fiber_affine_scalar_sound .slope22
  convert h using 1 <;> norm_num [fiberAffineStrict, fiberAffineCanonicalLeft,
    fiberAffineExpectedTerms, fiberAffineCanonicalRight, lowMeanFractionAdd, lowMeanFractionReal]

theorem fiber_affine_constant32 :
    (1/66 + 251/1980 + 32/20625 + 1/60 + (3/2)*(4/165) : ℝ) < 1/5 := by
  have h := fiber_affine_scalar_sound .constant32
  convert h using 1 <;> norm_num [fiberAffineStrict, fiberAffineCanonicalLeft,
    fiberAffineExpectedTerms, fiberAffineCanonicalRight, lowMeanFractionAdd, lowMeanFractionMul, lowMeanFractionReal]

theorem fiber_affine_slope32 : (1/2 + 4/165 : ℝ) < 21/40 := by
  have h := fiber_affine_scalar_sound .slope32
  convert h using 1 <;> norm_num [fiberAffineStrict, fiberAffineCanonicalLeft,
    fiberAffineExpectedTerms, fiberAffineCanonicalRight, lowMeanFractionAdd, lowMeanFractionReal]

theorem fiber_affine_root22_squared : (22/23^2 : ℝ) ≤ (47/230)^2 := by
  have h := fiber_affine_scalar_sound .root22
  convert h using 1 <;> norm_num [fiberAffineStrict, fiberAffineCanonicalLeft,
    fiberAffineCanonicalRight, lowMeanFractionPow, lowMeanFractionReal]

theorem fiber_affine_root32_squared : (32/33^2 : ℝ) ≤ (2/11)^2 := by
  have h := fiber_affine_scalar_sound .root32
  convert h using 1 <;> norm_num [fiberAffineStrict, fiberAffineCanonicalLeft,
    fiberAffineCanonicalRight, lowMeanFractionPow, lowMeanFractionReal]

theorem fiber_affine_inverse_root_squared : (2/3 : ℝ) ≤ (5/6)^2 := by
  have h := fiber_affine_scalar_sound .inverseRootW
  convert h using 1 <;> norm_num [fiberAffineStrict, fiberAffineCanonicalLeft,
    fiberAffineCanonicalRight, lowMeanFractionPow, lowMeanFractionReal]

end Erdos993Lean.Analytic.V213
