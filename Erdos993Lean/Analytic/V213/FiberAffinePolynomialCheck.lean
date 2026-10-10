module

public import Erdos993Lean.Analytic.V213.FiberAffinePolynomialData

/-!
Remaining reviewed F03 controls are consumed by typed printed identities.
Canonical ascending coefficients and auxiliary expression operands are
independently specified. Every grouped check uses Int/Nat arithmetic and
decide +kernel, with F4Fast extraction. Real polynomial semantics and
closed-domain analytic extensions are proved in subsequent modules.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

def fiberAffinePolynomialCanonical : FiberAffinePolynomialIdentity → List lowMeanFraction
  | .a => [(7903,6250),(-34401,25000),(21,40)]
  | .v => [(-45819,12500),(201323,50000),(-63,80)]
  | .c => [(9,1),(0,1),(-9,8)]
  | .p => [(63,50),(-69,50),(21,40)]
  | .q => [(14,3),(-4,1),(4,5)]
  | .quarticLeft | .quarticRight => [(203,225),(937,75),(-10111,600),(1901,200),(-1457,800)]
  | .errorA => [(14,3125),(99,25000),(0,1)]
  | .errorQ => [(43,37500),(1323,50000),(1,80)]
  | .positiveQuadratic => [(12,1),(-17,1),(27,4)]
  | .discriminant => [(2132,1),(-2941,1),(1015,1)]

def fiberAffinePolynomialCheck (id : FiberAffinePolynomialIdentity) : Bool :=
  let x := fiberAffinePolynomialById id
  decide (x.printed = fiberAffinePolynomialPrinted id ∧
    x.coefficients = fiberAffinePolynomialCanonical id ∧
    x.coefficients.all (fun a => decide (0 < a.2)) = true)

theorem fiber_affine_polynomial_checks :
    (List.range 11).all (fun k => fiberAffinePolynomialCheck (fiberAffinePolynomialIdentityAt k)) = true := by
  decide +kernel

theorem fiber_affine_polynomial_checked {k : ℕ} (hk : k < 11) :
    fiberAffinePolynomialCheck (fiberAffinePolynomialIdentityAt k) = true :=
  Erdos993Lean.F4Fast.forall_lt_of_range_all fiber_affine_polynomial_checks k hk

theorem fiber_affine_named_polynomial_checked (id : FiberAffinePolynomialIdentity) :
    fiberAffinePolynomialCheck id = true := by
  cases id with
  | a => exact fiber_affine_polynomial_checked (k := 0) (by decide +kernel)
  | v => exact fiber_affine_polynomial_checked (k := 1) (by decide +kernel)
  | c => exact fiber_affine_polynomial_checked (k := 2) (by decide +kernel)
  | p => exact fiber_affine_polynomial_checked (k := 3) (by decide +kernel)
  | q => exact fiber_affine_polynomial_checked (k := 4) (by decide +kernel)
  | quarticLeft => exact fiber_affine_polynomial_checked (k := 5) (by decide +kernel)
  | quarticRight => exact fiber_affine_polynomial_checked (k := 6) (by decide +kernel)
  | errorA => exact fiber_affine_polynomial_checked (k := 7) (by decide +kernel)
  | errorQ => exact fiber_affine_polynomial_checked (k := 8) (by decide +kernel)
  | positiveQuadratic => exact fiber_affine_polynomial_checked (k := 9) (by decide +kernel)
  | discriminant => exact fiber_affine_polynomial_checked (k := 10) (by decide +kernel)

theorem fiber_affine_polynomial_binding (id : FiberAffinePolynomialIdentity) :
    (fiberAffinePolynomialById id).printed = fiberAffinePolynomialPrinted id ∧
    (fiberAffinePolynomialById id).coefficients = fiberAffinePolynomialCanonical id ∧
    (fiberAffinePolynomialById id).coefficients.all (fun a => decide (0 < a.2)) = true :=
  of_decide_eq_true (fiber_affine_named_polynomial_checked id)

def fiberAffineAuxiliaryCanonical : FiberAffineAuxiliaryIdentity → lowMeanFraction
  | .deficit => (4 * 1015 * 2132 - 2941 ^ 2,1)
  | .sqrt3 => (45,26)
  | .ratio => (91,81)
  | .ratioUpper => (9,8)
  | .vAt => (120459,200000)
  | .vUpper => (5,8)
  | .margin => (587,16200)
  | .required => (1,28)
  | .squareCoefficient => (27,4)
  | .squareShift => (-34,27)
  | .squareConstant => (35,27)

def fiberAffineAuxiliaryRelation (id : FiberAffineAuxiliaryIdentity) (x : lowMeanFraction) : Bool :=
  match id with
  | .deficit | .squareCoefficient | .squareConstant => decide (0 < x.1)
  | .sqrt3 => decide (x.1 ^ 2 ≤ (3 : ℤ) * (x.2 : ℤ) ^ 2)
  | .ratio => decide (x.1 * 8 < (9 : ℤ) * (x.2 : ℤ))
  | .vAt => decide (x.1 * 8 < (5 : ℤ) * (x.2 : ℤ))
  | .margin => decide ((x.2 : ℤ) < x.1 * 28)
  | _ => true

def fiberAffineAuxiliaryCheck (id : FiberAffineAuxiliaryIdentity) : Bool :=
  let x := fiberAffineAuxiliaryById id
  decide (x.1 = fiberAffineAuxiliaryPrinted id ∧ 0 < x.2.2 ∧
    x.2 = fiberAffineAuxiliaryCanonical id ∧ fiberAffineAuxiliaryRelation id x.2 = true)

theorem fiber_affine_auxiliary_checks :
    (List.range 11).all (fun k => fiberAffineAuxiliaryCheck (fiberAffineAuxiliaryIdentityAt k)) = true := by
  decide +kernel

theorem fiber_affine_auxiliary_checked {k : ℕ} (hk : k < 11) :
    fiberAffineAuxiliaryCheck (fiberAffineAuxiliaryIdentityAt k) = true :=
  Erdos993Lean.F4Fast.forall_lt_of_range_all fiber_affine_auxiliary_checks k hk

theorem fiber_affine_named_auxiliary_checked (id : FiberAffineAuxiliaryIdentity) :
    fiberAffineAuxiliaryCheck id = true := by
  cases id with
  | deficit => exact fiber_affine_auxiliary_checked (k := 0) (by decide +kernel)
  | sqrt3 => exact fiber_affine_auxiliary_checked (k := 1) (by decide +kernel)
  | ratio => exact fiber_affine_auxiliary_checked (k := 2) (by decide +kernel)
  | ratioUpper => exact fiber_affine_auxiliary_checked (k := 3) (by decide +kernel)
  | vAt => exact fiber_affine_auxiliary_checked (k := 4) (by decide +kernel)
  | vUpper => exact fiber_affine_auxiliary_checked (k := 5) (by decide +kernel)
  | margin => exact fiber_affine_auxiliary_checked (k := 6) (by decide +kernel)
  | required => exact fiber_affine_auxiliary_checked (k := 7) (by decide +kernel)
  | squareCoefficient => exact fiber_affine_auxiliary_checked (k := 8) (by decide +kernel)
  | squareShift => exact fiber_affine_auxiliary_checked (k := 9) (by decide +kernel)
  | squareConstant => exact fiber_affine_auxiliary_checked (k := 10) (by decide +kernel)

theorem fiber_affine_auxiliary_binding (id : FiberAffineAuxiliaryIdentity) :
    (fiberAffineAuxiliaryById id).1 = fiberAffineAuxiliaryPrinted id ∧
    0 < (fiberAffineAuxiliaryById id).2.2 ∧
    (fiberAffineAuxiliaryById id).2 = fiberAffineAuxiliaryCanonical id ∧
    fiberAffineAuxiliaryRelation id (fiberAffineAuxiliaryById id).2 = true :=
  of_decide_eq_true (fiber_affine_named_auxiliary_checked id)

noncomputable def fiberAffinePolynomialValue (id : FiberAffinePolynomialIdentity) (w : ℝ) : ℝ :=
  (fiberAffinePolynomialById id).coefficients.foldr (fun a rest => lowMeanFractionReal a + w * rest) 0

theorem fiber_affine_polynomial_value (id : FiberAffinePolynomialIdentity) (w : ℝ) :
    fiberAffinePolynomialValue id w =
      (fiberAffinePolynomialCanonical id).foldr (fun a rest => lowMeanFractionReal a + w * rest) 0 := by
  unfold fiberAffinePolynomialValue
  rw [(fiber_affine_polynomial_binding id).2.1]

theorem fiber_affine_discriminant_deficit : (0 : ℝ) < 4 * 1015 * 2132 - 2941 ^ 2 := by
  have h := (fiber_affine_auxiliary_binding .deficit).2.2.2
  have hi := of_decide_eq_true h
  have hc : (0 : ℤ) < 4 * 1015 * 2132 - 2941 ^ 2 := by
    rw [(fiber_affine_auxiliary_binding .deficit).2.2.1] at hi
    exact hi
  exact_mod_cast hc

theorem fiber_affine_sqrt3_squared : (45 / 26 : ℝ) ^ 2 ≤ 3 := by
  have h := (fiber_affine_auxiliary_binding .sqrt3).2.2.2
  have hi := of_decide_eq_true h
  rw [(fiber_affine_auxiliary_binding .sqrt3).2.2.1] at hi
  change (45 : ℤ) ^ 2 ≤ 3 * (26 : ℤ) ^ 2 at hi
  have hc : (45 : ℝ) ^ 2 ≤ 3 * (26 : ℝ) ^ 2 := by exact_mod_cast hi
  rw [div_pow]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < (26 : ℝ)^2)).2
  exact hc

theorem fiber_affine_curvature_ratio : (91 / 81 : ℝ) < 9 / 8 := by
  have h := (fiber_affine_auxiliary_binding .ratio).2.2.2
  have hi := of_decide_eq_true h
  have hc := (lowMean_fraction_lt_iff (x := (fiberAffineAuxiliaryById .ratio).2)
    (y := (9,8)) (fiber_affine_auxiliary_binding .ratio).2.1 (by change 0 < (8 : ℕ); decide +kernel)).mp hi
  convert hc using 1 <;> norm_num [fiberAffineAuxiliaryById,lowMeanFractionReal]

theorem fiber_affine_V_endpoint_upper : (120459 / 200000 : ℝ) < 5 / 8 := by
  have h := (fiber_affine_auxiliary_binding .vAt).2.2.2
  have hi := of_decide_eq_true h
  have hc := (lowMean_fraction_lt_iff (x := (fiberAffineAuxiliaryById .vAt).2)
    (y := (5,8)) (fiber_affine_auxiliary_binding .vAt).2.1 (by change 0 < (8 : ℕ); decide +kernel)).mp hi
  convert hc using 1 <;> norm_num [fiberAffineAuxiliaryById,lowMeanFractionReal]

theorem fiber_affine_final_margin : (1 / 28 : ℝ) < 587 / 16200 := by
  have h := (fiber_affine_auxiliary_binding .margin).2.2.2
  have hi := of_decide_eq_true h
  have hc := (lowMean_fraction_lt_iff (x := (1,28))
    (y := (fiberAffineAuxiliaryById .margin).2) (by change 0 < (28 : ℕ); decide +kernel)
    (fiber_affine_auxiliary_binding .margin).2.1).mp hi
  convert hc using 1 <;> norm_num [fiberAffineAuxiliaryById,lowMeanFractionReal]

end Erdos993Lean.Analytic.V213
