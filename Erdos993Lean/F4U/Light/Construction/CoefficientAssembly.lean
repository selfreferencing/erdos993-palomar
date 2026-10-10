module

public import Erdos993Lean.F4U.Light.Linking.Rational
public import Mathlib.Data.List.GetD

/-! Lossless coefficient assembly for the exact retained cancellation arrays.
Zero extension removes no interior coefficient or padding convention.  The
conclusion is the original `normalizedEq` / `checkReduction` predicate. -/

@[expose] public section

namespace F4Unified.LightConstruction.CoefficientAssembly
open F4U.Light.Linking
open F4U.Light.Linking.Polynomial2

def coefficient (p : Rows) (j i : Nat) : Int := (p.getD j []).getD i 0

theorem trimZ_eq_nil_of_coefficients_zero (p : List Int)
    (h : ∀ i, p.getD i 0 = 0) : F4U.Light.trimZ p = [] := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    have ha : a = 0 := by simpa using h 0
    have hp : ∀ i, p.getD i 0 = 0 := by
      intro i
      simpa only [List.getD_cons_succ] using h (i + 1)
    simp [F4U.Light.trimZ, ha, ih hp]

theorem trimZ_eq_of_coefficients_eq (p q : List Int)
    (h : ∀ i, p.getD i 0 = q.getD i 0) :
    F4U.Light.trimZ p = F4U.Light.trimZ q := by
  induction p generalizing q with
  | nil =>
    have hq : ∀ i, q.getD i 0 = 0 := by intro i; simpa using (h i).symm
    simpa [F4U.Light.trimZ] using (trimZ_eq_nil_of_coefficients_zero q hq).symm
  | cons a p ih =>
    cases q with
    | nil =>
      have hp : ∀ i, (a :: p).getD i 0 = 0 := by intro i; simpa using h i
      simpa [F4U.Light.trimZ] using trimZ_eq_nil_of_coefficients_zero (a :: p) hp
    | cons b q =>
      have hab : a = b := by simpa using h 0
      have hpq : ∀ i, p.getD i 0 = q.getD i 0 := by
        intro i
        simpa only [List.getD_cons_succ] using h (i + 1)
      simp only [F4U.Light.trimZ, hab, ih q hpq]

theorem trim_eq_nil_of_coefficients_zero (p : Rows)
    (h : ∀ j i, coefficient p j i = 0) : trim p = [] := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    have ha : F4U.Light.trimZ a = [] :=
      trimZ_eq_nil_of_coefficients_zero a (by
        intro i
        simpa [coefficient] using h 0 i)
    have hp : ∀ j i, coefficient p j i = 0 := by
      intro j i
      simpa only [coefficient, List.getD_cons_succ] using h (j + 1) i
    simp [trim, ha, ih hp]

theorem trim_eq_of_coefficients_eq (p q : Rows)
    (h : ∀ j i, coefficient p j i = coefficient q j i) : trim p = trim q := by
  induction p generalizing q with
  | nil =>
    have hq : ∀ j i, coefficient q j i = 0 := by
      intro j i
      simpa [coefficient] using (h j i).symm
    simpa [trim] using (trim_eq_nil_of_coefficients_zero q hq).symm
  | cons a p ih =>
    cases q with
    | nil =>
      have hp : ∀ j i, coefficient (a :: p) j i = 0 := by
        intro j i
        simpa [coefficient] using h j i
      simpa [trim] using trim_eq_nil_of_coefficients_zero (a :: p) hp
    | cons b q =>
      have hab : F4U.Light.trimZ a = F4U.Light.trimZ b :=
        trimZ_eq_of_coefficients_eq a b (by
          intro i
          simpa [coefficient] using h 0 i)
      have hpq : ∀ j i, coefficient p j i = coefficient q j i := by
        intro j i
        simpa only [coefficient, List.getD_cons_succ] using h (j + 1) i
      simp only [trim, hab, ih q hpq]

theorem normalizedEq_of_coefficients_eq (p q : Rows)
    (h : ∀ j i, coefficient p j i = coefficient q j i) : normalizedEq p q = true := by
  unfold normalizedEq
  exact decide_eq_true (trim_eq_of_coefficients_eq p q h)

theorem checkReduction_of_coefficients (c : Reduction) (hs : 0 < c.scale)
    (hN : ∀ j i,
      coefficient (Polynomial2.pscale c.scale c.raw.numerator) j i =
      coefficient (pmul c.factor c.reduced.numerator) j i)
    (hD : ∀ j i,
      coefficient (Polynomial2.pscale c.scale c.raw.denominator) j i =
      coefficient (pmul c.factor c.reduced.denominator) j i) :
    checkReduction c = true := by
  simp only [checkReduction, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨hs, normalizedEq_of_coefficients_eq _ _ hN⟩,
    normalizedEq_of_coefficients_eq _ _ hD⟩

#print axioms coefficient
#print axioms trimZ_eq_nil_of_coefficients_zero
#print axioms trimZ_eq_of_coefficients_eq
#print axioms trim_eq_nil_of_coefficients_zero
#print axioms trim_eq_of_coefficients_eq
#print axioms normalizedEq_of_coefficients_eq
#print axioms checkReduction_of_coefficients

end F4Unified.LightConstruction.CoefficientAssembly
