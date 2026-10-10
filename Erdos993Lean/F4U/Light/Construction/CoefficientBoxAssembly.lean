module

public import Erdos993Lean.F4U.Light.Construction.CoefficientAssembly

/-! Finite support of the same complete integer coefficient objects.
The two bounds are the explicit row/column supports consumed immediately by
the coefficient-family assembly.  They do not replace any polynomial input. -/

@[expose] public section

namespace F4Unified.LightConstruction.CoefficientBoxAssembly
open F4U.Light.Linking
open F4U.Light.Linking.Polynomial2
open CoefficientAssembly

def width : Rows → Nat
  | [] => 0
  | a :: p => max a.length (width p)

theorem row_length_le_width (p : Rows) (j : Nat) : (p.getD j []).length ≤ width p := by
  induction p generalizing j with
  | nil => simp [width]
  | cons a p ih =>
    cases j with
    | zero => simp [width]
    | succ j =>
      simpa only [List.getD_cons_succ, width] using
        le_trans (ih j) (Nat.le_max_right a.length (width p))

theorem coefficient_zero_of_outer (p : Rows) {j i : Nat} (h : p.length ≤ j) :
    coefficient p j i = 0 := by
  unfold coefficient
  rw [List.getD_eq_default _ _ h]
  simp

theorem coefficient_zero_of_inner (p : Rows) {j i : Nat} (h : width p ≤ i) :
    coefficient p j i = 0 := by
  unfold coefficient
  exact List.getD_eq_default _ _ (le_trans (row_length_le_width p j) h)

theorem coefficients_eq_of_box (p q : Rows) (rows columns : Nat)
    (hpRows : p.length ≤ rows) (hqRows : q.length ≤ rows)
    (hpColumns : width p ≤ columns) (hqColumns : width q ≤ columns)
    (h : ∀ j : Fin rows, ∀ i : Fin columns,
      coefficient p j.val i.val = coefficient q j.val i.val) :
    ∀ j i : Nat, coefficient p j i = coefficient q j i := by
  intro j i
  by_cases hj : j < rows
  · by_cases hi : i < columns
    · exact h ⟨j, hj⟩ ⟨i, hi⟩
    · have hci : columns ≤ i := Nat.le_of_not_gt hi
      rw [coefficient_zero_of_inner p (le_trans hpColumns hci),
        coefficient_zero_of_inner q (le_trans hqColumns hci)]
  · have hrj : rows ≤ j := Nat.le_of_not_gt hj
    rw [coefficient_zero_of_outer p (le_trans hpRows hrj),
      coefficient_zero_of_outer q (le_trans hqRows hrj)]

theorem normalizedEq_of_box (p q : Rows) (rows columns : Nat)
    (hpRows : p.length ≤ rows) (hqRows : q.length ≤ rows)
    (hpColumns : width p ≤ columns) (hqColumns : width q ≤ columns)
    (h : ∀ j : Fin rows, ∀ i : Fin columns,
      coefficient p j.val i.val = coefficient q j.val i.val) :
    normalizedEq p q = true :=
  normalizedEq_of_coefficients_eq p q
    (coefficients_eq_of_box p q rows columns hpRows hqRows hpColumns hqColumns h)

theorem checkReduction_of_boxes (c : Reduction) (hs : 0 < c.scale)
    (nRows nColumns dRows dColumns : Nat)
    (hnRawRows : (Polynomial2.pscale c.scale c.raw.numerator).length ≤ nRows)
    (hnNewRows : (pmul c.factor c.reduced.numerator).length ≤ nRows)
    (hnRawColumns : width (Polynomial2.pscale c.scale c.raw.numerator) ≤ nColumns)
    (hnNewColumns : width (pmul c.factor c.reduced.numerator) ≤ nColumns)
    (hdRawRows : (Polynomial2.pscale c.scale c.raw.denominator).length ≤ dRows)
    (hdNewRows : (pmul c.factor c.reduced.denominator).length ≤ dRows)
    (hdRawColumns : width (Polynomial2.pscale c.scale c.raw.denominator) ≤ dColumns)
    (hdNewColumns : width (pmul c.factor c.reduced.denominator) ≤ dColumns)
    (hN : ∀ j : Fin nRows, ∀ i : Fin nColumns,
      coefficient (Polynomial2.pscale c.scale c.raw.numerator) j.val i.val =
      coefficient (pmul c.factor c.reduced.numerator) j.val i.val)
    (hD : ∀ j : Fin dRows, ∀ i : Fin dColumns,
      coefficient (Polynomial2.pscale c.scale c.raw.denominator) j.val i.val =
      coefficient (pmul c.factor c.reduced.denominator) j.val i.val) :
    checkReduction c = true :=
  checkReduction_of_coefficients c hs
    (coefficients_eq_of_box _ _ nRows nColumns
      hnRawRows hnNewRows hnRawColumns hnNewColumns hN)
    (coefficients_eq_of_box _ _ dRows dColumns
      hdRawRows hdNewRows hdRawColumns hdNewColumns hD)

#print axioms width
#print axioms row_length_le_width
#print axioms coefficient_zero_of_outer
#print axioms coefficient_zero_of_inner
#print axioms coefficients_eq_of_box
#print axioms normalizedEq_of_box
#print axioms checkReduction_of_boxes

end F4Unified.LightConstruction.CoefficientBoxAssembly
