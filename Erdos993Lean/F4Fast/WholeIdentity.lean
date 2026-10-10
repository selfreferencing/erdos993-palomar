module

public import Erdos993Lean.BCFG.ExactPolynomial

/-!
Structural adapter for the original F4R-B whole-interval identities.
All lemmas
are generic over the original rational coefficient-list operations. The extra
trailing zero produced by identity-chart composition is retained until trim.
-/

@[expose] public section

set_option autoImplicit false

namespace Erdos993Lean.BCFG.Uni

/-- Scaling by one preserves every coefficient and the complete list shape. -/
theorem whole_scale_one (p : Uni) : scale 1 p = p := by
  induction p with
  | nil => rfl
  | cons a p ih => simp only [scale, one_mul, ih]

theorem whole_add_nil_right (p : Uni) : add p [] = p := by
  cases p <;> rfl

/-- A zero vector with the tail's length is shorter than this right list.
This exact shape is enough for the identity-chart multiplication proof. -/
theorem whole_add_scale_zero_cons (a : Rat) (p : Uni) :
    add (scale 0 p) (a :: p) = a :: p := by
  induction p generalizing a with
  | nil => rfl
  | cons b p ih => simp only [scale, zero_mul, add, zero_add, ih]

/-- The nonempty premise is carried by the displayed cons constructor. -/
theorem whole_mul_one_cons (a : Rat) (p : Uni) :
    mul [1] (a :: p) = a :: p := by
  change add (scale 1 (a :: p)) [0] = a :: p
  rw [whole_scale_one]
  simp only [add, add_zero, whole_add_nil_right]

/-- The original multiplication recursion pads even an empty right input. -/
theorem whole_mul_zero_one_nil : mul [0,1] [] = [0,0] := by rfl

/-- Multiplication by the identity monomial shifts a nonempty list exactly. -/
theorem whole_mul_zero_one_cons (a : Rat) (p : Uni) :
    mul [0,1] (a :: p) = 0 :: a :: p := by
  change add (scale 0 (a :: p)) (0 :: mul [1] (a :: p)) = 0 :: a :: p
  rw [whole_mul_one_cons]
  simp only [scale, zero_mul, add, zero_add, whole_add_scale_zero_cons]

/-- Identity-chart composition appends one zero to every nonempty input.
The statement is intentionally exact list equality, before applying trim. -/
theorem comp_zero_one_cons (a : Rat) (p : Uni) :
    comp (a :: p) [0,1] = (a :: p) ++ [0] := by
  induction p generalizing a with
  | nil =>
      change add [a] (mul [0,1] []) = [a,0]
      rw [whole_mul_zero_one_nil]
      simp only [add, add_zero]
  | cons b p ih =>
      change add [a] (mul [0,1] (comp (b :: p) [0,1])) = (a :: b :: p) ++ [0]
      rw [ih b]
      simp only [List.cons_append, whole_mul_zero_one_cons, add, add_zero]

/-- Appending one trailing zero leaves the original tail-first trim unchanged. -/
theorem trim_append_zero (p : Uni) : trim (p ++ [0]) = trim p := by
  induction p with
  | nil => simp [trim]
  | cons a p ih => simp only [List.cons_append, trim, ih]

/-- This includes the empty input and every original trailing-zero shape. -/
theorem trim_comp_zero_one (p : Uni) : trim (comp p [0,1]) = trim p := by
  cases p with
  | nil => rfl
  | cons a p => rw [comp_zero_one_cons, trim_append_zero]

/-- Exact original Boolean predicate; no coefficient computation is performed
by the proof body when this generic lemma is applied to a Bernstein vector. -/
theorem checkEq_comp_zero_one (p : Uni) : checkEq (comp p [0,1]) p = true := by
  unfold checkEq
  rw [trim_comp_zero_one]
  simp

end Erdos993Lean.BCFG.Uni

#print axioms Erdos993Lean.BCFG.Uni.trim_comp_zero_one
#print axioms Erdos993Lean.BCFG.Uni.checkEq_comp_zero_one
