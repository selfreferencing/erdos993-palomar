module

public import Erdos993Lean.BCFG.WholePolynomial
public import Erdos993Lean.F4Fast.IntegerPolynomial
public import Mathlib.Data.Rat.Cast.CharZero

/-! Exact Horner semantics for the immutable integer source lists.
No new coefficient list, truncation, normalization or finite test is defined. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Erdos993Lean.BCFG.Analytic

def integerUniValue : List Int → ℝ → ℝ
  | [], _ => 0
  | a :: p, y => (a : ℝ) + y * integerUniValue p y

def integerBiValue : List (List Int) → ℝ → ℝ → ℝ
  | [], _, _ => 0
  | p :: ps, lam, y => integerUniValue p y + lam * integerBiValue ps lam y

theorem integerUniValue_eq_cast_eval (p : List Int) (y : ℝ) :
    integerUniValue p y = Uni.evalReal (IUni.castRat p) y := by
  induction p with
  | nil => rfl
  | cons a p ih =>
      simp only [integerUniValue, IUni.castRat, List.map_cons,
        Uni.evalReal, Rat.cast_intCast]
      rw [ih]
      rfl

theorem integerBiValue_eq_cast_eval (p : List (List Int)) (lam y : ℝ) :
    integerBiValue p lam y = Bi.evalReal (p.map IUni.castRat) lam y := by
  induction p with
  | nil => rfl
  | cons a p ih =>
      simp only [integerBiValue, List.map_cons, Bi.evalReal,
        integerUniValue_eq_cast_eval, ih]

end Erdos993Lean.BCFG.Analytic

#check Erdos993Lean.BCFG.Analytic.integerUniValue
#print axioms Erdos993Lean.BCFG.Analytic.integerUniValue
#check Erdos993Lean.BCFG.Analytic.integerBiValue
#print axioms Erdos993Lean.BCFG.Analytic.integerBiValue
#check Erdos993Lean.BCFG.Analytic.integerUniValue_eq_cast_eval
#print axioms Erdos993Lean.BCFG.Analytic.integerUniValue_eq_cast_eval
#check Erdos993Lean.BCFG.Analytic.integerBiValue_eq_cast_eval
#print axioms Erdos993Lean.BCFG.Analytic.integerBiValue_eq_cast_eval
