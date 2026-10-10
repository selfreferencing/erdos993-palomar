module

public import Erdos993Lean.Analytic.V213.LowMeanArithmeticFormulas

/-!
Budget syntax with exact coefficient and interval leaves. This module
binds integer arithmetic expression checks to equation r12:eq58 and its
closed interval quadratic minimum. It is generic and consumes no generated
record family.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

def lowMeanShapeSum : List LowMeanIntegerShape → LowMeanIntegerShape
  | [] => lowMeanShapeInt 0
  | x :: xs => .add x (lowMeanShapeSum xs)

@[simp] theorem lowMean_shape_sum (xs : List LowMeanIntegerShape) :
    lowMeanIntegerShapeReal (lowMeanShapeSum xs) = (xs.map lowMeanIntegerShapeReal).sum := by
  induction xs with
  | nil => simp [lowMeanShapeSum]
  | cons x xs ih => simp [lowMeanShapeSum, lowMeanIntegerShapeReal, ih]

def lowMeanShapePsi (alpha beta gamma m0 x : LowMeanIntegerShape) : LowMeanIntegerShape :=
  lowMeanShapeSub (.add alpha (.mul beta (lowMeanShapeSub x m0)))
    (.mul gamma (.pow (lowMeanShapeSub x m0) 2))

@[simp] theorem lowMean_shape_psi (alpha beta gamma m0 x : LowMeanIntegerShape) :
    lowMeanIntegerShapeReal (lowMeanShapePsi alpha beta gamma m0 x) =
      lowMeanPsi (lowMeanIntegerShapeReal alpha) (lowMeanIntegerShapeReal beta)
        (lowMeanIntegerShapeReal gamma) (lowMeanIntegerShapeReal m0) (lowMeanIntegerShapeReal x) := by
  simp [lowMeanShapePsi, lowMeanIntegerShapeReal, lowMeanPsi]

/-- Only explicit integers and positive denominators are stored in records. -/
structure LowMeanBudgetInput where
  M : ℕ
  j : ℤ
  eta : lowMeanFraction
  xi : lowMeanFraction
  alpha : lowMeanFraction
  beta : lowMeanFraction
  gamma : lowMeanFraction
  m0 : lowMeanFraction
  zeta : lowMeanFraction
  L : lowMeanFraction
  H : lowMeanFraction
  tau : lowMeanFraction
  terms : List (lowMeanFraction × ℤ × ℤ)

noncomputable def lowMeanBudgetInputTerms (r : LowMeanBudgetInput) : List (ℝ × ℤ × ℤ) :=
  r.terms.map fun t => (lowMeanFractionReal t.1, t.2)

def lowMeanBudgetShapeA (r : LowMeanBudgetInput) : LowMeanIntegerShape :=
  .add (.mul (.atom r.eta) (.pow (lowMeanShapeInt r.M) 2))
    (lowMeanShapeSum (r.terms.map fun t => lowMeanShapeSupportA (.atom t.1) t.2.1 t.2.2 (.atom r.L) (.atom r.H)))
def lowMeanBudgetShapeB (r : LowMeanBudgetInput) : LowMeanIntegerShape :=
  .add (lowMeanShapeSub (.mul (.mul (.mul (lowMeanShapeInt (-2)) (.atom r.eta))
      (lowMeanShapeInt r.j)) (lowMeanShapeInt r.M)) (.mul (.atom r.xi) (lowMeanShapeInt r.M)))
    (lowMeanShapeSum (r.terms.map fun t => lowMeanShapeSupportB (.atom t.1) t.2.1 t.2.2
      (.atom r.L) (.atom r.H) (.atom r.tau)))
def lowMeanBudgetShapeC (r : LowMeanBudgetInput) : LowMeanIntegerShape :=
  .add (lowMeanShapeSub (lowMeanShapeSub
    (.add (.mul (.atom r.eta) (.pow (lowMeanShapeInt r.j) 2)) (.mul (.atom r.xi) (lowMeanShapeInt r.j)))
    (lowMeanShapePsi (.atom r.alpha) (.atom r.beta) (.atom r.gamma) (.atom r.m0) (lowMeanShapeInt r.M))) (.atom r.zeta))
    (lowMeanShapeSum (r.terms.map fun t => lowMeanShapeSupportC (.atom t.1) t.2.1 t.2.2
      (.atom r.L) (.atom r.H) (.atom r.tau)))
def lowMeanBudgetShapeMinimum (r : LowMeanBudgetInput) : LowMeanIntegerShape :=
  lowMeanShapeQuadMin (lowMeanBudgetShapeA r) (lowMeanBudgetShapeB r) (lowMeanBudgetShapeC r) (.atom r.L) (.atom r.H)

@[simp] theorem lowMean_budgetShape_A (r : LowMeanBudgetInput) :
    lowMeanIntegerShapeReal (lowMeanBudgetShapeA r) = lowMeanBudgetA (lowMeanBudgetInputTerms r) r.M
      (lowMeanFractionReal r.eta) (lowMeanFractionReal r.L) (lowMeanFractionReal r.H) := by
  simp [lowMeanBudgetShapeA, lowMeanIntegerShapeReal, lowMeanBudgetA, lowMeanBudgetInputTerms, List.map_map, Function.comp_def]
@[simp] theorem lowMean_budgetShape_B (r : LowMeanBudgetInput) :
    lowMeanIntegerShapeReal (lowMeanBudgetShapeB r) = lowMeanBudgetB (lowMeanBudgetInputTerms r) r.M r.j
      (lowMeanFractionReal r.eta) (lowMeanFractionReal r.xi) (lowMeanFractionReal r.L)
      (lowMeanFractionReal r.H) (lowMeanFractionReal r.tau) := by
  simp [lowMeanBudgetShapeB, lowMeanIntegerShapeReal, lowMeanBudgetB, lowMeanBudgetInputTerms, List.map_map, Function.comp_def]
@[simp] theorem lowMean_budgetShape_C (r : LowMeanBudgetInput) :
    lowMeanIntegerShapeReal (lowMeanBudgetShapeC r) = lowMeanBudgetC (lowMeanBudgetInputTerms r) r.M r.j
      (lowMeanFractionReal r.eta) (lowMeanFractionReal r.xi) (lowMeanFractionReal r.alpha)
      (lowMeanFractionReal r.beta) (lowMeanFractionReal r.gamma) (lowMeanFractionReal r.m0)
      (lowMeanFractionReal r.zeta) (lowMeanFractionReal r.L) (lowMeanFractionReal r.H) (lowMeanFractionReal r.tau) := by
  simp [lowMeanBudgetShapeC, lowMeanIntegerShapeReal, lowMeanBudgetC, lowMeanBudgetInputTerms, List.map_map, Function.comp_def]

/-- A checked expression must have the exact budget shape, with all leaves
from this record. Its positivity certifies the printed minimum formula. -/
theorem lowMean_budgetShape_positive (r : LowMeanBudgetInput) (e : LowMeanIntegerExpr)
    (h : lowMeanIntegerPositiveCheck e (lowMeanBudgetShapeMinimum r) (0, 1) = true) :
    0 < lowMeanQuadMinimum
      (lowMeanBudgetA (lowMeanBudgetInputTerms r) r.M (lowMeanFractionReal r.eta) (lowMeanFractionReal r.L) (lowMeanFractionReal r.H))
      (lowMeanBudgetB (lowMeanBudgetInputTerms r) r.M r.j (lowMeanFractionReal r.eta) (lowMeanFractionReal r.xi)
        (lowMeanFractionReal r.L) (lowMeanFractionReal r.H) (lowMeanFractionReal r.tau))
      (lowMeanBudgetC (lowMeanBudgetInputTerms r) r.M r.j (lowMeanFractionReal r.eta) (lowMeanFractionReal r.xi)
        (lowMeanFractionReal r.alpha) (lowMeanFractionReal r.beta) (lowMeanFractionReal r.gamma) (lowMeanFractionReal r.m0)
        (lowMeanFractionReal r.zeta) (lowMeanFractionReal r.L) (lowMeanFractionReal r.H) (lowMeanFractionReal r.tau))
      (lowMeanFractionReal r.L) (lowMeanFractionReal r.H) := by
  simpa [lowMeanBudgetShapeMinimum, lowMeanIntegerShapeReal, lowMeanFractionReal]
    using lowMean_integerPositive_sound h

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMean_budgetShape_positive
