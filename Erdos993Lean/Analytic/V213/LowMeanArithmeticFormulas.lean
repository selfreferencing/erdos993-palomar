module

public import Erdos993Lean.Analytic.V213.LowMeanIntegerShape
public import Erdos993Lean.Analytic.V213.LowMeanBudgetFormula

/-!
Formula builders and semantic identities. Arithmetic expression
syntax is bound to the printed monomials, extrema and support coefficients.
Checking a builder's exact erased syntax therefore proves its mathematical
formula. No generated record family is invoked here.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

def lowMeanShapeInt (n : ℤ) : LowMeanIntegerShape := .atom (n, 1)
def lowMeanShapeSub (x y : LowMeanIntegerShape) : LowMeanIntegerShape := .add x (.neg y)
def lowMeanShapeZPow (x : LowMeanIntegerShape) : ℤ → LowMeanIntegerShape
  | .ofNat n => .pow x n
  | .negSucc n => .div (lowMeanShapeInt 1) (.pow x (n + 1))

@[simp] theorem lowMean_shape_int (n : ℤ) : lowMeanIntegerShapeReal (lowMeanShapeInt n) = (n : ℝ) := by
  simp [lowMeanShapeInt, lowMeanIntegerShapeReal, lowMeanFractionReal]
@[simp] theorem lowMean_shape_sub (x y : LowMeanIntegerShape) :
    lowMeanIntegerShapeReal (lowMeanShapeSub x y) = lowMeanIntegerShapeReal x - lowMeanIntegerShapeReal y := by
  simp [lowMeanShapeSub, lowMeanIntegerShapeReal, sub_eq_add_neg]
@[simp] theorem lowMean_shape_zpow (x : LowMeanIntegerShape) (n : ℤ) :
    lowMeanIntegerShapeReal (lowMeanShapeZPow x n) = lowMeanIntegerShapeReal x ^ n := by
  cases n with
  | ofNat n =>
    change lowMeanIntegerShapeReal x ^ n = lowMeanIntegerShapeReal x ^ (n : ℤ)
    rw [zpow_natCast]
  | negSucc n =>
    simp only [lowMeanShapeZPow, lowMeanIntegerShapeReal, lowMean_shape_int,
      Int.cast_one, zpow_negSucc, one_div]

def lowMeanShapeMonomial (c : LowMeanIntegerShape) (a b : ℤ) (q : LowMeanIntegerShape) : LowMeanIntegerShape :=
  .mul (.mul c (lowMeanShapeZPow q a)) (lowMeanShapeZPow (lowMeanShapeSub (lowMeanShapeInt 1) q) b)
def lowMeanShapeMonomialD (c : LowMeanIntegerShape) (a b : ℤ) (q : LowMeanIntegerShape) : LowMeanIntegerShape :=
  .mul (lowMeanShapeMonomial c a b q) (lowMeanShapeSub (.div (lowMeanShapeInt a) q)
    (.div (lowMeanShapeInt b) (lowMeanShapeSub (lowMeanShapeInt 1) q)))
def lowMeanShapeQuad (A B C q : LowMeanIntegerShape) : LowMeanIntegerShape :=
  .add (.add (.mul A (.pow q 2)) (.mul B q)) C
def lowMeanShapeQuadMin (A B C L H : LowMeanIntegerShape) : LowMeanIntegerShape :=
  let v := .div (.neg B) (.mul (lowMeanShapeInt 2) A)
  let left := lowMeanShapeQuad A B C L
  let vertex := lowMeanShapeSub C (.div (.pow B 2) (.mul (lowMeanShapeInt 4) A))
  .minimum left (.minimum (lowMeanShapeQuad A B C H)
    (.selectLT (lowMeanShapeInt 0) A (.selectLE L v (.selectLE v H vertex left) left) left))

@[simp] theorem lowMean_shape_monomial (c : LowMeanIntegerShape) (a b : ℤ) (q : LowMeanIntegerShape) :
    lowMeanIntegerShapeReal (lowMeanShapeMonomial c a b q) =
      lowMeanMonomial (lowMeanIntegerShapeReal c) a b (lowMeanIntegerShapeReal q) := by
  simp [lowMeanShapeMonomial, lowMeanIntegerShapeReal, lowMeanMonomial]
@[simp] theorem lowMean_shape_monomialD (c : LowMeanIntegerShape) (a b : ℤ) (q : LowMeanIntegerShape) :
    lowMeanIntegerShapeReal (lowMeanShapeMonomialD c a b q) =
      lowMeanMonomialD (lowMeanIntegerShapeReal c) a b (lowMeanIntegerShapeReal q) := by
  simp [lowMeanShapeMonomialD, lowMeanIntegerShapeReal, lowMeanMonomialD]
@[simp] theorem lowMean_shape_quad (A B C q : LowMeanIntegerShape) :
    lowMeanIntegerShapeReal (lowMeanShapeQuad A B C q) = lowMeanQuad
      (lowMeanIntegerShapeReal A) (lowMeanIntegerShapeReal B) (lowMeanIntegerShapeReal C) (lowMeanIntegerShapeReal q) := by
  simp [lowMeanShapeQuad, lowMeanIntegerShapeReal, lowMeanQuad]
@[simp] theorem lowMean_shape_quadMin (A B C L H : LowMeanIntegerShape) :
    lowMeanIntegerShapeReal (lowMeanShapeQuadMin A B C L H) = lowMeanQuadMinimum
      (lowMeanIntegerShapeReal A) (lowMeanIntegerShapeReal B) (lowMeanIntegerShapeReal C)
      (lowMeanIntegerShapeReal L) (lowMeanIntegerShapeReal H) := by
  simp only [lowMeanShapeQuadMin, lowMeanIntegerShapeReal, lowMean_shape_quad, lowMean_shape_sub,
    lowMean_shape_int, Int.cast_zero, Int.cast_ofNat, lowMeanQuadMinimum]
  split_ifs <;> simp_all

def lowMeanShapePiA (c : LowMeanIntegerShape) (a b : ℤ) : LowMeanIntegerShape :=
  .mul (.mul (.div c (.abs c)) (lowMeanShapeInt (a + b))) (lowMeanShapeInt (a + b - 1))
def lowMeanShapePiB (c : LowMeanIntegerShape) (a b : ℤ) : LowMeanIntegerShape :=
  .mul (.mul (.mul (lowMeanShapeInt (-2)) (.div c (.abs c))) (lowMeanShapeInt a)) (lowMeanShapeInt (a + b - 1))
def lowMeanShapePiC (c : LowMeanIntegerShape) (a : ℤ) : LowMeanIntegerShape :=
  .mul (.mul (.div c (.abs c)) (lowMeanShapeInt a)) (lowMeanShapeInt (a - 1))
def lowMeanShapePiMin (c : LowMeanIntegerShape) (a b : ℤ) (L H : LowMeanIntegerShape) : LowMeanIntegerShape :=
  lowMeanShapeQuadMin (lowMeanShapePiA c a b) (lowMeanShapePiB c a b) (lowMeanShapePiC c a) L H
def lowMeanShapePiMax (c : LowMeanIntegerShape) (a b : ℤ) (L H : LowMeanIntegerShape) : LowMeanIntegerShape :=
  .neg (lowMeanShapeQuadMin (.neg (lowMeanShapePiA c a b)) (.neg (lowMeanShapePiB c a b))
    (.neg (lowMeanShapePiC c a)) L H)
def lowMeanShapeMonomialR (c : LowMeanIntegerShape) (a b : ℤ) (L H : LowMeanIntegerShape) : LowMeanIntegerShape :=
  let left := .abs (lowMeanShapeMonomial c a b L)
  let mode := .div (lowMeanShapeInt a) (lowMeanShapeInt (a + b))
  .maximum left (.maximum (.abs (lowMeanShapeMonomial c a b H))
    (.selectLT (lowMeanShapeInt 0) (lowMeanShapeInt (a + b))
      (.selectLE L mode (.selectLE mode H (.abs (lowMeanShapeMonomial c a b mode)) left) left) left))
def lowMeanShapeLambda (c : LowMeanIntegerShape) (a b : ℤ) (L H : LowMeanIntegerShape) : LowMeanIntegerShape :=
  .div (.mul (lowMeanShapePiMin c a b L H) (lowMeanShapeMonomialR c a b L H))
    (.pow (.minimum (.mul L (lowMeanShapeSub (lowMeanShapeInt 1) L))
      (.mul H (lowMeanShapeSub (lowMeanShapeInt 1) H))) 2)

@[simp] theorem lowMean_shape_piA (c : LowMeanIntegerShape) (a b : ℤ) :
    lowMeanIntegerShapeReal (lowMeanShapePiA c a b) = lowMeanPiA (lowMeanIntegerShapeReal c) a b := by
  simp [lowMeanShapePiA, lowMeanIntegerShapeReal, lowMeanPiA]
@[simp] theorem lowMean_shape_piB (c : LowMeanIntegerShape) (a b : ℤ) :
    lowMeanIntegerShapeReal (lowMeanShapePiB c a b) = lowMeanPiB (lowMeanIntegerShapeReal c) a b := by
  simp [lowMeanShapePiB, lowMeanIntegerShapeReal, lowMeanPiB]
@[simp] theorem lowMean_shape_piC (c : LowMeanIntegerShape) (a : ℤ) :
    lowMeanIntegerShapeReal (lowMeanShapePiC c a) = lowMeanPiC (lowMeanIntegerShapeReal c) a := by
  simp [lowMeanShapePiC, lowMeanIntegerShapeReal, lowMeanPiC]
@[simp] theorem lowMean_shape_piMin (c : LowMeanIntegerShape) (a b : ℤ) (L H : LowMeanIntegerShape) :
    lowMeanIntegerShapeReal (lowMeanShapePiMin c a b L H) =
      lowMeanPiMin (lowMeanIntegerShapeReal c) a b (lowMeanIntegerShapeReal L) (lowMeanIntegerShapeReal H) := by
  simp [lowMeanShapePiMin, lowMeanPiMin]
@[simp] theorem lowMean_shape_piMax (c : LowMeanIntegerShape) (a b : ℤ) (L H : LowMeanIntegerShape) :
    lowMeanIntegerShapeReal (lowMeanShapePiMax c a b L H) =
      lowMeanPiMax (lowMeanIntegerShapeReal c) a b (lowMeanIntegerShapeReal L) (lowMeanIntegerShapeReal H) := by
  simp [lowMeanShapePiMax, lowMeanIntegerShapeReal, lowMeanPiMax]
@[simp] theorem lowMean_shape_monomialR (c : LowMeanIntegerShape) (a b : ℤ) (L H : LowMeanIntegerShape) :
    lowMeanIntegerShapeReal (lowMeanShapeMonomialR c a b L H) =
      lowMeanMonomialR (lowMeanIntegerShapeReal c) a b (lowMeanIntegerShapeReal L) (lowMeanIntegerShapeReal H) := by
  simp only [lowMeanShapeMonomialR, lowMeanIntegerShapeReal, lowMean_shape_monomial, lowMean_shape_int,
    Int.cast_zero, lowMeanMonomialR]
  by_cases hm : 0 < a + b
  · have hmR : (0 : ℝ) < ((a + b : ℤ) : ℝ) := by exact_mod_cast hm
    simp only [hm, hmR, true_and, ite_true]
    split_ifs <;> simp_all <;> linarith
  · have hmR : ¬ (0 : ℝ) < ((a + b : ℤ) : ℝ) := by
      intro hh
      apply hm
      exact_mod_cast hh
    simp only [hm, hmR, false_and, ite_false]
@[simp] theorem lowMean_shape_lambda (c : LowMeanIntegerShape) (a b : ℤ) (L H : LowMeanIntegerShape) :
    lowMeanIntegerShapeReal (lowMeanShapeLambda c a b L H) =
      lowMeanLambda (lowMeanIntegerShapeReal c) a b (lowMeanIntegerShapeReal L) (lowMeanIntegerShapeReal H) := by
  simp [lowMeanShapeLambda, lowMeanIntegerShapeReal, lowMeanLambda, lowMeanVarianceMin]

def lowMeanShapeSupportA (c : LowMeanIntegerShape) (a b : ℤ) (L H : LowMeanIntegerShape) : LowMeanIntegerShape :=
  let zero := lowMeanShapeInt 0
  .selectLE (lowMeanShapePiMax c a b L H) zero zero
    (.selectLE zero (lowMeanShapePiMin c a b L H) zero (.div (lowMeanShapeLambda c a b L H) (lowMeanShapeInt 2)))
def lowMeanShapeSupportB (c : LowMeanIntegerShape) (a b : ℤ) (L H tau : LowMeanIntegerShape) : LowMeanIntegerShape :=
  let D := lowMeanShapeMonomialD c a b tau
  .selectLE (lowMeanShapePiMax c a b L H) (lowMeanShapeInt 0)
    (.div (lowMeanShapeSub (lowMeanShapeMonomial c a b H) (lowMeanShapeMonomial c a b L)) (lowMeanShapeSub H L))
    (.selectLE (lowMeanShapeInt 0) (lowMeanShapePiMin c a b L H) D
      (lowMeanShapeSub D (.mul (lowMeanShapeLambda c a b L H) tau)))
def lowMeanShapeSupportC (c : LowMeanIntegerShape) (a b : ℤ) (L H tau : LowMeanIntegerShape) : LowMeanIntegerShape :=
  let tangent := lowMeanShapeSub (lowMeanShapeMonomial c a b tau) (.mul (lowMeanShapeMonomialD c a b tau) tau)
  .selectLE (lowMeanShapePiMax c a b L H) (lowMeanShapeInt 0)
    (.div (lowMeanShapeSub (.mul H (lowMeanShapeMonomial c a b L)) (.mul L (lowMeanShapeMonomial c a b H)))
      (lowMeanShapeSub H L))
    (.selectLE (lowMeanShapeInt 0) (lowMeanShapePiMin c a b L H) tangent
      (.add tangent (.mul (.div (lowMeanShapeLambda c a b L H) (lowMeanShapeInt 2)) (.pow tau 2))))

@[simp] theorem lowMean_shape_supportA (c : LowMeanIntegerShape) (a b : ℤ) (L H : LowMeanIntegerShape) :
    lowMeanIntegerShapeReal (lowMeanShapeSupportA c a b L H) =
      lowMeanSupportA (lowMeanIntegerShapeReal c) a b (lowMeanIntegerShapeReal L) (lowMeanIntegerShapeReal H) := by
  simp [lowMeanShapeSupportA, lowMeanIntegerShapeReal, lowMeanSupportA]
@[simp] theorem lowMean_shape_supportB (c : LowMeanIntegerShape) (a b : ℤ) (L H tau : LowMeanIntegerShape) :
    lowMeanIntegerShapeReal (lowMeanShapeSupportB c a b L H tau) =
      lowMeanSupportB (lowMeanIntegerShapeReal c) a b (lowMeanIntegerShapeReal L) (lowMeanIntegerShapeReal H)
        (lowMeanIntegerShapeReal tau) := by
  simp [lowMeanShapeSupportB, lowMeanIntegerShapeReal, lowMeanSupportB]
@[simp] theorem lowMean_shape_supportC (c : LowMeanIntegerShape) (a b : ℤ) (L H tau : LowMeanIntegerShape) :
    lowMeanIntegerShapeReal (lowMeanShapeSupportC c a b L H tau) =
      lowMeanSupportC (lowMeanIntegerShapeReal c) a b (lowMeanIntegerShapeReal L) (lowMeanIntegerShapeReal H)
        (lowMeanIntegerShapeReal tau) := by
  simp [lowMeanShapeSupportC, lowMeanIntegerShapeReal, lowMeanSupportC]

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMean_shape_quadMin
#print axioms Erdos993Lean.Analytic.V213.lowMean_shape_supportA
#print axioms Erdos993Lean.Analytic.V213.lowMean_shape_supportB
#print axioms Erdos993Lean.Analytic.V213.lowMean_shape_supportC
