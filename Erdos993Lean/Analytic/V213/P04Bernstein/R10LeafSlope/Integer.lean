module

public import Erdos993Lean.Analytic.V213.P04Bernstein.R10LeafSlope.Data
public import Erdos993Lean.F4Fast.P04IntegerBernstein
public import Erdos993Lean.F4Fast.P04IntegerAssembly

/-! Pure integer certificate checks; original data in Data.lean is retained.
The syntax erasure and generic field lemmas recover the original Rat predicates. -/

@[expose] public section
set_option autoImplicit false

namespace Erdos993Lean.Analytic.V213.P04Bernstein.R10LeafSlope
open Erdos993Lean.BCFG Erdos993Lean.F4Fast.P04Int
open Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial

def integerExpression : IntExpr := IntExpr.add (IntExpr.mul (IntExpr.mul (IntExpr.mul (IntExpr.first) (IntExpr.add (IntExpr.constant 1 1) (IntExpr.first))) (IntExpr.add (IntExpr.add (IntExpr.add (IntExpr.constant 100 1) (IntExpr.neg (IntExpr.mul (IntExpr.constant 101 1) (IntExpr.first)))) (IntExpr.neg (IntExpr.mul (IntExpr.constant 3 1) (IntExpr.pow (IntExpr.first) 2)))) (IntExpr.mul (IntExpr.mul (IntExpr.first) (IntExpr.add (IntExpr.constant 1 1) (IntExpr.mul (IntExpr.constant 3 1) (IntExpr.first)))) (IntExpr.pow (IntExpr.second) 2)))) (IntExpr.pow (IntExpr.add (IntExpr.constant 1 1) (IntExpr.mul (IntExpr.first) (IntExpr.pow (IntExpr.second) 2))) 2)) (IntExpr.neg (IntExpr.mul (IntExpr.mul (IntExpr.add (IntExpr.mul (IntExpr.mul (IntExpr.mul (IntExpr.constant 100 1) (IntExpr.first)) (IntExpr.add (IntExpr.constant 1 1) (IntExpr.mul (IntExpr.constant 2 1) (IntExpr.first)))) (IntExpr.add (IntExpr.constant 1 1) (IntExpr.neg (IntExpr.first)))) (IntExpr.mul (IntExpr.mul (IntExpr.mul (IntExpr.constant 50 1) (IntExpr.constant 3 1250)) (IntExpr.add (IntExpr.constant 1 1) (IntExpr.first))) (IntExpr.add (IntExpr.constant 2 1) (IntExpr.neg (IntExpr.first))))) (IntExpr.add (IntExpr.add (IntExpr.constant 1 1) (IntExpr.neg (IntExpr.first))) (IntExpr.mul (IntExpr.first) (IntExpr.pow (IntExpr.second) 2)))) (IntExpr.add (IntExpr.add (IntExpr.add (IntExpr.constant 1 1) (IntExpr.mul (IntExpr.first) (IntExpr.second))) (IntExpr.mul (IntExpr.first) (IntExpr.pow (IntExpr.second) 2))) (IntExpr.neg (IntExpr.mul (IntExpr.first) (IntExpr.pow (IntExpr.second) 3))))))
def integerX : WholeBi := ⟨[[30], [19]], 70⟩
def integerY : WholeBi := ⟨[[0, 1]], 1⟩
def integerChart : WholeBi := IntExpr.encode integerExpression integerX integerY
def integerLower : List Int := [69, 144, 241, 355, 474, 578, 632]
def integerWeight : Int := (n.factorial * m.factorial : Nat)
def integerFactor (i j : Nat) : Int := integerWeight / ((n.choose i : Int)*(m.choose j : Int))
def integerCoefficient (A B : Nat) : Int :=
  weightedCoefficient n m integerChart.num integerFactor A B

theorem integer_domain : IntExpr.valid integerExpression ∧ WholeBi.valid integerX ∧
    WholeBi.valid integerY ∧ 0 < integerWeight := by
  dsimp [integerExpression,IntExpr.valid,WholeBi.valid,integerX,integerY]
  repeat' apply And.intro
  all_goals decide +kernel

theorem integer_weights_checked :
    (List.range (n+1)).all (fun i => (List.range (m+1)).all (fun j =>
      decide (integerFactor i j * (n.choose i : Int) * (m.choose j : Int) = integerWeight))) = true := by
  decide +kernel

theorem integer_weights (i j : Nat) (hi : i < n+1) (hj : j < m+1) :
    integerFactor i j * (n.choose i : Int) * (m.choose j : Int) = integerWeight := by
  exact of_decide_eq_true (Erdos993Lean.F4Fast.forall_lt_of_range_all
    (Erdos993Lean.F4Fast.forall_lt_of_range_all integer_weights_checked i hi) j hj)

theorem integer_chart_valid : 0 < integerChart.den :=
  IntExpr.encode_valid integerExpression integerX integerY integer_domain.1
    integer_domain.2.1 integer_domain.2.2.1

theorem integer_syntax_exact : IntExpr.erase integerExpression = expr := by
  norm_num [integerExpression,IntExpr.erase,expr,leafSlopeExpr,minusExpr] <;> rfl

theorem integer_chart_exact : chart = WholeBi.recover integerChart := by
  apply IntExpr.chart_eq_recover integerExpression expr lo hi v w integerX integerY
    integer_domain.1 integer_domain.2.1 integer_domain.2.2.1 integer_syntax_exact
  · norm_num [WholeBi.recover,integerX,IBi.castRat,IUni.castRat,rscale,Uni.scale,lo,hi]
  · norm_num [WholeBi.recover,integerY,IBi.castRat,IUni.castRat,rscale,Uni.scale,v,w]

theorem integer_coeff_exact (A B : Nat) (hA : A ≤ n) (hB : B ≤ m) :
    coeff A B = (integerCoefficient A B : Rat) / ((integerChart.den*integerWeight : Int) : Rat) := by
  simp only [Int.cast_mul]
  apply bernCoefficient_eq_integer n m chart integerChart.num integerChart.den
    integerWeight integerFactor (ne_of_gt integer_chart_valid) (ne_of_gt integer_domain.2.2.2)
  · intro i hi j hj
    rw [integer_chart_exact, WholeBi.recover, rscale_getD_getD, IBi.castRat_getD_getD]
    simp only [one_div,div_eq_mul_inv,mul_comm,one_mul,mul_one]
  · intro i hi j hj
    exact integer_weights i j hi hj
  · exact hA
  · exact hB

theorem integer_lower_checked :
    (List.range (n+1)).all (fun A => decide (0 < integerLower.getD A 0) &&
      (List.range (m+1)).all (fun B => decide
        (integerLower.getD A 0 * (integerChart.den*integerWeight) ≤ 100*integerCoefficient A B))) = true := by
  decide +kernel

theorem integer_reconstruction_checked :
    IBi.checkEq (IBi.scale integerWeight integerChart.num)
      (integerFromBernstein n m integerCoefficient) = true := by
  decide +kernel

theorem integer_original_row (A : Nat) (hA : A ≤ n) :
    (decide (0 < lower.getD A 0) &&
      (List.range (m+1)).all (fun B => decide (lower.getD A 0 ≤ 100*coeff A B))) = true := by
  apply lower_row_of_integer m A coeff lower integerLower (integerCoefficient A)
    (integerChart.den*integerWeight) (mul_pos integer_chart_valid integer_domain.2.2.2)
  · have hl : lower = IUni.castRat integerLower := by rfl
    rw [hl, IUni.castRat_getD]
  · intro B hB
    exact integer_coeff_exact A B hA (Nat.le_of_lt_succ hB)
  · exact Erdos993Lean.F4Fast.forall_lt_of_range_all integer_lower_checked A
      (Nat.lt_succ_of_le hA)

theorem integer_original_identity : Bi.checkEq chart (fromBernstein n m coeff) = true := by
  apply reconstruction_of_integer n m chart coeff integerChart.num integerCoefficient
    integerChart.den integerWeight (ne_of_gt integer_chart_valid) (ne_of_gt integer_domain.2.2.2)
  · exact integer_chart_exact
  · intro A hA B hB
    exact integer_coeff_exact A B (Nat.le_of_lt_succ hA) (Nat.le_of_lt_succ hB)
  · exact integer_reconstruction_checked

end Erdos993Lean.Analytic.V213.P04Bernstein.R10LeafSlope

#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R10LeafSlope.integer_domain
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R10LeafSlope.integer_weights_checked
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R10LeafSlope.integer_chart_exact
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R10LeafSlope.integer_coeff_exact
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R10LeafSlope.integer_lower_checked
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R10LeafSlope.integer_reconstruction_checked
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R10LeafSlope.integer_original_row
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R10LeafSlope.integer_original_identity
