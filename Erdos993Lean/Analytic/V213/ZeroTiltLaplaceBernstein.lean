module

public import Erdos993Lean.Analytic.V213.ZeroTiltLaplaceExactBi
public import Erdos993Lean.BCFG.BernsteinPositivity

/-! Printed equation(44), exact reconstruction checks and closed rectangles.
The coefficient formula is evaluated inside Lean. Each finite instance must
prove its own reconstruction and all its printed lower comparisons; this
generic implication accepts none of the ten instances by itself. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial

open Erdos993Lean.BCFG
open scoped BigOperators

/-- Literal equation(44), with ascending monomial coefficients of the already
affine-substituted polynomial. Consumers use A<=n and B<=m. -/
def bernCoefficient (n m : Nat) (p : Bi) (A B : Nat) : Rat :=
  ((List.range (A+1)).map fun i =>
    ((List.range (B+1)).map fun j =>
      (p.getD i []).getD j 0 * (A.choose i : Rat) * (B.choose j : Rat) /
        ((n.choose i : Rat) * (m.choose j : Rat))).sum).sum

def fromBernstein (n m : Nat) (c : Nat → Nat → Rat) : Bi :=
  Bi.sumRange (fun A =>
    Bi.tensor (Uni.bernBasis n A) (Uni.bernPoly m (c A))) (n+1)

theorem fromBernstein_sound (n m : Nat) (c : Nat → Nat → Rat) (s z : ℝ) :
    Bi.evalReal (fromBernstein n m c) s z =
      bernsteinSum n (fun A => bernsteinSum m (fun B => (c A B : ℝ)) z) s := by
  rw [fromBernstein, Bi.evalReal_sumRange]
  unfold bernsteinSum
  apply Finset.sum_congr rfl
  intro A hA
  rw [Bi.evalReal_tensor, Uni.evalReal_bernBasis, Uni.evalReal_bernPoly]
  unfold bernsteinBasis
  ring

/-- The table prints one positive c_A per outer index; every inner index must
separately satisfy the explicit100*b_AB>=c_A comparison. -/
def lowerCheck (n m : Nat) (b : Nat → Nat → Rat) (c : List Rat) : Bool :=
  (List.range (n+1)).all fun A =>
    decide (0 < c.getD A 0) &&
      (List.range (m+1)).all (fun B => decide (c.getD A 0 ≤ 100*b A B))

theorem lowerCheck_sound {n m : Nat} {b : Nat → Nat → Rat} {c : List Rat}
    (h : lowerCheck n m b c = true) (A B : Nat) (hA : A≤n) (hB : B≤m) :
    0 < b A B := by
  have hr := List.all_eq_true.mp h A (List.mem_range.mpr (Nat.lt_succ_iff.mpr hA))
  rcases Bool.and_eq_true_iff.mp hr with ⟨hp,hrow⟩
  have hp' : 0<c.getD A 0 := of_decide_eq_true hp
  have hc : c.getD A 0≤100*b A B := of_decide_eq_true
    (List.all_eq_true.mp hrow B (List.mem_range.mpr (Nat.lt_succ_iff.mpr hB)))
  linarith

theorem two_bernstein_positive {n m : Nat} {b : Nat → Nat → Rat}
    (hb : ∀ A≤n, ∀ B≤m, 0<b A B) {s z : ℝ}
    (hs : 0≤s ∧ s≤1) (hz : 0≤z ∧ z≤1) :
    0<Bi.evalReal (fromBernstein n m b) s z := by
  rw [fromBernstein_sound]
  apply bernsteinSum_pos n _ _ hs
  intro A hA
  apply bernsteinSum_pos m _ _ hz
  intro B hB
  exact_mod_cast hb A hA B hB

theorem checked_chart_positive (e : Expr) (n m : Nat) (l h v w : Rat)
    (c : List Rat)
    (hidentity : Bi.checkEq (Expr.chart e l h v w)
      (fromBernstein n m (bernCoefficient n m (Expr.chart e l h v w))) = true)
    (hlower : lowerCheck n m (bernCoefficient n m (Expr.chart e l h v w)) c = true)
    {s z : ℝ} (hs : 0≤s ∧ s≤1) (hz : 0≤z ∧ z≤1) :
    0<Expr.eval e ((l : ℝ)+((h : ℝ)-(l : ℝ))*s)
      ((v : ℝ)+((w : ℝ)-(v : ℝ))*z) := by
  rw [← Expr.chart_sound, Bi.checkEq_sound hidentity s z]
  exact two_bernstein_positive (fun A hA B hB => lowerCheck_sound hlower A B hA hB) hs hz

/-- Exact affine chart recovery, including all four sides of the rectangle.
For an unused second variable the finite instance may use the dummy[0,1]. -/
theorem checked_rectangle_positive (e : Expr) (n m : Nat) (l h v w : Rat)
    (c : List Rat) (hlh : l<h) (hvw : v<w)
    (hidentity : Bi.checkEq (Expr.chart e l h v w)
      (fromBernstein n m (bernCoefficient n m (Expr.chart e l h v w))) = true)
    (hlower : lowerCheck n m (bernCoefficient n m (Expr.chart e l h v w)) c = true)
    {x y : ℝ} (hx : (l : ℝ)≤x ∧ x≤(h : ℝ)) (hy : (v : ℝ)≤y ∧ y≤(w : ℝ)) :
    0<Expr.eval e x y := by
  have hlhR : (l : ℝ)<(h : ℝ) := by exact_mod_cast hlh
  have hvwR : (v : ℝ)<(w : ℝ) := by exact_mod_cast hvw
  have hq : 0<(h : ℝ)-(l : ℝ) := sub_pos.mpr hlhR
  have hu : 0<(w : ℝ)-(v : ℝ) := sub_pos.mpr hvwR
  let s := (x-(l : ℝ))/((h : ℝ)-(l : ℝ))
  let z := (y-(v : ℝ))/((w : ℝ)-(v : ℝ))
  have hs : 0≤s ∧ s≤1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hx.1) hq.le
    · exact (div_le_one hq).2 (by linarith [hx.2])
  have hz : 0≤z ∧ z≤1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hy.1) hu.le
    · exact (div_le_one hu).2 (by linarith [hy.2])
  have hx' : (l : ℝ)+((h : ℝ)-(l : ℝ))*s=x := by
    dsimp [s]
    field_simp [hq.ne'] <;> ring
  have hy' : (v : ℝ)+((w : ℝ)-(v : ℝ))*z=y := by
    dsimp [z]
    field_simp [hu.ne'] <;> ring
  have hp := checked_chart_positive e n m l h v w c hidentity hlower hs hz
  simpa only [hx',hy'] using hp

end Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial

#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.fromBernstein_sound
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.fromBernstein_sound
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.lowerCheck_sound
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.lowerCheck_sound
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.two_bernstein_positive
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.two_bernstein_positive
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.checked_chart_positive
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.checked_chart_positive
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.checked_rectangle_positive
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.checked_rectangle_positive
