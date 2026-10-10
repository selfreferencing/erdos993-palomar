module

public import Erdos993Lean.BCFG.BernsteinPositivity
public import Erdos993Lean.BCFG.ExactPolynomial

/-! Adapter from the executable rational coefficient lists to Bernstein positivity.
No packet data or data acceptance proof is introduced here.
-/

@[expose] public section


namespace Erdos993Lean.BCFG

namespace Uni

theorem evalReal_bernPoly_eq_bernsteinSum (M : Nat) (c : Nat → Rat) (z : ℝ) :
    evalReal (bernPoly M c) z = bernsteinSum M (fun j => (c j : ℝ)) z := by
  simpa only [bernsteinSum, bernsteinBasis] using evalReal_bernPoly M c z

theorem evalReal_bernVector_eq_bernsteinSum (M : Nat) (c : List Rat) (z : ℝ) :
    evalReal (bernVector M c) z =
      bernsteinSum M (fun j => (c.getD j 0 : ℝ)) z := by
  exact evalReal_bernPoly_eq_bernsteinSum M (fun j => c.getD j 0) z

/-- One finite interval certificate suffices for positivity on its closed
interval. Shape/completeness of a packet's collection is a separate obligation. -/
theorem positive_on_interval_of_checks (p : Uni) (M : Nat) (c : List Rat)
    (a b : Rat) (hab : a < b)
    (hidentity : checkEq (comp p [a, b-a]) (bernVector M c) = true)
    (hpositive : positiveCoefficients M (fun j => c.getD j 0) = true)
    {x : ℝ} (hx : (a : ℝ) ≤ x ∧ x ≤ (b : ℝ)) :
    0 < evalReal p x := by
  apply positive_on_interval_of_bernstein (evalReal p) M
    (fun j => (c.getD j 0 : ℝ)) (a : ℝ) (b : ℝ)
    (by exact_mod_cast hab) ?_ ?_ hx
  · intro t
    have ht := checkEq_sound hidentity t
    rw [evalReal_affine_comp, evalReal_bernVector_eq_bernsteinSum] at ht
    exact ht
  · intro j hj
    change (0 : ℝ) < (c.getD j 0 : ℝ)
    exact_mod_cast (positiveCoefficients_sound hpositive j hj)

end Uni

end Erdos993Lean.BCFG
