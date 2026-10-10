module

public import Mathlib.Algebra.Order.Field.Rat
public import Lean.Elab.Tactic.NormCast

/-! Generic exact recovery of fraction comparisons and source-custody
fraction equalities. Every finite comparison premise is an integer
cross-product; denominator domains are explicit and unchanged.
-/

@[expose] public section
set_option autoImplicit false

namespace Erdos993Lean.F4Fast.P04Int

theorem fraction_le (a b c d : Int) (hb : 0 < b) (hd : 0 < d)
    (hcross : a*d ≤ c*b) :
    (a : Rat)/(b : Rat) ≤ (c : Rat)/(d : Rat) := by
  have hbRat : (0 : Rat) < (b : Rat) := by exact_mod_cast hb
  have hdRat : (0 : Rat) < (d : Rat) := by exact_mod_cast hd
  have hc : (a : Rat)*(d : Rat) ≤ (c : Rat)*(b : Rat) := by exact_mod_cast hcross
  exact (div_le_div_iff₀ hbRat hdRat).2 hc

theorem fraction_eq (a b c d : Int) (hb : b ≠ 0) (hd : d ≠ 0)
    (hcross : a*d = c*b) :
    (a : Rat)/(b : Rat) = (c : Rat)/(d : Rat) := by
  have hbRat : (b : Rat) ≠ 0 := by exact_mod_cast hb
  have hdRat : (d : Rat) ≠ 0 := by exact_mod_cast hd
  apply (div_eq_div_iff hbRat hdRat).2
  exact_mod_cast hcross

end Erdos993Lean.F4Fast.P04Int

#print axioms Erdos993Lean.F4Fast.P04Int.fraction_le
#print axioms Erdos993Lean.F4Fast.P04Int.fraction_eq
