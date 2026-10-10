module

public import Mathlib

/-! Exact nonnegative fraction pairs. No quotient normalization or external arithmetic. -/

@[expose] public section
set_option autoImplicit false

namespace Erdos993Lean.BCFG.Analytic.NatLog

abbrev Pair := ℕ × ℕ

def add (p q : Pair) : Pair := (p.1*q.2+q.1*p.2, p.2*q.2)

noncomputable def value (p : Pair) : ℝ := (p.1 : ℝ)/(p.2 : ℝ)

theorem add_den_pos {p q : Pair} (hp : 0 < p.2) (hq : 0 < q.2) :
    0 < (add p q).2 := by
  exact Nat.mul_pos hp hq

theorem value_add {p q : Pair} (hp : 0 < p.2) (hq : 0 < q.2) :
    value (add p q) = value p+value q := by
  have hpR : (p.2 : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp)
  have hqR : (q.2 : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  simp only [value, add, Nat.cast_add, Nat.cast_mul]
  field_simp [hpR, hqR] <;> ring

theorem value_lt_of_cross {p q : Pair} (hp : 0 < p.2) (hq : 0 < q.2)
    (h : p.1*q.2 < q.1*p.2) : value p < value q := by
  have hpR : (0 : ℝ) < p.2 := by exact_mod_cast hp
  have hqR : (0 : ℝ) < q.2 := by exact_mod_cast hq
  apply (div_lt_div_iff₀ hpR hqR).2
  exact_mod_cast h

end Erdos993Lean.BCFG.Analytic.NatLog

#check Erdos993Lean.BCFG.Analytic.NatLog.Pair
#print axioms Erdos993Lean.BCFG.Analytic.NatLog.Pair
#check Erdos993Lean.BCFG.Analytic.NatLog.add
#print axioms Erdos993Lean.BCFG.Analytic.NatLog.add
#check Erdos993Lean.BCFG.Analytic.NatLog.value
#print axioms Erdos993Lean.BCFG.Analytic.NatLog.value
#check Erdos993Lean.BCFG.Analytic.NatLog.add_den_pos
#print axioms Erdos993Lean.BCFG.Analytic.NatLog.add_den_pos
#check Erdos993Lean.BCFG.Analytic.NatLog.value_add
#print axioms Erdos993Lean.BCFG.Analytic.NatLog.value_add
#check Erdos993Lean.BCFG.Analytic.NatLog.value_lt_of_cross
#print axioms Erdos993Lean.BCFG.Analytic.NatLog.value_lt_of_cross
