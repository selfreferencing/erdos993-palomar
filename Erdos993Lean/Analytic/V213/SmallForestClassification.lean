module

public import Erdos993Lean.Section6V210.Classification
public import Mathlib.Data.Nat.Choose.Basic

/-!
Exact current domain ↔ accepted C2 catalogue.
No new list is enumerated, no forest is enumerated, and no arithmetic route or
symbolic tangent identity is inferred from this membership statement.

-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.SmallForestPrinted

/-- Equation r12:eq115, without any finite enumeration. -/
def CurrentDomain (a c k : ℕ) : Prop :=
  c ≤ a ∧ 1 ≤ c ∧ a + c ≤ min 24 (4*k-4) ∧ 6*k+3 ≤ 3*a+c

theorem currentDomain_iff_accepted (a c k : ℕ) :
    CurrentDomain a c k ↔ Erdos993Lean.Section6V210.IntegerDomain a c k := by
  unfold CurrentDomain Erdos993Lean.Section6V210.IntegerDomain
  omega

theorem currentDomain_bounds {a c k : ℕ} (hd : CurrentDomain a c k) :
    3 ≤ k ∧ k ≤ 11 ∧ a ≤ 23 ∧ c ≤ 12 := by
  exact Erdos993Lean.Section6V210.integerDomain_bounds
    ((currentDomain_iff_accepted a c k).mp hd)

/-- Every current-domain triple, and only those triples, is in the existing C2 list. -/
theorem mem_accepted_catalogue_iff (a c k : ℕ) :
    Erdos993Lean.Section6V210.mkTriple a c k ∈ Erdos993Lean.Section6V210.allTriples ↔
      CurrentDomain a c k := by
  rw [Erdos993Lean.Section6V210.mem_allTriples_iff]
  change Erdos993Lean.Section6V210.PaperDomain (a+c) a k ↔ CurrentDomain a c k
  rw [Erdos993Lean.Section6V210.paperDomain_iff]
  simpa only [Nat.add_sub_cancel_left] using (currentDomain_iff_accepted a c k).symm

theorem accepted_catalogue_length :
    Erdos993Lean.Section6V210.allTriples.length = 203 :=
  Erdos993Lean.Section6V210.domain_size

theorem accepted_catalogue_nodup : Erdos993Lean.Section6V210.allTriples.Nodup :=
  Erdos993Lean.Section6V210.domain_nodup

end Erdos993Lean.Analytic.V213.SmallForestPrinted

#check Erdos993Lean.Analytic.V213.SmallForestPrinted.currentDomain_iff_accepted
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.currentDomain_iff_accepted
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.currentDomain_bounds
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.currentDomain_bounds
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.mem_accepted_catalogue_iff
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.mem_accepted_catalogue_iff
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.accepted_catalogue_length
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.accepted_catalogue_length
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.accepted_catalogue_nodup
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.accepted_catalogue_nodup
