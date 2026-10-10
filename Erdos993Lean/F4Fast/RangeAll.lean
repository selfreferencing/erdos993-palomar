module

public import Mathlib.Data.List.Range

/-!
# Leaf-level kernel checks

A helper for the F4 certificate modules. One `decide +kernel` evaluates `(List.range n).all f`; this lemma turns
the result into the statement for every `i < n`. Checking all rows of a leaf in one kernel evaluation lets the kernel
share the work the rows have in common.
-/

@[expose] public section

namespace Erdos993Lean.F4Fast

theorem forall_lt_of_range_all {n : Nat} {f : Nat → Bool} (h : (List.range n).all f = true) :
    ∀ i < n, f i = true := by
  intro i hi
  exact List.all_eq_true.mp h i (List.mem_range.mpr hi)

end Erdos993Lean.F4Fast
