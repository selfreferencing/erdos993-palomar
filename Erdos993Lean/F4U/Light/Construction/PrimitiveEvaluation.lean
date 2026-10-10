module
public import Erdos993Lean.F4U.Light.Linking.Polynomial2
public import Erdos993Lean.F4U.Light.Soundness.Function
public import Mathlib.Data.List.GetD

/-! The nested integer Horner evaluator is the exact primitive numerator
already certified by the finite checker. Padding uses the record's original
declared parent degree; the activity transform is retained verbatim. -/
@[expose] public section
namespace F4Unified.LightConstruction
noncomputable section
open scoped BigOperators

theorem polynomial2_eval_eq_sum (rows : F4U.Light.Linking.Polynomial2.Rows) (x t : ℝ) :
    F4U.Light.Linking.Polynomial2.eval rows x t =
      ∑ j ∈ Finset.range rows.length, F4U.Light.eval (rows.getD j []) x*t^j := by
  induction rows with
  | nil => simp
  | cons a rows ih =>
    rw [F4U.Light.Linking.Polynomial2.eval_cons,ih,List.length_cons,Finset.sum_range_succ']
    simp only [List.getD_cons_zero,List.getD_cons_succ,pow_zero,mul_one,pow_succ]
    rw [Finset.mul_sum]
    conv_rhs => rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring

theorem polynomial2_eval_eq_sum_padded (rows : F4U.Light.Linking.Polynomial2.Rows)
    (n : Nat) (hn : rows.length ≤ n) (x t : ℝ) :
    F4U.Light.Linking.Polynomial2.eval rows x t =
      ∑ j ∈ Finset.range n, F4U.Light.eval (rows.getD j []) x*t^j := by
  rw [polynomial2_eval_eq_sum]
  apply Finset.sum_subset (Finset.range_mono hn)
  intro j hj hnot
  have hlen : rows.length ≤ j :=
    Nat.le_of_not_gt (fun h => hnot (Finset.mem_range.mpr h))
  rw [List.getD_eq_default rows [] hlen]
  simp

theorem polynomial2_eval_primitiveNumerator (F : F4U.Light.Fn)
    (hrows : F.rows.length ≤ F.m+1) (x t : ℝ) :
    F4U.Light.Linking.Polynomial2.eval F.rows (F4U.Light.activityArg F x) t =
      F4U.Light.primitiveNumerator F x t := by
  exact polynomial2_eval_eq_sum_padded F.rows (F.m+1) hrows (F4U.Light.activityArg F x) t

/-- A checked normalized integer numerator identity connects the root's
integer linking representation to the actual primitive positivity consumer. -/
theorem normalizedNumerator_eq_primitiveNumerator
    {N : F4U.Light.Linking.Polynomial2.Rows} (F : F4U.Light.Fn)
    (hrows : F.rows.length ≤ F.m+1)
    (heq : F4U.Light.Linking.Polynomial2.normalizedEq N F.rows = true) (x t : ℝ) :
    F4U.Light.Linking.Polynomial2.eval N (F4U.Light.activityArg F x) t =
      F4U.Light.primitiveNumerator F x t := by
  exact (F4U.Light.Linking.Polynomial2.normalizedEq_sound heq
    (F4U.Light.activityArg F x) t).trans (polynomial2_eval_primitiveNumerator F hrows x t)

#print axioms polynomial2_eval_eq_sum
#print axioms polynomial2_eval_eq_sum_padded
#print axioms polynomial2_eval_primitiveNumerator
#print axioms normalizedNumerator_eq_primitiveNumerator

end
end F4Unified.LightConstruction
