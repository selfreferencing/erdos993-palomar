module

public import Erdos993Lean.Analytic.V213.LowMeanData.CoreBlock00
public import Erdos993Lean.Analytic.V213.LowMeanData.CoreBlock01
public import Erdos993Lean.Analytic.V213.LowMeanData.CoreBlock02
public import Erdos993Lean.Analytic.V213.LowMeanData.CoreBlock03
public import Erdos993Lean.Analytic.V213.LowMeanData.CoreBlock04
public import Erdos993Lean.Analytic.V213.LowMeanData.CoreBlock05
public import Erdos993Lean.Analytic.V213.LowMeanData.CoreBlock06
public import Erdos993Lean.Analytic.V213.LowMeanData.CoreBlock07
public import Erdos993Lean.Analytic.V213.LowMeanData.CoreBlock08
public import Erdos993Lean.Analytic.V213.LowMeanData.CoreBlock09
public import Erdos993Lean.Analytic.V213.LowMeanData.CoreBlock10
public import Erdos993Lean.Analytic.V213.LowMeanData.CoreBlock11
public import Erdos993Lean.Analytic.V213.LowMeanData.CoreBlock12
public import Erdos993Lean.Analytic.V213.LowMeanData.CoreBlock13
public import Erdos993Lean.Analytic.V213.LowMeanData.CoreBlock14
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0000

/-! Complete cores for every reviewed direct fiber, over all integer ranks. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanCoreFibers : List LowMeanFiberInput :=
  lowMeanCoreBlock00 ++ lowMeanCoreBlock01 ++ lowMeanCoreBlock02 ++ lowMeanCoreBlock03 ++ lowMeanCoreBlock04 ++ lowMeanCoreBlock05 ++ lowMeanCoreBlock06 ++ lowMeanCoreBlock07 ++ lowMeanCoreBlock08 ++ lowMeanCoreBlock09 ++ lowMeanCoreBlock10 ++ lowMeanCoreBlock11 ++ lowMeanCoreBlock12 ++ lowMeanCoreBlock13 ++ lowMeanCoreBlock14

theorem lowMean_cores_kernel : lowMeanCoreFibers.all lowMeanFiberCheck = true := by
  simp only [lowMeanCoreFibers, List.all_append, lowMeanCoreBlock00_kernel, lowMeanCoreBlock01_kernel, lowMeanCoreBlock02_kernel, lowMeanCoreBlock03_kernel, lowMeanCoreBlock04_kernel, lowMeanCoreBlock05_kernel, lowMeanCoreBlock06_kernel, lowMeanCoreBlock07_kernel, lowMeanCoreBlock08_kernel, lowMeanCoreBlock09_kernel, lowMeanCoreBlock10_kernel, lowMeanCoreBlock11_kernel, lowMeanCoreBlock12_kernel, lowMeanCoreBlock13_kernel, lowMeanCoreBlock14_kernel, Bool.and_self]

theorem lowMean_cores_length : lowMeanCoreFibers.length = 564 := by
  simp only [lowMeanCoreFibers, List.length_append, lowMeanCoreBlock00_length, lowMeanCoreBlock01_length, lowMeanCoreBlock02_length, lowMeanCoreBlock03_length, lowMeanCoreBlock04_length, lowMeanCoreBlock05_length, lowMeanCoreBlock06_length, lowMeanCoreBlock07_length, lowMeanCoreBlock08_length, lowMeanCoreBlock09_length, lowMeanCoreBlock10_length, lowMeanCoreBlock11_length, lowMeanCoreBlock12_length, lowMeanCoreBlock13_length, lowMeanCoreBlock14_length]

noncomputable def lowMeanCoreFiberAt (i : ℕ) : LowMeanFiberInput := lowMeanCoreFibers.getD i lowMeanFiber0000

theorem lowMean_core_getD_mem {α : Type*} (xs : List α) (d : α) (i : ℕ) (hi : i < xs.length) : xs.getD i d ∈ xs := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => simp
    | succ i =>
      rw [List.getD_cons_succ]
      exact List.mem_cons_of_mem x (ih i (by simpa using hi))

theorem lowMean_cores_range_kernel : (List.range 564).all (fun i => lowMeanFiberCheck (lowMeanCoreFiberAt i)) = true := by
  apply List.all_eq_true.mpr
  intro i hi
  apply List.all_eq_true.mp lowMean_cores_kernel
  exact lowMean_core_getD_mem _ _ i (by simpa only [lowMean_cores_length] using List.mem_range.mp hi)

theorem lowMean_coreAt_checked (i : ℕ) (hi : i < 564) : lowMeanFiberCheck (lowMeanCoreFiberAt i) = true :=
  Erdos993Lean.F4Fast.forall_lt_of_range_all lowMean_cores_range_kernel i hi

theorem lowMean_coreAt_exact (i : ℕ) (hi : i < 564) (j : ℤ) :
    j ∈ lowMeanFiberCore (lowMeanCoreFiberAt i) ↔ j ∈ (lowMeanCoreFiberAt i).core :=
  lowMean_fiber_core_exact _ (lowMean_coreAt_checked i hi) j

theorem lowMean_cores_frozenOrder_kernel : (List.range 564).all (fun i => decide ((lowMeanCoreFiberAt i).record = i)) = true := by
  decide +kernel

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMean_cores_kernel
#print axioms Erdos993Lean.Analytic.V213.lowMean_coreAt_exact
