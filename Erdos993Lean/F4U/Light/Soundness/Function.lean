module
public import Erdos993Lean.F4U.Light.Soundness.Control
public import Erdos993Lean.F4U.Light.Soundness.Parent

@[expose] public section

namespace F4U.Light
open scoped BigOperators

/-- Literal primitive polynomial of a function record, evaluated in its true
activity variable. For an E q-chart this variable is `x/(1-x)`. -/
noncomputable def primitiveNumerator (F : Fn) (x t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (F.m+1), eval (F.rows.getD j []) (activityArg F x) * t^j

noncomputable def NumeratorPositive (F : Fn) : Prop :=
  ∀ x t : ℝ, ActivityInterval F x → 0 ≤ t → t ≤ 1 → 0 < primitiveNumerator F x t

/-- Complete soundness: the geometry, degree shape and every parent index are
checked, and every scalar comparison is consumed for this named polynomial. -/
theorem checkFn_sound {F : Fn} (h : checkFn F = true) : NumeratorPositive F := by
  have hh : (geomOK F && shapeOK F) = true ∧ F.ctls.all (checkCtl F) = true :=
    Bool.and_eq_true_iff.mp h
  have hg : geomOK F = true := (Bool.and_eq_true_iff.mp hh.1).1
  have hs : shapeOK F = true := (Bool.and_eq_true_iff.mp hh.1).2
  have hshape : F.rows.length ≤ F.m+1 ∧ F.ctls.map Ctl.s = List.range (F.m+1) := by
    simpa only [shapeOK, Bool.and_eq_true_iff, decide_eq_true_eq] using hs
  intro x t hx ht0 ht1
  unfold primitiveNumerator
  apply powerSum_pos_of_parent F.m _ _ ⟨ht0, ht1⟩
  intro s hsle
  have hsmem : s ∈ F.ctls.map Ctl.s := by
    rw [hshape.2]
    exact List.mem_range.mpr (Nat.lt_succ_iff.mpr hsle)
  obtain ⟨C, hC, hCs⟩ := List.mem_map.mp hsmem
  have hc : checkCtl F C = true := List.all_eq_true.mp hh.2 C hC
  have hp := checkCtl_sound hg hc hx
  rw [hCs, eval_parent F.m s F.rows hshape.1] at hp
  exact hp

end F4U.Light
