module

public import Erdos993Lean.F4U.Light.Construction.Definitions

/-! Literal light response guards and the parent chart retained by their
records. These guards are distinct from the compact-heavy guards. -/

@[expose] public section

namespace F4Unified.LightConstruction
noncomputable section

inductive GuardSlot where
  | r0_lo | r0_hi | r1_lo | r1_hi | s0 | s1
  deriving DecidableEq, Repr

 def ActiveGuard (r : Row) (slot : GuardSlot) : Prop :=
  match r, slot with
  | .E1, .r1_lo | .E1, .r1_hi | .E2, .r1_lo | .E2, .r1_hi => False
  | _, _ => True

 def guardValue (r : Row) (slot : GuardSlot) (lam H : ℝ) : ℝ :=
  match slot with
  | .r0_lo => retainedRGuard r lam H (responseIntervalLo r) (vacancyLo lam H)
  | .r0_hi => retainedRGuard r lam H (responseIntervalHi r) (vacancyLo lam H)
  | .r1_lo => retainedRGuard r lam H (responseIntervalLo r) 1
  | .r1_hi => retainedRGuard r lam H (responseIntervalHi r) 1
  | .s0 => SGuard r lam H (responseIntervalLo r)
  | .s1 => SGuard r lam H (responseIntervalHi r)

 def guardParentChart (lam t : ℝ) : ℝ := q lam/2+q lam*t/2

 def guardFunctionValue (r : Row) (slot : GuardSlot) (lam t : ℝ) : ℝ :=
  guardValue r slot lam (guardParentChart lam t)

 theorem retainedRGuard_pos_iff (r : Row) (lam H v e : ℝ) (hp : 0 < pH lam H) :
    0 < retainedRGuard r lam H v e ↔ 0 < RGuard r lam H v e := by
  cases r <;> simp only [retainedRGuard]
  all_goals exact div_pos_iff_of_pos_right hp

#print axioms ActiveGuard
#print axioms guardValue
#print axioms guardParentChart
#print axioms guardFunctionValue
#print axioms retainedRGuard_pos_iff

end
end F4Unified.LightConstruction
