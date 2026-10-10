module

public import Mathlib.Init
public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Meta.AppBuilder

/-! `kernel_rfl`: close `lhs = rhs` by `Eq.refl lhs`, leaving the definitional check to the kernel
(the elaborator's own unifier is not asked). Test prototype. -/

public meta section

namespace F4U.Light.Reflect
open Lean Meta Elab.Tactic

elab "kernel_rfl" : tactic =>
  liftMetaTactic fun goal => do
    let t ← instantiateMVars (← goal.getType)
    let some (_, lhs, _) := t.eq? | throwError "kernel_rfl: the goal is not an equality"
    goal.assign (← mkEqRefl lhs)
    return []

end F4U.Light.Reflect
