module
public import Erdos993Lean.F4U.Light.Construction.ActualPositivity.E2_guard_S_hi
public import Erdos993Lean.F4U.Light.Construction.ActualPositivity.E2_guard_S_lo
public import Erdos993Lean.F4U.Light.Construction.ActualPositivity.E2_guard_r_hi
public import Erdos993Lean.F4U.Light.Construction.ActualPositivity.E2_guard_r_lo
public import Erdos993Lean.F4U.Light.Construction.FiniteFunctionSigns
@[expose] public section
namespace F4Unified.LightConstruction.FiniteSignsAssembly
noncomputable section
theorem actualGuardFunctionSigns_E2 : ActualGuardFunctionSigns .E2 := by
  intro slot lam t hactive hlam ht0 ht1
  cases slot with
  | r0_lo =>
    exact F4Unified.LightConstruction.ActualPositivity.E2_guard_r_lo.actual_positive hlam ht0 ht1
  | r0_hi =>
    exact F4Unified.LightConstruction.ActualPositivity.E2_guard_r_hi.actual_positive hlam ht0 ht1
  | r1_lo =>
    exact False.elim hactive
  | r1_hi =>
    exact False.elim hactive
  | s0 =>
    exact F4Unified.LightConstruction.ActualPositivity.E2_guard_S_lo.actual_positive hlam ht0 ht1
  | s1 =>
    exact F4Unified.LightConstruction.ActualPositivity.E2_guard_S_hi.actual_positive hlam ht0 ht1
#print axioms actualGuardFunctionSigns_E2
end
end F4Unified.LightConstruction.FiniteSignsAssembly
