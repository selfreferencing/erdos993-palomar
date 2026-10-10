module
public import Erdos993Lean.F4U.Light.Construction.ActualPositivity.D_mono_r0_hi
public import Erdos993Lean.F4U.Light.Construction.ActualPositivity.D_mono_r0_lo
public import Erdos993Lean.F4U.Light.Construction.ActualPositivity.D_mono_r1_hi
public import Erdos993Lean.F4U.Light.Construction.ActualPositivity.D_mono_r1_lo
public import Erdos993Lean.F4U.Light.Construction.ActualPositivity.D_mono_s0
public import Erdos993Lean.F4U.Light.Construction.ActualPositivity.D_mono_s1
public import Erdos993Lean.F4U.Light.Construction.FiniteFunctionSigns
@[expose] public section
namespace F4Unified.LightConstruction.FiniteSignsAssembly
noncomputable section
theorem actualGuardFunctionSigns_D : ActualGuardFunctionSigns .D := by
  intro slot lam t hactive hlam ht0 ht1
  cases slot with
  | r0_lo =>
    exact F4Unified.LightConstruction.ActualPositivity.D_mono_r0_lo.actual_positive hlam ht0 ht1
  | r0_hi =>
    exact F4Unified.LightConstruction.ActualPositivity.D_mono_r1_lo.actual_positive hlam ht0 ht1
  | r1_lo =>
    exact F4Unified.LightConstruction.ActualPositivity.D_mono_r0_hi.actual_positive hlam ht0 ht1
  | r1_hi =>
    exact F4Unified.LightConstruction.ActualPositivity.D_mono_r1_hi.actual_positive hlam ht0 ht1
  | s0 =>
    exact F4Unified.LightConstruction.ActualPositivity.D_mono_s0.actual_positive hlam ht0 ht1
  | s1 =>
    exact F4Unified.LightConstruction.ActualPositivity.D_mono_s1.actual_positive hlam ht0 ht1
#print axioms actualGuardFunctionSigns_D
end
end F4Unified.LightConstruction.FiniteSignsAssembly
