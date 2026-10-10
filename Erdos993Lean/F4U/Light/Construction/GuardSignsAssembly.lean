module
public import Erdos993Lean.F4U.Light.Construction.GuardSignsAssembly.D
public import Erdos993Lean.F4U.Light.Construction.GuardSignsAssembly.E1
public import Erdos993Lean.F4U.Light.Construction.GuardSignsAssembly.E2
public import Erdos993Lean.F4U.Light.Construction.GuardSignsAssembly.H
@[expose] public section
namespace F4Unified.LightConstruction.FiniteSignsAssembly
theorem actualGuardFunctionSigns (r : Row) : ActualGuardFunctionSigns r := by
  cases r with
  | D => exact actualGuardFunctionSigns_D
  | E1 => exact actualGuardFunctionSigns_E1
  | E2 => exact actualGuardFunctionSigns_E2
  | H => exact actualGuardFunctionSigns_H
#print axioms actualGuardFunctionSigns
end F4Unified.LightConstruction.FiniteSignsAssembly
