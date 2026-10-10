module
public import Erdos993Lean.F4U.Light.Construction.GuardSignsAssembly
public import Erdos993Lean.F4U.Light.Construction.FiniteSignsAssembly.D
public import Erdos993Lean.F4U.Light.Construction.FiniteSignsAssembly.E1
public import Erdos993Lean.F4U.Light.Construction.FiniteSignsAssembly.E2
public import Erdos993Lean.F4U.Light.Construction.FiniteSignsAssembly.H
@[expose] public section
namespace F4Unified.LightConstruction.FiniteSignsAssembly
theorem actualFiniteFunctionSigns (r : Row) : ActualFiniteFunctionSigns r := by
  cases r with
  | D => exact actualFiniteFunctionSigns_D
  | E1 => exact actualFiniteFunctionSigns_E1
  | E2 => exact actualFiniteFunctionSigns_E2
  | H => exact actualFiniteFunctionSigns_H
#print axioms actualFiniteFunctionSigns
end F4Unified.LightConstruction.FiniteSignsAssembly
