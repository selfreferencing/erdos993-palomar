module
public import Erdos993Lean.F4U.Light.Construction.GuardSignsAssembly
public import Erdos993Lean.F4U.Light.Construction.LightStructural
@[expose] public section
namespace F4Unified.LightConstruction
/-- All original guard functions have been supplied; the retained native
function signs are the sole remaining explicit input to the structural proof. -/
theorem lightCore_of_actual_native_signs (r : Row)
    (hf : ActualFiniteFunctionSigns r) : LightCore r :=
  lightCore_of_actual_signs r hf (FiniteSignsAssembly.actualGuardFunctionSigns r)
#print axioms lightCore_of_actual_native_signs
end F4Unified.LightConstruction
