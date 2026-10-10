module
public import Erdos993Lean.F4U.Light.Construction.FiniteSignsAssembly
public import Erdos993Lean.F4U.Light.Construction.LightCoreFromNative
public import Erdos993Lean.F4U.Light.FrozenLightCore
public import Lean.Elab.Term
@[expose] public section
namespace F4Unified.LightConstruction
theorem lightCore_D : LightCore .D :=
  lightCore_of_actual_native_signs .D FiniteSignsAssembly.actualFiniteFunctionSigns_D
#print axioms lightCore_D
theorem lightCore_E1 : LightCore .E1 :=
  lightCore_of_actual_native_signs .E1 FiniteSignsAssembly.actualFiniteFunctionSigns_E1
#print axioms lightCore_E1
theorem lightCore_E2 : LightCore .E2 :=
  lightCore_of_actual_native_signs .E2 FiniteSignsAssembly.actualFiniteFunctionSigns_E2
#print axioms lightCore_E2
theorem lightCore_H : LightCore .H :=
  lightCore_of_actual_native_signs .H FiniteSignsAssembly.actualFiniteFunctionSigns_H
#print axioms lightCore_H
theorem lightCore_all_rows (r : Row) : LightCore r :=
  lightCore_of_actual_native_signs r (FiniteSignsAssembly.actualFiniteFunctionSigns r)
#print axioms lightCore_all_rows
theorem lightCore_type_frozen (r : Row) :
    LightCore r = F4UTypeFreeze.frozenLightCore r := rfl
#print axioms lightCore_type_frozen
theorem lightCore_all_rows_frozen_type :
    (∀ r : Row, LightCore r) = (∀ r : Row, F4UTypeFreeze.frozenLightCore r) := rfl
#print axioms lightCore_all_rows_frozen_type
example : (show LightCore .D from lightCore_D) =
    (show F4UTypeFreeze.frozenLightCore .D from lightCore_D) := rfl
example : (show LightCore .E1 from lightCore_E1) =
    (show F4UTypeFreeze.frozenLightCore .E1 from lightCore_E1) := rfl
example : (show LightCore .E2 from lightCore_E2) =
    (show F4UTypeFreeze.frozenLightCore .E2 from lightCore_E2) := rfl
example : (show LightCore .H from lightCore_H) =
    (show F4UTypeFreeze.frozenLightCore .H from lightCore_H) := rfl
elab "type_of_decl%" declaration:ident : term => do
  let info ← Lean.getConstInfo declaration.getId
  return info.type
example : (type_of_decl% F4Unified.LightConstruction.lightCore_D) =
    F4UTypeFreeze.frozenLightCore .D := rfl
example : (type_of_decl% F4Unified.LightConstruction.lightCore_E1) =
    F4UTypeFreeze.frozenLightCore .E1 := rfl
example : (type_of_decl% F4Unified.LightConstruction.lightCore_E2) =
    F4UTypeFreeze.frozenLightCore .E2 := rfl
example : (type_of_decl% F4Unified.LightConstruction.lightCore_H) =
    F4UTypeFreeze.frozenLightCore .H := rfl
example : (type_of_decl% F4Unified.LightConstruction.lightCore_all_rows) =
    (∀ r : Row, F4UTypeFreeze.frozenLightCore r) := rfl
example : lightCore_all_rows =
    (show (∀ r : Row, F4UTypeFreeze.frozenLightCore r) from lightCore_all_rows) := rfl
end F4Unified.LightConstruction
