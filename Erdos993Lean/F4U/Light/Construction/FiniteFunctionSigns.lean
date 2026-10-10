module
public import Erdos993Lean.F4U.Light.Construction.CubicW
public import Erdos993Lean.F4U.Light.Construction.GuardConstruction

/-! The exact retained functions which the finite integer linking modules must
certify. Native second-phase zero controls are restored by a proved source-face
identity, rather than appearing as additional inputs. -/
@[expose] public section
namespace F4Unified.LightConstruction
noncomputable section

def ActualFiniteFunctionSigns (r : Row) : Prop :=
  ∀ reg phase endpoint control s lam t, InRow r lam → 0 ≤ t → t ≤ 1 →
    (reg = .A → control = .V0) → s ≤ vacancyControlDegree reg phase →
    (phase = .second → 1 ≤ s) →
    0 < actualFunctionValue r reg phase endpoint control s lam t

def ActualGuardFunctionSigns (r : Row) : Prop :=
  ∀ slot lam t, ActiveGuard r slot → InRow r lam → 0 ≤ t → t ≤ 1 →
    0 < guardFunctionValue r slot lam t

end
end F4Unified.LightConstruction
