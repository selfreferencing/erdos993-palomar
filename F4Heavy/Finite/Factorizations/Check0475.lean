module

public import F4Heavy.Finite.Arithmetic

@[expose] public section
namespace F4Heavy.Finite
open Fraction

theorem factor_step_0475_00 : polyMul [⟨0, 0, ⟨1, 1⟩⟩] [⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩, ⟨1, 1, ⟨1, 1⟩⟩] = [⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩, ⟨1, 1, ⟨1, 1⟩⟩] := by
  decide +kernel

theorem factor_step_0475_01 : polyMul [⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩, ⟨1, 1, ⟨1, 1⟩⟩] [⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩, ⟨1, 1, ⟨1, 1⟩⟩] = [⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨2, 1⟩⟩, ⟨1, 1, ⟨2, 1⟩⟩, ⟨2, 0, ⟨1, 1⟩⟩, ⟨2, 1, ⟨2, 1⟩⟩, ⟨2, 2, ⟨1, 1⟩⟩] := by
  decide +kernel

theorem factor_step_0475_02 : polyMul [⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨2, 1⟩⟩, ⟨1, 1, ⟨2, 1⟩⟩, ⟨2, 0, ⟨1, 1⟩⟩, ⟨2, 1, ⟨2, 1⟩⟩, ⟨2, 2, ⟨1, 1⟩⟩] [⟨0, 0, ⟨1, 9⟩⟩, ⟨0, 1, ⟨4, 3⟩⟩, ⟨0, 2, ⟨1, 1⟩⟩] = [⟨0, 0, ⟨1, 9⟩⟩, ⟨0, 1, ⟨4, 3⟩⟩, ⟨0, 2, ⟨1, 1⟩⟩, ⟨1, 0, ⟨2, 9⟩⟩, ⟨1, 1, ⟨26, 9⟩⟩, ⟨1, 2, ⟨14, 3⟩⟩, ⟨1, 3, ⟨2, 1⟩⟩, ⟨2, 0, ⟨1, 9⟩⟩, ⟨2, 1, ⟨14, 9⟩⟩, ⟨2, 2, ⟨34, 9⟩⟩, ⟨2, 3, ⟨10, 3⟩⟩, ⟨2, 4, ⟨1, 1⟩⟩] := by
  decide +kernel

-- Source assertions.json[475]: E2.r8.D allowed denominator factors
theorem cert_0475_E2_r8_D_allowed_denominator_factors :
    (factorCheck [⟨0, 0, ⟨773115084800000000000, 1⟩⟩, ⟨0, 1, ⟨9277381017600000000000, 1⟩⟩, ⟨0, 2, ⟨6958035763200000000000, 1⟩⟩, ⟨1, 0, ⟨1546230169600000000000, 1⟩⟩, ⟨1, 1, ⟨20100992204800000000000, 1⟩⟩, ⟨1, 2, ⟨32470833561600000000000, 1⟩⟩, ⟨1, 3, ⟨13916071526400000000000, 1⟩⟩, ⟨2, 0, ⟨773115084800000000000, 1⟩⟩, ⟨2, 1, ⟨10823611187200000000000, 1⟩⟩, ⟨2, 2, ⟨26285912883200000000000, 1⟩⟩, ⟨2, 3, ⟨23193452544000000000000, 1⟩⟩, ⟨2, 4, ⟨6958035763200000000000, 1⟩⟩] ⟨6958035763200000000000, 1⟩
    [([⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩, ⟨1, 1, ⟨1, 1⟩⟩], 2),
    ([⟨0, 0, ⟨1, 9⟩⟩, ⟨0, 1, ⟨4, 3⟩⟩, ⟨0, 2, ⟨1, 1⟩⟩], 1)]) = true := by
  exact factorCheck_of_steps (FactorSteps.cons (MultiplySteps.succ factor_step_0475_00 (MultiplySteps.succ factor_step_0475_01 (MultiplySteps.zero _))) (FactorSteps.cons (MultiplySteps.succ factor_step_0475_02 (MultiplySteps.zero _)) (FactorSteps.nil _))) (by decide +kernel)
end F4Heavy.Finite
