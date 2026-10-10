module

public import F4Heavy.Finite.Arithmetic

@[expose] public section
namespace F4Heavy.Finite
open Fraction

theorem factor_step_0413_00 : polyMul [⟨0, 0, ⟨1, 1⟩⟩] [⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩, ⟨1, 1, ⟨1, 1⟩⟩] = [⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩, ⟨1, 1, ⟨1, 1⟩⟩] := by
  decide +kernel

theorem factor_step_0413_01 : polyMul [⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩, ⟨1, 1, ⟨1, 1⟩⟩] [⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩, ⟨1, 1, ⟨1, 1⟩⟩] = [⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨2, 1⟩⟩, ⟨1, 1, ⟨2, 1⟩⟩, ⟨2, 0, ⟨1, 1⟩⟩, ⟨2, 1, ⟨2, 1⟩⟩, ⟨2, 2, ⟨1, 1⟩⟩] := by
  decide +kernel

theorem factor_step_0413_02 : polyMul [⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨2, 1⟩⟩, ⟨1, 1, ⟨2, 1⟩⟩, ⟨2, 0, ⟨1, 1⟩⟩, ⟨2, 1, ⟨2, 1⟩⟩, ⟨2, 2, ⟨1, 1⟩⟩] [⟨0, 0, ⟨1, 9⟩⟩, ⟨0, 1, ⟨4, 3⟩⟩, ⟨0, 2, ⟨1, 1⟩⟩] = [⟨0, 0, ⟨1, 9⟩⟩, ⟨0, 1, ⟨4, 3⟩⟩, ⟨0, 2, ⟨1, 1⟩⟩, ⟨1, 0, ⟨2, 9⟩⟩, ⟨1, 1, ⟨26, 9⟩⟩, ⟨1, 2, ⟨14, 3⟩⟩, ⟨1, 3, ⟨2, 1⟩⟩, ⟨2, 0, ⟨1, 9⟩⟩, ⟨2, 1, ⟨14, 9⟩⟩, ⟨2, 2, ⟨34, 9⟩⟩, ⟨2, 3, ⟨10, 3⟩⟩, ⟨2, 4, ⟨1, 1⟩⟩] := by
  decide +kernel

-- Source assertions.json[413]: E1.r8.D allowed denominator factors
theorem cert_0413_E1_r8_D_allowed_denominator_factors :
    (factorCheck [⟨0, 0, ⟨72718745600000000000, 1⟩⟩, ⟨0, 1, ⟨872624947200000000000, 1⟩⟩, ⟨0, 2, ⟨654468710400000000000, 1⟩⟩, ⟨1, 0, ⟨145437491200000000000, 1⟩⟩, ⟨1, 1, ⟨1890687385600000000000, 1⟩⟩, ⟨1, 2, ⟨3054187315200000000000, 1⟩⟩, ⟨1, 3, ⟨1308937420800000000000, 1⟩⟩, ⟨2, 0, ⟨72718745600000000000, 1⟩⟩, ⟨2, 1, ⟨1018062438400000000000, 1⟩⟩, ⟨2, 2, ⟨2472437350400000000000, 1⟩⟩, ⟨2, 3, ⟨2181562368000000000000, 1⟩⟩, ⟨2, 4, ⟨654468710400000000000, 1⟩⟩] ⟨654468710400000000000, 1⟩
    [([⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩, ⟨1, 1, ⟨1, 1⟩⟩], 2),
    ([⟨0, 0, ⟨1, 9⟩⟩, ⟨0, 1, ⟨4, 3⟩⟩, ⟨0, 2, ⟨1, 1⟩⟩], 1)]) = true := by
  exact factorCheck_of_steps (FactorSteps.cons (MultiplySteps.succ factor_step_0413_00 (MultiplySteps.succ factor_step_0413_01 (MultiplySteps.zero _))) (FactorSteps.cons (MultiplySteps.succ factor_step_0413_02 (MultiplySteps.zero _)) (FactorSteps.nil _))) (by decide +kernel)
end F4Heavy.Finite
