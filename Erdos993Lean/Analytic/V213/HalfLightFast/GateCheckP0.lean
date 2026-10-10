module

public import Erdos993Lean.Analytic.V213.HalfLightFast.GateShare
public import Erdos993Lean.Analytic.V213.ResponseHalfLightCacheP0Bridge

/-! Every gate of product 0 in ONE kernel evaluation, with the stages of each control shared. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.HalfLightFast

open Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows

theorem productCheck_0 :
    productCheck (⟨0, by decide⟩ : Fin 8) HalfLightPolys.StagedP0.trimmedNF = true := by
  decide +kernel

end Erdos993Lean.Analytic.V213.HalfLightFast
