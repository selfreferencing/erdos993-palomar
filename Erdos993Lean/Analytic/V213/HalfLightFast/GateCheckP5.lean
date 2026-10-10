module

public import Erdos993Lean.Analytic.V213.HalfLightFast.GateShare
public import Erdos993Lean.Analytic.V213.ResponseHalfLightCacheP5Bridge

/-! Every gate of product 5 in ONE kernel evaluation, with the stages of each control shared. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.HalfLightFast

open Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows

theorem productCheck_5 :
    productCheck (⟨5, by decide⟩ : Fin 8) HalfLightPolys.StagedP5.trimmedNF = true := by
  decide +kernel

end Erdos993Lean.Analytic.V213.HalfLightFast
