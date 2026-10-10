module

public import Erdos993Lean.Analytic.V213.HalfLightFast.GateShare
public import Erdos993Lean.Analytic.V213.ResponseHalfLightCacheP6Bridge

/-! Every gate of product 6 in ONE kernel evaluation, with the stages of each control shared. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.HalfLightFast

open Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows

theorem productCheck_6 :
    productCheck (⟨6, by decide⟩ : Fin 8) HalfLightPolys.StagedP6.trimmedNF = true := by
  decide +kernel

end Erdos993Lean.Analytic.V213.HalfLightFast
