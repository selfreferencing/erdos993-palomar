module

public import Erdos993Lean.Analytic.V213.HalfLightFast.GateShare
public import Erdos993Lean.Analytic.V213.ResponseHalfLightCacheP2Bridge

/-! Every gate of product 2 in ONE kernel evaluation, with the stages of each control shared. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.HalfLightFast

open Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows

theorem productCheck_2 :
    productCheck (⟨2, by decide⟩ : Fin 8) HalfLightPolys.StagedP2.trimmedNF = true := by
  decide +kernel

end Erdos993Lean.Analytic.V213.HalfLightFast
