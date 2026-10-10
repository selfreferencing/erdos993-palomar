module

public import Erdos993Lean.BCFG.Generated.BLightCurvature.NormalizationChunk00

/-! Exact bounded row checks for the unchanged light normalization predicate. -/

@[expose] public section

set_option autoImplicit false

namespace Erdos993Lean.BCFG.CertData.BLightCurvature

theorem normalization_rows_integer : ∀ i < N+1,
    Uni.checkEq (Bi.normalizedRow N p qc rq a b i)
      (Uni.bernVector M (A.getD i [])) = true := by
  intro i hi
  have hi' : i < 18 := by simpa only [N] using hi
  simpa only [Nat.zero_add] using normalization_chunk_rows00 i hi'

end Erdos993Lean.BCFG.CertData.BLightCurvature
