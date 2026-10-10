module

public import Erdos993Lean.BCFG.Generated.FHeavyB0.NormalizationGroup


/-! Direct normalization row; no getD of a full bivariate normalization.
-/

@[expose] public section

set_option autoImplicit false
namespace Erdos993Lean.BCFG.CertData.FHeavyB0

theorem normalization_direct_row04 :
    Uni.checkEq
      (Bi.normalizedRow N p qc rq a b 4)
      (Uni.bernVector M (A.getD 4 [])) = true := by
  exact normalization_leaf_rows_checked 4 (by decide +kernel)

end Erdos993Lean.BCFG.CertData.FHeavyB0
