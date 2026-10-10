module

public import Erdos993Lean.BCFG.Generated.FHeavyB3.NormalizationGroup


/-! Direct normalization row; no getD of a full bivariate normalization.
-/

@[expose] public section

set_option autoImplicit false
namespace Erdos993Lean.BCFG.CertData.FHeavyB3

theorem normalization_direct_row01 :
    Uni.checkEq
      (Bi.normalizedRow N p qc rq a b 1)
      (Uni.bernVector M (A.getD 1 [])) = true := by
  exact normalization_leaf_rows_checked 1 (by decide +kernel)

end Erdos993Lean.BCFG.CertData.FHeavyB3
