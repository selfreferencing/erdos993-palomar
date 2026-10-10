module

public import Erdos993Lean.BCFG.Generated.FHeavyB3.NormalizationGroup


/-! Direct normalization row; no getD of a full bivariate normalization.
-/

@[expose] public section

set_option autoImplicit false
namespace Erdos993Lean.BCFG.CertData.FHeavyB3

theorem normalization_direct_row02 :
    Uni.checkEq
      (Bi.normalizedRow N p qc rq a b 2)
      (Uni.bernVector M (A.getD 2 [])) = true := by
  exact normalization_leaf_rows_checked 2 (by decide +kernel)

end Erdos993Lean.BCFG.CertData.FHeavyB3
