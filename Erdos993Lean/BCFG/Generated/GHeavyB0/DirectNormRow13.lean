module

public import Erdos993Lean.BCFG.Generated.GHeavyB0.NormalizationGroup


/-! Direct normalization row; no getD of a full bivariate normalization.
-/

@[expose] public section

set_option autoImplicit false
namespace Erdos993Lean.BCFG.CertData.GHeavyB0

theorem normalization_direct_row13 :
    Uni.checkEq
      (Bi.normalizedRow N p qc rq a b 13)
      (Uni.bernVector M (A.getD 13 [])) = true := by
  exact normalization_leaf_rows_checked 13 (by decide +kernel)

end Erdos993Lean.BCFG.CertData.GHeavyB0
