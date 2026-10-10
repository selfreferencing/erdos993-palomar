module

public import Erdos993Lean.BCFG.Generated.CHeavyB0.NormalizationGroup


/-! Direct normalization row; no getD of a full bivariate normalization.
-/

@[expose] public section

set_option autoImplicit false
namespace Erdos993Lean.BCFG.CertData.CHeavyB0

theorem normalization_direct_row09 :
    Uni.checkEq
      (Bi.normalizedRow N p qc rq a b 9)
      (Uni.bernVector M (A.getD 9 [])) = true := by
  exact normalization_leaf_rows_checked 9 (by decide +kernel)

end Erdos993Lean.BCFG.CertData.CHeavyB0
