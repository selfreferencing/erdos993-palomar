module

public import Erdos993Lean.BCFG.Generated.GHeavyH2.NormalizationGroup


/-! Direct normalization row; no getD of a full bivariate normalization.
-/

@[expose] public section

set_option autoImplicit false
namespace Erdos993Lean.BCFG.CertData.GHeavyH2

theorem normalization_direct_row13 :
    Uni.checkEq
      (Bi.normalizedRow N p qc rq a b 13)
      (Uni.bernVector M (A.getD 13 [])) = true := by
  exact normalization_leaf_rows_checked 13 (by decide +kernel)

end Erdos993Lean.BCFG.CertData.GHeavyH2
