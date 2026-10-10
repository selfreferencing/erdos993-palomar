module

public import Erdos993Lean.BCFG.Generated.GHeavyH1.NormalizationGroup


/-! Direct normalization row; no getD of a full bivariate normalization.
-/

@[expose] public section

set_option autoImplicit false
namespace Erdos993Lean.BCFG.CertData.GHeavyH1

theorem normalization_direct_row12 :
    Uni.checkEq
      (Bi.normalizedRow N p qc rq a b 12)
      (Uni.bernVector M (A.getD 12 [])) = true := by
  exact normalization_leaf_rows_checked 12 (by decide +kernel)

end Erdos993Lean.BCFG.CertData.GHeavyH1
