module

public import Erdos993Lean.BCFG.Generated.BHeavyH1.NormalizationGroup


/-! Direct normalization row; no getD of a full bivariate normalization.
-/

@[expose] public section

set_option autoImplicit false
namespace Erdos993Lean.BCFG.CertData.BHeavyH1

theorem normalization_direct_row15 :
    Uni.checkEq
      (Bi.normalizedRow N p qc rq a b 15)
      (Uni.bernVector M (A.getD 15 [])) = true := by
  exact normalization_leaf_rows_checked 15 (by decide +kernel)

end Erdos993Lean.BCFG.CertData.BHeavyH1
