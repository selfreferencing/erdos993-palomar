module

public import Erdos993Lean.BCFG.Generated.BHeavyH2.NormalizationGroup


/-! Direct normalization row; no getD of a full bivariate normalization.
-/

@[expose] public section

set_option autoImplicit false
namespace Erdos993Lean.BCFG.CertData.BHeavyH2

theorem normalization_direct_row05 :
    Uni.checkEq
      (Bi.normalizedRow N p qc rq a b 5)
      (Uni.bernVector M (A.getD 5 [])) = true := by
  exact normalization_leaf_rows_checked 5 (by decide +kernel)

end Erdos993Lean.BCFG.CertData.BHeavyH2
