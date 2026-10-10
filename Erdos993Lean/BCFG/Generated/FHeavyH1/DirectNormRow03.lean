module

public import Erdos993Lean.BCFG.Generated.FHeavyH1.NormalizationGroup


/-! Direct normalization row; no getD of a full bivariate normalization.
-/

@[expose] public section

set_option autoImplicit false
namespace Erdos993Lean.BCFG.CertData.FHeavyH1

theorem normalization_direct_row03 :
    Uni.checkEq
      (Bi.normalizedRow N p qc rq a b 3)
      (Uni.bernVector M (A.getD 3 [])) = true := by
  exact normalization_leaf_rows_checked 3 (by decide +kernel)

end Erdos993Lean.BCFG.CertData.FHeavyH1
