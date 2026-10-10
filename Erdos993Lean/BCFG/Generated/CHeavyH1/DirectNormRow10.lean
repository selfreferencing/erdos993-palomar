module

public import Erdos993Lean.BCFG.Generated.CHeavyH1.NormalizationGroup


/-! Direct normalization row; no getD of a full bivariate normalization.
-/

@[expose] public section

set_option autoImplicit false
namespace Erdos993Lean.BCFG.CertData.CHeavyH1

theorem normalization_direct_row10 :
    Uni.checkEq
      (Bi.normalizedRow N p qc rq a b 10)
      (Uni.bernVector M (A.getD 10 [])) = true := by
  exact normalization_leaf_rows_checked 10 (by decide +kernel)

end Erdos993Lean.BCFG.CertData.CHeavyH1
