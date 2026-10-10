module

public import Erdos993Lean.BCFG.Generated.FHeavyH2.NormalizationGroup


/-! Direct normalization row. -/

@[expose] public section

set_option autoImplicit false
namespace Erdos993Lean.BCFG.CertData.FHeavyH2

theorem normalization_direct_row06 :
    Uni.checkEq
      (Bi.normalizedRow N p qc rq a b 6)
      (Uni.bernVector M (A.getD 6 [])) = true := by
  exact normalization_leaf_rows_checked 6 (by decide +kernel)

end Erdos993Lean.BCFG.CertData.FHeavyH2

