module

public import Erdos993Lean.BCFG.Generated.FHeavyH2.NormalizationGroup


/-! Direct normalization row. -/

@[expose] public section

set_option autoImplicit false
namespace Erdos993Lean.BCFG.CertData.FHeavyH2

theorem normalization_direct_row02 :
    Uni.checkEq
      (Bi.normalizedRow N p qc rq a b 2)
      (Uni.bernVector M (A.getD 2 [])) = true := by
  exact normalization_leaf_rows_checked 2 (by decide +kernel)

end Erdos993Lean.BCFG.CertData.FHeavyH2

