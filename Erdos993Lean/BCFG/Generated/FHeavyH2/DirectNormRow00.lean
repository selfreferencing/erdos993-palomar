module

public import Erdos993Lean.BCFG.Generated.FHeavyH2.NormalizationGroup


/-! Direct normalization row. This does not call getD on a full Bi normalization.
-/

@[expose] public section

set_option autoImplicit false
namespace Erdos993Lean.BCFG.CertData.FHeavyH2

theorem normalization_direct_row00 :
    Uni.checkEq
      (Bi.normalizedRow N p qc rq a b 0)
      (Uni.bernVector M (A.getD 0 [])) = true := by
  exact normalization_leaf_rows_checked 0 (by decide +kernel)

end Erdos993Lean.BCFG.CertData.FHeavyH2
