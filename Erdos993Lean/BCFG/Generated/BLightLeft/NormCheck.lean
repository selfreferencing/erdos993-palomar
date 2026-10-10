module

public import Erdos993Lean.BCFG.Generated.BLightLeft.Data
public import Erdos993Lean.BCFG.Generated.BLightLeft.NormalizationGroup
public import Erdos993Lean.F4Fast.ExactAssembly

/-! Generated transcription of B.light.left
from the coefficient data of rows B, C, F, G.
No Python polynomial arithmetic or certificate replay is performed.
-/

@[expose] public section

set_option autoImplicit false
namespace Erdos993Lean.BCFG.CertData.BLightLeft

theorem normalization_checked :
    Bi.checkEq (Bi.normalized N p qc rq a b) (Bi.fromNorm N M A) = true := by
  exact Bi.normalization_checkEq_of_directRows N M p A qc rq a b
    normalization_rows_integer

end Erdos993Lean.BCFG.CertData.BLightLeft
