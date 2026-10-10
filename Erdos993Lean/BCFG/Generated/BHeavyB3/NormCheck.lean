module

public import Mathlib.Tactic.IntervalCases
public import Erdos993Lean.BCFG.Generated.BHeavyB3.DirectNormRow00
public import Erdos993Lean.BCFG.Generated.BHeavyB3.DirectNormRow01
public import Erdos993Lean.BCFG.Generated.BHeavyB3.DirectNormRow02
public import Erdos993Lean.BCFG.Generated.BHeavyB3.DirectNormRow03
public import Erdos993Lean.BCFG.Generated.BHeavyB3.DirectNormRow04
public import Erdos993Lean.BCFG.Generated.BHeavyB3.DirectNormRow05
public import Erdos993Lean.BCFG.Generated.BHeavyB3.DirectNormRow06
public import Erdos993Lean.BCFG.Generated.BHeavyB3.DirectNormRow07
public import Erdos993Lean.BCFG.Generated.BHeavyB3.DirectNormRow08
public import Erdos993Lean.BCFG.Generated.BHeavyB3.DirectNormRow09
public import Erdos993Lean.BCFG.Generated.BHeavyB3.DirectNormRow10

/-! Every direct normalization row, with the original data and degree.
The whole-list Boolean is not claimed by this route. -/

@[expose] public section

set_option autoImplicit false
namespace Erdos993Lean.BCFG.CertData.BHeavyB3

theorem normalization_rows_checked :
    ∀ i < N+1,
      Uni.checkEq (Bi.normalizedRow N p qc rq a b i)
        (Uni.bernVector M (A.getD i [])) = true := by
  intro i hi
  have hiBound : i < 11 := by simpa only [N] using hi
  interval_cases i
  · exact normalization_direct_row00
  · exact normalization_direct_row01
  · exact normalization_direct_row02
  · exact normalization_direct_row03
  · exact normalization_direct_row04
  · exact normalization_direct_row05
  · exact normalization_direct_row06
  · exact normalization_direct_row07
  · exact normalization_direct_row08
  · exact normalization_direct_row09
  · exact normalization_direct_row10

end Erdos993Lean.BCFG.CertData.BHeavyB3
