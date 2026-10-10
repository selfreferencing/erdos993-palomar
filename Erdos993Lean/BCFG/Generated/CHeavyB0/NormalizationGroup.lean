module

public import Erdos993Lean.BCFG.Generated.CHeavyB0.NormalizationChunk00
public import Erdos993Lean.BCFG.Generated.CHeavyB0.NormalizationChunk01
public import Erdos993Lean.BCFG.Generated.CHeavyB0.NormalizationChunk02
public import Lean.Elab.Tactic.Omega

/-!
# Three memory-bounded kernel checks for CHeavyB0's normalization rows

The data and original per-row statements are fixed inputs.  Each chunk
shares the kernel's evaluation cache over a consecutive range.  The ranges
partition all 15 rows, with no omitted index or strengthened hypothesis.
The consumer is the original row family, then NormCheck and Positive.
-/

@[expose] public section

set_option autoImplicit false

namespace Erdos993Lean.BCFG.CertData.CHeavyB0

theorem normalization_leaf_rows_checked :
    ∀ i < N+1,
      Uni.checkEq (Bi.normalizedRow N p qc rq a b i)
        (Uni.bernVector M (A.getD i [])) = true := by
  intro i hi
  have hi' : i < 15 := by simpa only [N] using hi
  by_cases h0 : i < 5
  · simpa only [Nat.zero_add] using normalization_chunk_rows00 i h0
  · by_cases h1 : i < 10
    · have hs : 5 ≤ i := by omega
      have hj : i-5 < 5 := by omega
      simpa only [Nat.add_sub_of_le hs] using normalization_chunk_rows01 (i-5) hj
    · have hs : 10 ≤ i := by omega
      have hj : i-10 < 5 := by omega
      simpa only [Nat.add_sub_of_le hs] using normalization_chunk_rows02 (i-10) hj

end Erdos993Lean.BCFG.CertData.CHeavyB0
