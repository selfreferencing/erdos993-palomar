module

public import Erdos993Lean.F4U.AssemblyA.Light

/-! The contract's pair closure from its five regional inputs. -/

@[expose] public section

namespace F4Unified.Assembly

 theorem pairPositive_of_localEvidence : ∀ r, LocalEvidence r → PairPositive r := by
  intro r he lam Y rho u y hdom
  by_cases hlight : parentH Y ≤ q lam
  · exact lightRegion_positive r he.boundary he.cap he.light lam Y rho u y hdom hlight
  · have hx : parentX lam Y ≤ 1 := by
      have hlam : 0 < lam := lam_pos_of_inRow hdom.1
      have hnot : ¬ 1 ≤ parentX lam Y := fun h =>
        hlight ((parentH_le_q_iff_one_le_parentX hlam).mpr h)
      exact le_of_lt (lt_of_not_ge hnot)
    by_cases hcompact : (rowData r).xMin ≤ parentX lam Y
    · exact he.compact lam Y rho u y hdom hcompact hx
    · exact he.tail lam Y rho u y hdom (le_of_lt (lt_of_not_ge hcompact))

#print axioms pairPositive_of_localEvidence

end F4Unified.Assembly
