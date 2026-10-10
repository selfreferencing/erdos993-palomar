module
public import F4Heavy.Contract
@[expose] public section
namespace F4Unified.F4UTypeFreeze
def frozenLightCore (r : Row) : Prop :=
  ∀ lam Y rho u, InRow r lam → 0 < Y → parentH Y ≤ q lam →
    FeasibleVacancy lam Y rho → q lam / 2 ≤ u → u ≤ parentH Y →
    ∃ m, MinAt r lam Y rho u m ∧ 0 < m
end F4Unified.F4UTypeFreeze
