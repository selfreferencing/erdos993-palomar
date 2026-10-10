module

public import F4Heavy.Contract

/-! Uniqueness of the attained payment minimum, with all parent data fixed. -/

@[expose] public section

namespace F4Unified.Assembly

 theorem minAt_unique {r : Row} {lam Y rho u m₁ m₂ : ℝ}
    (h₁ : MinAt r lam Y rho u m₁) (h₂ : MinAt r lam Y rho u m₂) : m₁ = m₂ := by
  obtain ⟨y₁, hy₁, heq₁⟩ := h₁.2
  obtain ⟨y₂, hy₂, heq₂⟩ := h₂.2
  exact le_antisymm (heq₂ ▸ h₁.1 y₂ hy₂) (heq₁ ▸ h₂.1 y₁ hy₁)

#print axioms minAt_unique

end F4Unified.Assembly
