module

public import Erdos993Lean.F4U.AssemblyA.Regions

/-! Payment positivity in the light region, preserving all fixed parent data. -/

@[expose] public section

namespace F4Unified.Assembly

 theorem payment_pos_of_minAt {r : Row} {lam Y rho u y m : ℝ}
    (hm : MinAt r lam Y rho u m) (hpos : 0 < m) (hy : Admissible lam u y) :
    0 < payment r lam Y rho u y :=
  lt_of_lt_of_le hpos (hm.1 y hy)

 theorem payment_pos_below_cap {r : Row} {lam Y rho u y m : ℝ}
    (hcap : FixedParentCap r) (hrow : InRow r lam) (hY : 0 < Y)
    (hparent : parentH Y ≤ q lam) (hrho : FeasibleVacancy lam Y rho)
    (hu : 0 ≤ u) (hustar : u ≤ min (parentH Y) (q lam / 2))
    (hy : Admissible lam u y)
    (hm : MinAt r lam Y rho (min (parentH Y) (q lam / 2)) m) (hpos : 0 < m) :
    0 < payment r lam Y rho u y := by
  obtain ⟨mcap, hmcap, hbound⟩ := hcap lam Y rho hrow hY hparent hrho
  have heq : mcap = m := minAt_unique hmcap hm
  have hbound' := hbound u y hu hustar hy
  have hcorrection : 0 ≤ (min (parentH Y) (q lam / 2) - u) / 1000 :=
    div_nonneg (sub_nonneg.mpr hustar) (by norm_num)
  rw [heq] at hbound'
  linarith

 theorem upperLight_positive (r : Row) (hcap : FixedParentCap r) (hlight : LightCore r) :
    ∀ lam Y rho u y, PairDomain r lam Y rho u y → parentH Y ≤ q lam →
      q lam / 2 ≤ parentH Y → 0 < payment r lam Y rho u y := by
  intro lam Y rho u y hdom hparent hhalf
  rcases hdom with ⟨hrow, hY, hrho, hu, hucap, hy⟩
  have huH : u ≤ parentH Y := hucap.trans (min_le_right _ _)
  by_cases hupper : q lam / 2 ≤ u
  · obtain ⟨m, hm, hpos⟩ := hlight lam Y rho u hrow hY hparent hrho hupper huH
    exact payment_pos_of_minAt hm hpos hy
  · obtain ⟨m, hm, hpos⟩ :=
      hlight lam Y rho (q lam / 2) hrow hY hparent hrho le_rfl hhalf
    have hstar : min (parentH Y) (q lam / 2) = q lam / 2 := min_eq_right hhalf
    apply payment_pos_below_cap hcap hrow hY hparent hrho hu
    · rw [hstar]
      exact le_of_lt (lt_of_not_ge hupper)
    · exact hy
    · simpa only [hstar] using hm
    · exact hpos

 theorem lightRegion_positive (r : Row) (hhalf : HalfLight r)
    (hcap : FixedParentCap r) (hlight : LightCore r) :
    ∀ lam Y rho u y, PairDomain r lam Y rho u y → parentH Y ≤ q lam →
      0 < payment r lam Y rho u y := by
  intro lam Y rho u y hdom hparent
  by_cases hsmall : parentH Y ≤ q lam / 2
  · rcases hdom with ⟨hrow, hY, hrho, hu, hucap, hy⟩
    obtain ⟨m, hm, hpos⟩ := hhalf lam Y rho hrow hY hsmall hrho
    have hstar : min (parentH Y) (q lam / 2) = parentH Y := min_eq_left hsmall
    apply payment_pos_below_cap hcap hrow hY hparent hrho hu
    · rw [hstar]
      exact hucap.trans (min_le_right _ _)
    · exact hy
    · simpa only [hstar] using hm
    · exact hpos
  · exact upperLight_positive r hcap hlight lam Y rho u y hdom hparent
      (le_of_lt (lt_of_not_ge hsmall))

#print axioms payment_pos_of_minAt
#print axioms payment_pos_below_cap
#print axioms upperLight_positive
#print axioms lightRegion_positive

end F4Unified.Assembly
