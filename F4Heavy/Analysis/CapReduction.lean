module

public import F4Heavy.Analysis.CapComparison

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified
noncomputable section

def capChild (lam Y : ℝ) : ℝ := min (parentH Y) (q lam / 2)
def capB (r : Row) (lam Y rho : ℝ) : ℝ := p lam Y * beta r lam * rho
def capC (r : Row) (lam Y rho : ℝ) : ℝ :=
  p lam Y * (2 * parentP r lam Y rho - alpha r lam - beta r lam)
def capD (r : Row) (lam Y rho : ℝ) : ℝ :=
  gamma r lam - delta r lam - p lam Y * Y * parentP r lam Y rho

/-- Explicit scalar estimates still to be discharged for each region.
No minimum or payment comparison is assumed in these fields. -/
structure CapScalarBounds (r : Row) (lam Y rho : ℝ) : Prop where
  cap_pos : 0 < capChild lam Y
  delta_nonneg : 0 ≤ delta r lam
  b_lower : 1 / 500 ≤ capB r lam Y rho
  response_zero : 0 ≤ capC r lam Y rho + 2 * capD r lam Y rho
  child_bounds : ∀ u, 0 < u → u ≤ capChild lam Y →
    0 < childH u ∧ childH u ≤ 1 ∧ 0 < childJ lam u ∧
    0 < 2 * delta r lam * childH u - capC r lam Y rho * childJ lam u ∧
    0 < capC r lam Y rho + 2 * capD r lam Y rho * childH u
  height_increment : ∀ u, 0 ≤ u → u ≤ capChild lam Y →
    (capChild lam Y - u) / 2 ≤ childH u - childH (capChild lam Y)
  reserve_increment : ∀ u, 0 < u → u ≤ capChild lam Y →
    (childH u - childH (capChild lam Y)) / 500 ≤
      capB r lam Y rho * (childH u - childH (capChild lam Y)) + delta r lam *
      ((childH u) ^ 2 / childJ lam u -
        (childH (capChild lam Y)) ^ 2 / childJ lam (capChild lam Y))

/-- The original cap assertion at a fixed parent follows from scalar bounds. -/
theorem cap_fixed_parent_of_scalar_bounds (r : Row) (lam Y rho : ℝ)
    (hs : CapScalarBounds r lam Y rho) :
    ∃ m, MinAt r lam Y rho (capChild lam Y) m ∧
      ∀ u y, 0 ≤ u → u ≤ capChild lam Y → Admissible lam u y →
        m + (capChild lam Y - u) / 1000 ≤ payment r lam Y rho u y := by
  let a := p lam Y * parentN r lam Y rho / Y
  let b := capB r lam Y rho
  let c := capC r lam Y rho
  let d := capD r lam Y rho
  let h := childH (capChild lam Y)
  let J := childJ lam (capChild lam Y)
  let ys := capResponse c d (delta r lam) J h
  let m := responsePolynomial a b c d (delta r lam) J h ys
  have hc := hs.child_bounds _ hs.cap_pos le_rfl
  have hG := cap_response_curvature c d (delta r lam) J h hc.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2
  have hp (u y : ℝ) (hJu : 0 < childJ lam u) :
      payment r lam Y rho u y =
        responsePolynomial a b c d (delta r lam) (childJ lam u) (childH u) y :=
    cap_payment_response r lam Y rho u y hJu
  refine ⟨m, ?_, ?_⟩
  · constructor
    · intro y _
      rw [hp _ _ hc.2.2.1]
      exact cap_response_attained_lower a b c d (delta r lam) J h y hc.2.2.1 hG
    · exact ⟨ys, Or.inl hc.2.2.1, hp _ _ hc.2.2.1⟩
  · intro u y hu huc hadm
    have hheight := hs.height_increment u hu huc
    by_cases hu0 : u = 0
    · subst u
      have hy : y = 1 := by
        have hz : childJ lam 0 = 0 := by simp [childJ]
        simpa [childH] using admissible_zero_forces_response lam 0 y hz hadm
      subst y
      have hg := cap_attained_forced_gain a b c d (delta r lam) J h (1 / 500)
        hc.1 hc.2.1 hc.2.2.1 hs.delta_nonneg hc.2.2.2.1 hc.2.2.2.2
        hs.response_zero hs.b_lower
      have hp0 : payment r lam Y rho 0 1 = a + b + c + d := by
        simp [payment, reserve, childH, childJ, a, b, c, d, capB, capC, capD]
      rw [hp0]
      change m + (1 / 500) * (1 - h) ≤ a + b + c + d at hg
      simp only [childH, ite_true, sub_zero] at hheight
      change capChild lam Y / 2 ≤ 1 - h at hheight
      linarith only [hg, hheight]
    · have hu' : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
      have hc1 := hs.child_bounds u hu' huc
      have ht : h ≤ childH u := by
        change (capChild lam Y - u) / 2 ≤ childH u - h at hheight
        linarith only [hheight, huc]
      have hb : (1 / 500) * (childH u - h) ≤ b * (childH u - h) :=
        mul_le_mul_of_nonneg_right hs.b_lower (sub_nonneg.mpr ht)
      have hw : (1 / 500) * (childH u - h) ≤ b * (childH u - h) +
          delta r lam * ((childH u) ^ 2 / childJ lam u - h ^ 2 / J) := by
        simpa only [div_eq_mul_inv, one_mul, mul_comm, b, h, J] using hs.reserve_increment u hu' huc
      have hg := cap_attained_response_gain a b c d (delta r lam) (childJ lam u) J
        (childH u) h y (1 / 500) hc1.1 hc.1 ht hc1.2.2.1 hc.2.2.1 hs.delta_nonneg
        hc1.2.2.2.1 hc.2.2.2.1 hc1.2.2.2.2 hc.2.2.2.2 hb hw
      rw [hp _ _ hc1.2.2.1]
      change m + (1 / 500) * (childH u - h) ≤ _ at hg
      change (capChild lam Y - u) / 2 ≤ childH u - h at hheight
      linarith only [hg, hheight]

theorem fixedParentCap_of_scalar_bounds (r : Row)
    (hs : ∀ lam Y rho, InRow r lam → 0 < Y → parentH Y ≤ q lam →
      FeasibleVacancy lam Y rho → CapScalarBounds r lam Y rho) : FixedParentCap r := by
  intro lam Y rho hr hY hH hV
  exact cap_fixed_parent_of_scalar_bounds r lam Y rho (hs lam Y rho hr hY hH hV)

end
end F4Heavy.Analysis
