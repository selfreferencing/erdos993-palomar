module

public import F4Heavy.Analysis.EUpperResponse
public import F4Heavy.Analysis.ESupportCoverage

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem e_support_heights_nonnegative (r : Row) (lam : ℝ)
    (he : r = .E1 ∨ r = .E2) (hr : InRow r lam) (i : Fin 4) :
    0 ≤ eSupportHeight r lam i := by
  have h := e_support_height_positive r lam he hr
  rcases i with ⟨i, hi⟩
  interval_cases i
  · exact le_refl 0
  · exact h.1.le
  · exact h.2.1.le
  · exact h.2.2.le

theorem e_upper_response_original (r : Row) (lam Y u y L : ℝ) (hlam : 0 < lam) :
    responsePolynomial (eUpperA r lam (parentX lam Y)) (eUpperB r lam (parentX lam Y))
      (eUpperC r lam (parentX lam Y)) (eUpperD r lam (parentX lam Y))
      (delta r lam) L (childH u) y =
    responsePolynomial
      (p lam Y*tangentN r lam Y 1 (3/4) (eParentBase r lam Y+(1-p lam Y))/
        parentLogLower r lam (parentX lam Y))
      (p lam Y*beta r lam) (p lam Y*(2*(eParentBase r lam Y+(1-p lam Y))-alpha r lam-beta r lam))
      (gamma r lam-delta r lam-p lam Y*parentLogUpper r lam (parentX lam Y)*
        (eParentBase r lam Y+(1-p lam Y))) (delta r lam) L (childH u) y := by
  unfold eUpperA eUpperB eUpperC eUpperD eUpperParentX
  rw [eProbabilityX_original lam Y hlam, eParentBaseX_original r lam Y hlam,
    eHeavyKX_original r lam Y hlam]
  unfold responsePolynomial tangentN
  ring

theorem e_upper_payment_of_support_chord (r : Row) (lam Y u y t : ℝ) (i j : Fin 4)
    (he : r = .E1 ∨ r = .E2) (hr : InRow r lam)
    (hx : (1/4 : ℝ) ≤ parentX lam Y ∧ parentX lam Y ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hadm : Admissible lam u y)
    (hh : childH u = (1-t)*eSupportVertex r lam i+t*eSupportVertex r lam j)
    (hJL : childJ lam u ≤ (1-t)*eSupportHeight r lam i+t*eSupportHeight r lam j) :
    0 < mixedPayment r lam Y 1 u y (3/4) (eParentBase r lam Y+(1-p lam Y))
      (parentLogLower r lam (parentX lam Y)) (parentLogUpper r lam (parentX lam Y)) := by
  let L := (1-t)*eSupportHeight r lam i+t*eSupportHeight r lam j
  have hL0 : 0 ≤ L := add_nonneg
    (mul_nonneg (sub_nonneg.mpr ht1) (e_support_heights_nonnegative r lam he hr i))
    (mul_nonneg ht0 (e_support_heights_nonnegative r lam he hr j))
  have hG : 0 < delta r lam+eUpperD r lam (parentX lam Y)*L := by
    rw [response_gain_chord]
    exact positive_chord _ _ t (e_upper_response_vertex_gains r lam _ he hr hx i)
      (e_upper_response_vertex_gains r lam _ he hr hx j) ht0 ht1
  have hW := e_upper_response_chord_positive r lam (parentX lam Y) t i j he hr hx ht0 ht1
  rw [← hh] at hW
  have hresp : 0 < responsePolynomial (eUpperA r lam (parentX lam Y))
      (eUpperB r lam (parentX lam Y)) (eUpperC r lam (parentX lam Y))
      (eUpperD r lam (parentX lam Y)) (delta r lam) L (childH u) y := by
    by_cases hL : 0 < L
    · exact response_positive _ _ _ _ _ _ _ _ hL hG hW
    · have hzero : L = 0 := le_antisymm (le_of_not_gt hL) hL0
      have hy : y = childH u := by
        rcases hadm with hJ | ⟨_, hy⟩
        · change childJ lam u ≤ L at hJL
          linarith only [hJ, hJL, hzero]
        · exact hy
      change 0 < responseNumerator _ _ _ _ _ L _ at hW
      rw [hzero] at hW
      rw [hzero, hy]
      exact response_zero_vertex_positive _ _ _ _ _ _ (row_delta_pos r lam hr) hW
  rw [e_upper_response_original r lam Y u y L (inRow_activity_pos r lam hr)] at hresp
  exact mixedPayment_positive_of_response r lam Y 1 u y (3/4)
    (eParentBase r lam Y+(1-p lam Y)) _ _ L (row_delta_pos r lam hr).le hadm hJL
    (by simpa only [mul_one] using hresp)

/-- All E certificates and upper response segments are discharged. The remaining
input consists solely of the three original analytic child support bounds. -/
theorem e_compactHeavy_of_support_lines (r : Row) (he : r = .E1 ∨ r = .E2)
    (hlines : ∀ lam u : ℝ, InRow r lam → 0 ≤ u → u ≤ q lam →
      childJ lam u ≤ (7/3)*childH u+eSupportIntercept0 r lam ∧
      childJ lam u ≤ (3/10)*childH u+eSupportIntercept1 r lam ∧
      childJ lam u ≤ (-8/15)*childH u+eSupportIntercept2 r lam) : CompactHeavy r := by
  intro lam Y rho u y hdom hx0 hx1
  rcases hdom with ⟨hr, hY, hrho, hu0, hcap, hadm⟩
  have hlam := inRow_activity_pos r lam hr
  have huq : u ≤ q lam := hcap.trans (min_le_left _ _)
  have hq1 : q lam < 1 := (div_lt_one (by linarith : 0 < 1+lam)).mpr (by linarith)
  have hl := hlines lam u hr hu0 huq
  have hJ : 0 ≤ childJ lam u := by
    rcases hadm with hJ | ⟨hJ, _⟩
    · exact hJ.le
    · exact le_of_eq hJ.symm
  have hh0 := e_support_lower_vertex_of_first_bound r lam (childH u) (childJ lam u) hJ hl.1
  obtain ⟨i, j, t, ht0, ht1, hh, hJL⟩ := e_support_chord_coverage r lam (childH u)
    (childJ lam u) he hr hh0 (childH_upper_one u hu0 (huq.trans_lt hq1)) hl.1 hl.2.1 hl.2.2
  exact e_payment_positive_of_upper_endpoint r lam Y rho u y he hr hY hx0 hx1 hrho
    (e_upper_payment_of_support_chord r lam Y u y t i j he hr
      ⟨e_parent_domain_quarter r lam Y he hx0, hx1⟩ ht0 ht1 hadm hh hJL)

end F4Heavy.Analysis
