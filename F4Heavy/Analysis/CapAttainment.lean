module

public import F4Heavy.Analysis.CapTwoPoint
public import F4Heavy.Analysis.PaymentReduction

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified
noncomputable section

/-- The response at the attained minimum, with the parent data held fixed. -/
def capResponse (c d delta J h : ℝ) : ℝ :=
  (2 * delta * h - c * J) / (2 * (delta + d * J))

theorem cap_response_curvature (c d delta J h : ℝ)
    (hh : 0 < h) (hJ : 0 < J)
    (hK : 0 < 2 * delta * h - c * J) (hr : 0 < c + 2 * d * h) :
    0 < delta + d * J := by
  have hid : 2 * h * (delta + d * J) =
      (2 * delta * h - c * J) + J * (c + 2 * d * h) := by ring
  have hp := mul_pos hJ hr
  nlinarith only [hid, hp, hK, hh]

theorem cap_response_stationary (c d delta J h : ℝ)
    (hJ : J ≠ 0) (hG : delta + d * J ≠ 0) :
    c + 2 * d * capResponse c d delta J h -
      2 * delta / J * (h - capResponse c d delta J h) = 0 := by
  unfold capResponse
  field_simp [hG]
  <;> ring

theorem cap_response_gap (c d delta J h : ℝ) (hG : delta + d * J ≠ 0) :
    h - capResponse c d delta J h = J * (c + 2 * d * h) / (2 * (delta + d * J)) := by
  have hd : 2 * (delta + d * J) ≠ 0 := mul_ne_zero (by norm_num) hG
  apply (eq_div_iff hd).mpr
  unfold capResponse
  rw [sub_mul, div_mul_cancel₀ _ hd]
  ring

theorem cap_response_interior (c d delta J h : ℝ)
    (hh : 0 < h) (hJ : 0 < J)
    (hK : 0 < 2 * delta * h - c * J) (hr : 0 < c + 2 * d * h) :
    0 < capResponse c d delta J h ∧ capResponse c d delta J h < h := by
  have hG := cap_response_curvature c d delta J h hh hJ hK hr
  constructor
  · exact div_pos hK (mul_pos (by norm_num) hG)
  · have hg := cap_response_gap c d delta J h (ne_of_gt hG)
    have hp := div_pos (mul_pos hJ hr) (mul_pos (by norm_num : (0 : ℝ) < 2) hG)
    linarith only [hg, hp]

theorem cap_response_attained_lower (a b c d delta J h y : ℝ)
    (hJ : 0 < J) (hG : 0 < delta + d * J) :
    responsePolynomial a b c d delta J h (capResponse c d delta J h) ≤
      responsePolynomial a b c d delta J h y := by
  have hy : capResponse c d delta J h = (delta * h - J * c / 2) / (delta + d * J) := by
    unfold capResponse
    field_simp [ne_of_gt hG]
    <;> ring
  rw [response_complete a b c d delta J h y (ne_of_gt hJ) (ne_of_gt hG),
    response_complete a b c d delta J h _ (ne_of_gt hJ) (ne_of_gt hG), hy]
  simp only [sub_self, zero_pow (by norm_num : 2 ≠ 0), mul_zero, add_zero]
  exact le_add_of_nonneg_right (mul_nonneg (div_pos hG hJ).le (sq_nonneg _))

theorem cap_stationary_two_point_gain (b c d delta h1 h2 z1 z2 v1 v2 eps : ℝ)
    (ht : h2 ≤ h1) (hd : 0 ≤ delta) (hv1 : 0 ≤ v1) (hv2 : 0 ≤ v2)
    (hz10 : 0 ≤ z1) (hz11 : z1 ≤ 1) (hz20 : 0 ≤ z2) (hz21 : z2 ≤ 1)
    (hs1 : c + 2 * d * (h1 * (1 - z1)) - 2 * delta * v1 * z1 = 0)
    (hs2 : c + 2 * d * (h2 * (1 - z2)) - 2 * delta * v2 * z2 = 0)
    (hb : eps * (h1 - h2) ≤ b * (h1 - h2))
    (hw : eps * (h1 - h2) ≤ b * (h1 - h2) + delta * (h1 * v1 - h2 * v2)) :
    eps * (h1 - h2) ≤
      capPointValue b c d delta h1 z1 v1 - capPointValue b c d delta h2 z2 v2 := by
  have hid := cap_two_point_residual b c d delta h1 h2 z1 z2 v1 v2
  rw [hs1, hs2] at hid
  have hg := cap_two_point_gain b delta (h1 - h2) v1 v2 z1 z2
    (h1 * v1 - h2 * v2) eps (sub_nonneg.mpr ht) hd hv1 hv2 hz10 hz11 hz20 hz21 hb hw
  nlinarith only [hid, hg]

theorem cap_payment_response (r : Row) (lam Y rho u y : ℝ) (hJ : 0 < childJ lam u) :
    payment r lam Y rho u y = responsePolynomial
      (p lam Y * parentN r lam Y rho / Y) (p lam Y * beta r lam * rho)
      (p lam Y * (2 * parentP r lam Y rho - alpha r lam - beta r lam))
      (gamma r lam - delta r lam - p lam Y * Y * parentP r lam Y rho)
      (delta r lam) (childJ lam u) (childH u) y := by
  unfold payment reserve responsePolynomial
  rw [if_pos hJ]
  ring

theorem cap_payment_attainment (r : Row) (lam Y rho u : ℝ)
    (hJ : 0 < childJ lam u)
    (hG : 0 < delta r lam +
      (gamma r lam - delta r lam - p lam Y * Y * parentP r lam Y rho) * childJ lam u) :
    ∃ m, MinAt r lam Y rho u m := by
  apply Exists.intro
    (payment r lam Y rho u (capResponse
      (p lam Y * (2 * parentP r lam Y rho - alpha r lam - beta r lam))
      (gamma r lam - delta r lam - p lam Y * Y * parentP r lam Y rho)
      (delta r lam) (childJ lam u) (childH u)))
  constructor
  · intro y _
    rw [cap_payment_response r lam Y rho u _ hJ, cap_payment_response r lam Y rho u y hJ]
    exact cap_response_attained_lower _ _ _ _ _ _ _ _ hJ hG
  · exact ⟨_, Or.inl hJ, rfl⟩

end
end F4Heavy.Analysis
