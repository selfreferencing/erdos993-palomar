module

public import F4Heavy.Analysis.TailDomain

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified
noncomputable section

def tailEndpointZero (r : Row) (lam Y u y : ℝ) : ℝ :=
  responsePolynomial
    ((alpha r lam - gamma r lam * tailV (p lam Y) - tailS r lam * p lam Y / 4) / Y)
    0 (2 * gamma r lam * tailV (p lam Y) - alpha r lam - beta r lam)
    ((gamma r lam - delta r lam) / p lam Y - Y * gamma r lam * tailV (p lam Y))
    (delta r lam / p lam Y) (childJ lam u) (childH u) y

def tailEndpointOne (r : Row) (lam Y u y : ℝ) : ℝ :=
  responsePolynomial ((tailK r lam * p lam Y - tailP1 r lam (p lam Y)) / Y)
    (beta r lam) (2 * tailP1 r lam (p lam Y) - alpha r lam - beta r lam)
    ((gamma r lam - delta r lam) / p lam Y - Y * tailP1 r lam (p lam Y))
    (delta r lam / p lam Y) (childJ lam u) (childH u) y

theorem tail_source_mixture_identity (r : Row) (lam Y rho u y : ℝ)
    (hl : 0 < lam) (hY : 0 < Y) (hrho : FeasibleVacancy lam Y rho)
    (hx : parentX lam Y ≤ 1) (hJ : 0 < childJ lam u) :
    paymentWithParent r lam Y rho u y
        (rho * (1 - p lam Y) + gamma r lam * tailV (p lam Y)) / p lam Y -
      ((1 - rho) * tailEndpointZero r lam Y u y + rho * tailEndpointOne r lam Y u y) =
        tailS r lam * p lam Y / Y * (rho - 1 / 2) ^ 2 := by
  have hp := p_pos lam Y hl
  unfold paymentWithParent
  rw [heavy_source_term r lam Y rho hl hrho hx]
  unfold tailEndpointZero tailEndpointOne responsePolynomial tailP1 tailK reserve
  rw [if_pos hJ]
  change _ = tailS r lam * p lam Y / Y * (rho - 1 / 2) ^ 2
  have hk : heavyK r lam Y = tailS r lam * p lam Y := rfl
  rw [hk]
  field_simp
  <;> ring

theorem tail_source_mixture_lower (r : Row) (lam Y rho u y : ℝ) (hr : InRow r lam)
    (hY : 0 < Y) (hrho : FeasibleVacancy lam Y rho)
    (hx : parentX lam Y ≤ 1) (hJ : 0 < childJ lam u) :
    (1 - rho) * tailEndpointZero r lam Y u y + rho * tailEndpointOne r lam Y u y ≤
      payment r lam Y rho u y / p lam Y := by
  have hl := inRow_activity_pos r lam hr
  have hp := p_pos lam Y hl
  have hreplace := parent_replacement_lower_bound r lam Y rho u y
    (rho * (1 - p lam Y) + gamma r lam * tailV (p lam Y)) hp.le hY
    (parentP_quadratic_upper r lam Y rho hr)
  have hdiv := div_le_div_of_nonneg_right hreplace hp.le
  have hid := tail_source_mixture_identity r lam Y rho u y hl hY hrho hx hJ
  have hnon := mul_nonneg (div_nonneg (mul_nonneg (tailS_positive r lam hl).le hp.le) hY.le)
    (sq_nonneg (rho - 1 / 2))
  linarith only [hdiv, hid, hnon]

theorem tail_payment_positive_of_endpoints (r : Row) (lam Y rho u y : ℝ)
    (hr : InRow r lam) (hY : 0 < Y) (hrho : FeasibleVacancy lam Y rho)
    (hx : parentX lam Y ≤ 1) (hJ : 0 < childJ lam u)
    (hzero : 0 < tailEndpointZero r lam Y u y)
    (hone : 0 < tailEndpointOne r lam Y u y) : 0 < payment r lam Y rho u y := by
  have hl := inRow_activity_pos r lam hr
  have hv := feasible_vacancy_pos lam Y rho hl hrho
  have hmix := add_pos_of_nonneg_of_pos
    (mul_nonneg (sub_nonneg.mpr hrho.2) hzero.le) (mul_pos hv hone)
  have hpdiv := hmix.trans_le (tail_source_mixture_lower r lam Y rho u y hr hY hrho hx hJ)
  exact (div_pos_iff.mp hpdiv).elim (fun h => h.1) (fun h => False.elim ((not_lt_of_ge (p_pos lam Y hl).le) h.2))

end
end F4Heavy.Analysis
