module

public import F4Heavy.Analysis.HeavyDomain

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem row_price_pos (r : Row) : 0 < (rowData r).price := by
  cases r <;> norm_num [rowData]

theorem row_delta_pos (r : Row) (lam : ℝ) (hr : InRow r lam) : 0 < delta r lam := by
  cases r <;> norm_num [InRow, rowData] at hr <;>
    simp only [delta, field, rowData] <;> nlinarith [hr.1, hr.2]

noncomputable def heavyK (r : Row) (lam Y : ℝ) : ℝ :=
  (rowData r).price / (1 + lam) * ((1 + q lam) / (2 * q lam)) * p lam Y

noncomputable def tangentN (r : Row) (lam Y rho theta P : ℝ) : ℝ :=
  heavyK r lam Y * (2 * theta * rho - theta ^ 2) + alpha r lam * (1 - rho) - P

noncomputable def supportPayment (r : Row) (lam Y rho u y theta P L : ℝ) : ℝ :=
  p lam Y * tangentN r lam Y rho theta P / Y +
  p lam Y * beta r lam * rho * childH u +
  p lam Y * (2 * P - alpha r lam - beta r lam) * y +
  (gamma r lam - delta r lam - p lam Y * Y * P) * y ^ 2 +
  delta r lam * (childH u - y) ^ 2 / L

theorem heavyK_pos (r : Row) (lam Y : ℝ) (hr : InRow r lam) : 0 < heavyK r lam Y := by
  have hlam := inRow_activity_pos r lam hr
  have hq := q_pos lam hlam
  have hp := p_pos lam Y hlam
  have hprice := row_price_pos r
  unfold heavyK
  positivity

theorem heavy_source_term (r : Row) (lam Y rho : ℝ) (hlam : 0 < lam)
    (hrho : FeasibleVacancy lam Y rho) (hx : parentX lam Y ≤ 1) :
    (rowData r).price / (1 + lam) * rho * source lam Y rho = heavyK r lam Y * rho ^ 2 := by
  rw [heavy_source_identity lam Y rho hlam hrho hx]
  unfold heavyK
  ring

theorem supportPayment_difference (r : Row) (lam Y rho u y theta P L : ℝ)
    (hlam : 0 < lam) (hrho : FeasibleVacancy lam Y rho) (hx : parentX lam Y ≤ 1) :
    paymentWithParent r lam Y rho u y P - supportPayment r lam Y rho u y theta P L =
      p lam Y / Y * heavyK r lam Y * (rho - theta) ^ 2 +
        reserve r lam u y - delta r lam * (childH u - y) ^ 2 / L := by
  unfold paymentWithParent supportPayment tangentN
  rw [heavy_source_term r lam Y rho hlam hrho hx]
  simp only [div_eq_mul_inv]
  ring

theorem supportPayment_lower_bound (r : Row) (lam Y rho u y theta P L : ℝ)
    (hr : InRow r lam) (hY : 0 < Y) (hrho : FeasibleVacancy lam Y rho)
    (hx : parentX lam Y ≤ 1) (hP : parentP r lam Y rho ≤ P)
    (hJ : 0 < childJ lam u) (hJL : childJ lam u ≤ L) :
    supportPayment r lam Y rho u y theta P L ≤ payment r lam Y rho u y := by
  have hlam := inRow_activity_pos r lam hr
  have hp := p_pos lam Y hlam
  have hK := heavyK_pos r lam Y hr
  have hd := row_delta_pos r lam hr
  have hreserve := reserve_envelope_lower_bound r lam u y L hd.le hJ hJL
  have hs := mul_nonneg (mul_nonneg (div_pos hp hY).le hK.le) (sq_nonneg (rho - theta))
  have hid := supportPayment_difference r lam Y rho u y theta P L hlam hrho hx
  have hparent := parent_replacement_lower_bound r lam Y rho u y P hp.le hY hP
  linarith

theorem supportPayment_as_response (r : Row) (lam Y rho u y theta P L : ℝ) :
    supportPayment r lam Y rho u y theta P L =
      responsePolynomial (p lam Y * tangentN r lam Y rho theta P / Y)
        (p lam Y * beta r lam * rho)
        (p lam Y * (2 * P - alpha r lam - beta r lam))
        (gamma r lam - delta r lam - p lam Y * Y * P)
        (delta r lam) L (childH u) y := by
  unfold supportPayment responsePolynomial
  simp only [div_eq_mul_inv]
  ring

theorem payment_positive_of_support_certificate (r : Row) (lam Y rho u y theta P L : ℝ)
    (hr : InRow r lam) (hY : 0 < Y) (hrho : FeasibleVacancy lam Y rho)
    (hx : parentX lam Y ≤ 1) (hP : parentP r lam Y rho ≤ P)
    (hJ : 0 < childJ lam u) (hJL : childJ lam u ≤ L)
    (hG : 0 < delta r lam + (gamma r lam - delta r lam - p lam Y * Y * P) * L)
    (hW : 0 < responseNumerator (p lam Y * tangentN r lam Y rho theta P / Y)
      (p lam Y * beta r lam * rho) (p lam Y * (2 * P - alpha r lam - beta r lam))
      (gamma r lam - delta r lam - p lam Y * Y * P) (delta r lam) L (childH u)) :
    0 < payment r lam Y rho u y := by
  apply lt_of_lt_of_le _ (supportPayment_lower_bound r lam Y rho u y theta P L hr hY hrho hx hP hJ hJL)
  rw [supportPayment_as_response]
  exact response_positive _ _ _ _ _ _ _ _ (lt_of_lt_of_le hJ hJL) hG hW

end F4Heavy.Analysis
