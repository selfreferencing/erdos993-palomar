module

public import F4Heavy.Analysis.TailCurvatureBounds
public import F4Heavy.Analysis.TailLinearBounds
public import F4Heavy.Analysis.CapAttainment

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

noncomputable def tailModel (r : Row) (lam J h y : ℝ) : ℝ :=
  responsePolynomial (tailA r lam) (beta r lam) (tailC r lam) (tailD r lam)
    (tailReserveK r lam) J h y

theorem tail_reserve_coefficient_lower (r : Row) (lam Y : ℝ) (hr : InRow r lam)
    (hY : tailTau r lam ≤ Y) : tailReserveK r lam ≤ delta r lam / p lam Y := by
  have hl := inRow_activity_pos r lam hr
  have hp := p_pos lam Y hl
  have hpstar : p lam Y ≤ tailPStar r lam := by
    rw [← tail_probability_at_threshold r lam hl]
    exact tail_probability_antitone lam (tailTau r lam) Y hl hY
  exact div_le_div_of_nonneg_left (row_delta_pos r lam hr).le hp hpstar

theorem tail_curvature_gain (K K0 d D J C : ℝ) (hK0 : 0 < K0) (hK : K0 ≤ K)
    (hd : D ≤ d) (hJ : 0 < J) (hJC : J ≤ C) (hguard : 0 < K0 + D * C) :
    0 < K + d * J := by
  have hprod := mul_le_mul_of_nonneg_right hd hJ.le
  by_cases hD : D ≤ 0
  · have hm := mul_le_mul_of_nonpos_left hJC hD
    linarith only [hguard, hprod, hm, hK]
  · have hpos : 0 ≤ d := (le_of_not_ge hD).trans hd
    exact add_pos_of_pos_of_nonneg (hK0.trans_le hK) (mul_nonneg hpos hJ.le)

theorem tail_one_endpoint_lower (r : Row) (lam Y u y : ℝ) (hr : InRow r lam)
    (hY : tailTau r lam ≤ Y) (hy : 0 ≤ y) (hJ : 0 < childJ lam u)
    (hguards : ∀ i, 1 ≤ i → i ≤ 9 → 0 < tailGuard r lam i) :
    tailModel r lam (childJ lam u) (childH u) y ≤ tailEndpointOne r lam Y u y := by
  have ha := tail_source_lower_of_guards r lam Y hr hY
    (hguards 1 (by omega) (by omega)) (hguards 2 (by omega) (by omega))
    (hguards 6 (by omega) (by omega)) (hguards 7 (by omega) (by omega))
  have hc := mul_le_mul_of_nonneg_right (tail_linear_lower r lam Y hr hY) hy
  have hd := mul_le_mul_of_nonneg_right (tail_curvature_lower_of_guards r lam Y hr hY
    (hguards 1 (by omega) (by omega)) (hguards 2 (by omega) (by omega))
    (hguards 8 (by omega) (by omega)) (hguards 9 (by omega) (by omega))) (sq_nonneg y)
  have hK := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (tail_reserve_coefficient_lower r lam Y hr hY) hJ.le)
    (sq_nonneg (childH u - y))
  unfold tailModel tailEndpointOne responsePolynomial
  linarith only [ha, hc, hd, hK]

theorem tail_one_endpoint_positive_of_model (r : Row) (lam Y u y : ℝ)
    (hr : InRow r lam) (hY : tailTau r lam ≤ Y) (hu : 0 < u) (hu1 : u < 1)
    (hJ : 0 < childJ lam u) (hJC : childJ lam u ≤ tailChildC lam)
    (hguards : ∀ i, 1 ≤ i → i ≤ 13 → 0 < tailGuard r lam i)
    (hmodel : ∀ z, 0 < tailModel r lam (childJ lam u) (childH u) z) :
    0 < tailEndpointOne r lam Y u y := by
  let a := (tailK r lam * p lam Y - tailP1 r lam (p lam Y)) / Y
  let c := 2 * tailP1 r lam (p lam Y) - alpha r lam - beta r lam
  let d := (gamma r lam - delta r lam) / p lam Y - Y * tailP1 r lam (p lam Y)
  let K := delta r lam / p lam Y
  have hK0 : 0 < tailReserveK r lam := by
    unfold tailReserveK
    have hs : 0 < tailPStar r lam := by
      rw [← tail_probability_at_threshold r lam (inRow_activity_pos r lam hr)]
      exact p_pos lam _ (inRow_activity_pos r lam hr)
    exact div_pos (row_delta_pos r lam hr) hs
  have hG : 0 < K + d * childJ lam u := tail_curvature_gain K (tailReserveK r lam) d
    (tailD r lam) (childJ lam u) (tailChildC lam) hK0
    (tail_reserve_coefficient_lower r lam Y hr hY)
    (tail_curvature_lower_of_guards r lam Y hr hY
      (hguards 1 (by omega) (by omega)) (hguards 2 (by omega) (by omega))
      (hguards 8 (by omega) (by omega)) (hguards 9 (by omega) (by omega))) hJ hJC
    (hguards 13 (by omega) (by omega))
  have hnum : 0 < 2 * K * childH u - c * childJ lam u :=
    tail_response_positive_numerator r lam Y u hr hY hu hu1
      (hguards 10 (by omega) (by omega)) (hguards 11 (by omega) (by omega))
      (hguards 12 (by omega) (by omega))
  have hz : 0 < capResponse c d K (childJ lam u) (childH u) := by
    unfold capResponse
    exact div_pos hnum (by positivity)
  have hlow := tail_one_endpoint_lower r lam Y u (capResponse c d K (childJ lam u) (childH u))
    hr hY hz.le hJ (fun i hi hj => hguards i hi (by omega))
  have hmin := cap_response_attained_lower a (beta r lam) c d K (childJ lam u) (childH u) y hJ hG
  exact ((hmodel _).trans_le hlow).trans_le hmin

end F4Heavy.Analysis
