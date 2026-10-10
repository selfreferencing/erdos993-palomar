module

public import F4Heavy.Analysis.ActivityEnclosure
public import F4Heavy.Analysis.HeavyReduction

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

noncomputable def mixedPayment (r : Row) (lam Y rho u y theta P lo hi : ℝ) : ℝ :=
  p lam Y * tangentN r lam Y rho theta P / lo +
  p lam Y * beta r lam * rho * childH u +
  p lam Y * (2 * P - alpha r lam - beta r lam) * y +
  (gamma r lam - delta r lam - p lam Y * hi * P) * y ^ 2 + reserve r lam u y

theorem mixed_log_difference (p N P Y lo hi y : ℝ) (hY : Y ≠ 0) (hlo : lo ≠ 0) :
    p * N / Y - p * Y * P * y ^ 2 - (p * N / lo - p * hi * P * y ^ 2) =
      p * (-N) * (Y - lo) / (Y * lo) + p * P * (hi - Y) * y ^ 2 := by
  field_simp
  ring

theorem mixed_log_lower_bound (p N P Y lo hi y : ℝ) (hp : 0 ≤ p) (hN : N ≤ 0)
    (hP : 0 ≤ P) (hlo : 0 < lo) (hloY : lo ≤ Y) (hYhi : Y ≤ hi) :
    p * N / lo - p * hi * P * y ^ 2 ≤ p * N / Y - p * Y * P * y ^ 2 := by
  have hY : 0 < Y := hlo.trans_le hloY
  have hid := mixed_log_difference p N P Y lo hi y (ne_of_gt hY) (ne_of_gt hlo)
  have hfirst : 0 ≤ p * (-N) * (Y - lo) / (Y * lo) :=
    div_nonneg (mul_nonneg (mul_nonneg hp (neg_nonneg.mpr hN)) (sub_nonneg.mpr hloY))
      (mul_pos hY hlo).le
  have hsecond : 0 ≤ p * P * (hi - Y) * y ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg hp hP) (sub_nonneg.mpr hYhi)) (sq_nonneg y)
  linarith only [hid, hfirst, hsecond]

theorem mixedPayment_source_difference (r : Row) (lam Y rho u y theta P : ℝ)
    (hlam : 0 < lam) (hrho : FeasibleVacancy lam Y rho) (hx : parentX lam Y ≤ 1) :
    paymentWithParent r lam Y rho u y P - mixedPayment r lam Y rho u y theta P Y Y =
      p lam Y / Y * heavyK r lam Y * (rho - theta) ^ 2 := by
  unfold paymentWithParent mixedPayment tangentN
  rw [heavy_source_term r lam Y rho hlam hrho hx]
  simp only [div_eq_mul_inv]
  ring

theorem mixedPayment_log_lower_bound (r : Row) (lam Y rho u y theta P lo hi : ℝ)
    (hp : 0 ≤ p lam Y) (hN : tangentN r lam Y rho theta P ≤ 0) (hP : 0 ≤ P)
    (hlo : 0 < lo) (hloY : lo ≤ Y) (hYhi : Y ≤ hi) :
    mixedPayment r lam Y rho u y theta P lo hi ≤ mixedPayment r lam Y rho u y theta P Y Y := by
  have h := mixed_log_lower_bound (p lam Y) (tangentN r lam Y rho theta P) P Y lo hi y
    hp hN hP hlo hloY hYhi
  unfold mixedPayment
  linarith only [h]

theorem mixedPayment_lower_bound (r : Row) (lam Y rho u y theta P lo hi : ℝ)
    (hr : InRow r lam) (hY : 0 < Y) (hrho : FeasibleVacancy lam Y rho)
    (hx : parentX lam Y ≤ 1) (hP : parentP r lam Y rho ≤ P) (hP0 : 0 ≤ P)
    (hN : tangentN r lam Y rho theta P ≤ 0) (hlo : 0 < lo) (hloY : lo ≤ Y) (hYhi : Y ≤ hi) :
    mixedPayment r lam Y rho u y theta P lo hi ≤ payment r lam Y rho u y := by
  have hlam := inRow_activity_pos r lam hr
  have hp := p_pos lam Y hlam
  have hsource := mixedPayment_source_difference r lam Y rho u y theta P hlam hrho hx
  have hparent := parent_replacement_lower_bound r lam Y rho u y P hp.le hY hP
  have hlog := mixedPayment_log_lower_bound r lam Y rho u y theta P lo hi hp.le hN hP0 hlo hloY hYhi
  have hs := mul_nonneg (mul_nonneg (div_pos hp hY).le (heavyK_pos r lam Y hr).le) (sq_nonneg (rho - theta))
  linarith only [hsource, hparent, hlog, hs]

theorem mixedPayment_vacancy_chord (r : Row) (lam Y u y theta P0 P1 lo hi ra rb t : ℝ) :
    mixedPayment r lam Y ((1 - t) * ra + t * rb) u y theta
      (P0 + P1 * ((1 - t) * ra + t * rb)) lo hi =
    (1 - t) * mixedPayment r lam Y ra u y theta (P0 + P1 * ra) lo hi +
      t * mixedPayment r lam Y rb u y theta (P0 + P1 * rb) lo hi := by
  unfold mixedPayment tangentN
  simp only [div_eq_mul_inv]
  ring

theorem mixedPayment_zero_one (r : Row) (lam Y rho u y theta P0 P1 lo hi : ℝ) :
    mixedPayment r lam Y rho u y theta (P0 + P1 * rho) lo hi =
    (1 - rho) * mixedPayment r lam Y 0 u y theta P0 lo hi +
      rho * mixedPayment r lam Y 1 u y theta (P0 + P1) lo hi := by
  simpa only [mul_zero, add_zero, mul_one, zero_add] using
    mixedPayment_vacancy_chord r lam Y u y theta P0 P1 lo hi 0 1 rho

theorem mixedPayment_positive_of_endpoints (r : Row) (lam Y rho u y theta P0 P1 lo hi : ℝ)
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hzero : 0 < mixedPayment r lam Y 0 u y theta P0 lo hi)
    (hone : 0 < mixedPayment r lam Y 1 u y theta (P0 + P1) lo hi) :
    0 < mixedPayment r lam Y rho u y theta (P0 + P1 * rho) lo hi := by
  rw [mixedPayment_zero_one]
  exact positive_chord _ _ rho hzero hone hrho0 hrho1

theorem payment_positive_of_mixed_endpoints (r : Row) (lam Y rho u y theta P0 P1 : ℝ)
    (hr : InRow r lam) (hY : 0 < Y) (hrho : FeasibleVacancy lam Y rho)
    (hx0 : (rowData r).xMin ≤ parentX lam Y) (hx1 : parentX lam Y ≤ 1)
    (hP : parentP r lam Y rho ≤ P0 + P1 * rho) (hP0 : 0 ≤ P0 + P1 * rho)
    (hN : tangentN r lam Y rho theta (P0 + P1 * rho) ≤ 0)
    (hzero : 0 < mixedPayment r lam Y 0 u y theta P0
      (parentLogLower r lam (parentX lam Y)) (parentLogUpper r lam (parentX lam Y)))
    (hone : 0 < mixedPayment r lam Y 1 u y theta (P0 + P1)
      (parentLogLower r lam (parentX lam Y)) (parentLogUpper r lam (parentX lam Y))) :
    0 < payment r lam Y rho u y := by
  have hlogs := original_parent_log_enclosure r lam Y hr hx0 hx1
  have hrhop := feasible_vacancy_pos lam Y rho (inRow_activity_pos r lam hr) hrho
  exact lt_of_lt_of_le
    (mixedPayment_positive_of_endpoints r lam Y rho u y theta P0 P1 _ _ hrhop.le hrho.2 hzero hone)
    (mixedPayment_lower_bound r lam Y rho u y theta (P0 + P1 * rho) _ _ hr hY hrho hx1 hP hP0 hN
      hlogs.1 hlogs.2.1 hlogs.2.2)

theorem reserve_nonnegative (r : Row) (lam u y : ℝ) (hr : InRow r lam) : 0 ≤ reserve r lam u y := by
  unfold reserve
  split
  · rename_i hJ
    exact div_nonneg (mul_nonneg (row_delta_pos r lam hr).le (sq_nonneg _)) hJ.le
  · exact le_refl 0

theorem mixed_virtual_quadratic_positive (p C e d lo y : ℝ) (hp : 0 < p) (hC : 0 < C)
    (hlo : 0 < lo) (hdisc : 0 < 4 * d * C - p * lo * e ^ 2) :
    0 < p * C / lo + p * e * y + d * y ^ 2 := by
  have hterm : 0 ≤ p * lo * e ^ 2 := mul_nonneg (mul_pos hp hlo).le (sq_nonneg e)
  have hd : 0 < d := by nlinarith only [hC, hdisc, hterm]
  have hid : 4 * d * (p * C / lo) - (p * e) ^ 2 =
      p / lo * (4 * d * C - p * lo * e ^ 2) := by
    field_simp
  have hq := quadratic_positive d (p * e) (p * C / lo) y hd
    (by rw [hid]; exact mul_pos (div_pos hp hlo) hdisc)
  linarith only [hq]

theorem mixedPayment_virtual_positive (r : Row) (lam Y u y theta P0 lo hi : ℝ)
    (hr : InRow r lam) (hlo : 0 < lo) (hC : 0 < tangentN r lam Y 0 theta P0)
    (hdisc : 0 < 4 * (gamma r lam - delta r lam - p lam Y * hi * P0) *
      tangentN r lam Y 0 theta P0 - p lam Y * lo * (2 * P0 - alpha r lam - beta r lam) ^ 2) :
    0 < mixedPayment r lam Y 0 u y theta P0 lo hi := by
  have hq := mixed_virtual_quadratic_positive (p lam Y) (tangentN r lam Y 0 theta P0)
    (2 * P0 - alpha r lam - beta r lam) (gamma r lam - delta r lam - p lam Y * hi * P0)
    lo y (p_pos lam Y (inRow_activity_pos r lam hr)) hC hlo hdisc
  have hres := reserve_nonnegative r lam u y hr
  unfold mixedPayment
  simp only [mul_zero, zero_mul, add_zero]
  linarith only [hq, hres]

end F4Heavy.Analysis
