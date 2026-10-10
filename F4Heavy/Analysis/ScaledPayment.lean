module

public import F4Heavy.Analysis.MixedSupport
public import F4Heavy.Analysis.ESupportCoverage

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

-- The physical probability stays fixed while z ranges over its logarithm enclosure.
noncomputable def scaledPayment (r : Row) (lam Y rho u y theta P z : ℝ) : ℝ :=
  tangentN r lam Y rho theta P + z*beta r lam*rho*childH u +
    z*(2*P-alpha r lam-beta r lam)*y +
    (z*(gamma r lam-delta r lam)/p lam Y-z^2*P)*y^2 +
    z*reserve r lam u y/p lam Y

theorem scaledPayment_log_chord (r : Row) (lam Y rho u y theta P a b t : ℝ) :
    scaledPayment r lam Y rho u y theta P ((1-t)*a+t*b) =
      (1-t)*scaledPayment r lam Y rho u y theta P a +
      t*scaledPayment r lam Y rho u y theta P b + P*t*(1-t)*(b-a)^2*y^2 := by
  unfold scaledPayment
  ring

theorem scaledPayment_log_interval_positive (r : Row) (lam Y rho u y theta P a b z : ℝ)
    (hP : 0 ≤ P) (haz : a ≤ z) (hzb : z ≤ b)
    (ha : 0 < scaledPayment r lam Y rho u y theta P a)
    (hb : 0 < scaledPayment r lam Y rho u y theta P b) :
    0 < scaledPayment r lam Y rho u y theta P z := by
  by_cases hab : a = b
  · have hz : z = a := by linarith only [haz, hzb, hab]
    simpa only [hz] using ha
  · have hab' : a < b := lt_of_le_of_ne (haz.trans hzb) hab
    obtain ⟨t, ht0, ht1, hz⟩ := closed_interval_chord_parameter a b z hab' haz hzb
    rw [hz, scaledPayment_log_chord]
    have hp := positive_chord _ _ t ha hb ht0 ht1
    have hrem : 0 ≤ P*t*(1-t)*(b-a)^2*y^2 := by
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hP ht0)
        (sub_nonneg.mpr ht1)) (sq_nonneg _)) (sq_nonneg _)
    exact add_pos_of_pos_of_nonneg hp hrem

theorem scaledPayment_vacancy_chord (r : Row) (lam Y u y theta P0 P1 z a b t : ℝ) :
    scaledPayment r lam Y ((1-t)*a+t*b) u y theta (P0+P1*((1-t)*a+t*b)) z =
      (1-t)*scaledPayment r lam Y a u y theta (P0+P1*a) z +
      t*scaledPayment r lam Y b u y theta (P0+P1*b) z := by
  unfold scaledPayment tangentN
  ring

theorem scaledPayment_vacancy_interval_positive (r : Row) (lam Y rho u y theta P0 P1 z a b : ℝ)
    (har : a ≤ rho) (hrb : rho ≤ b)
    (ha : 0 < scaledPayment r lam Y a u y theta (P0+P1*a) z)
    (hb : 0 < scaledPayment r lam Y b u y theta (P0+P1*b) z) :
    0 < scaledPayment r lam Y rho u y theta (P0+P1*rho) z := by
  by_cases hab : a = b
  · have hr : rho = a := by linarith only [har, hrb, hab]
    simpa only [hr] using ha
  · have hab' : a < b := lt_of_le_of_ne (har.trans hrb) hab
    obtain ⟨t, ht0, ht1, hr⟩ := closed_interval_chord_parameter a b rho hab' har hrb
    rw [hr, scaledPayment_vacancy_chord]
    exact positive_chord _ _ t ha hb ht0 ht1

theorem scaledPayment_original (r : Row) (lam Y rho u y theta P : ℝ)
    (hp : p lam Y ≠ 0) (hY : Y ≠ 0) :
    p lam Y/Y*scaledPayment r lam Y rho u y theta P Y =
      mixedPayment r lam Y rho u y theta P Y Y := by
  unfold scaledPayment mixedPayment
  field_simp <;> ring

theorem payment_positive_of_scaled (r : Row) (lam Y rho u y theta P : ℝ)
    (hr : InRow r lam) (hY : 0 < Y) (hrho : FeasibleVacancy lam Y rho)
    (hx : parentX lam Y ≤ 1) (hP : parentP r lam Y rho ≤ P)
    (hpos : 0 < scaledPayment r lam Y rho u y theta P Y) :
    0 < payment r lam Y rho u y := by
  have hlam := inRow_activity_pos r lam hr
  have hp := p_pos lam Y hlam
  have hm : 0 < mixedPayment r lam Y rho u y theta P Y Y := by
    rw [← scaledPayment_original r lam Y rho u y theta P (ne_of_gt hp) (ne_of_gt hY)]
    exact mul_pos (div_pos hp hY) hpos
  have hs := mixedPayment_source_difference r lam Y rho u y theta P hlam hrho hx
  have hrem : 0 ≤ p lam Y/Y*heavyK r lam Y*(rho-theta)^2 :=
    mul_nonneg (mul_nonneg (div_pos hp hY).le (heavyK_pos r lam Y hr).le) (sq_nonneg _)
  have hparent := parent_replacement_lower_bound r lam Y rho u y P hp.le hY hP
  linarith only [hm, hs, hrem, hparent]

theorem payment_positive_of_scaled_corners (r : Row) (lam Y rho u y theta P0 P1 a b lo hi : ℝ)
    (hr : InRow r lam) (hY : 0 < Y) (hrho : FeasibleVacancy lam Y rho)
    (hx : parentX lam Y ≤ 1) (hP : parentP r lam Y rho ≤ P0+P1*rho)
    (hPa : 0 ≤ P0+P1*a) (hPb : 0 ≤ P0+P1*b)
    (har : a ≤ rho) (hrb : rho ≤ b) (hlo : lo ≤ Y) (hhi : Y ≤ hi)
    (ha0 : 0 < scaledPayment r lam Y a u y theta (P0+P1*a) lo)
    (ha1 : 0 < scaledPayment r lam Y a u y theta (P0+P1*a) hi)
    (hb0 : 0 < scaledPayment r lam Y b u y theta (P0+P1*b) lo)
    (hb1 : 0 < scaledPayment r lam Y b u y theta (P0+P1*b) hi) :
    0 < payment r lam Y rho u y := by
  apply payment_positive_of_scaled r lam Y rho u y theta (P0+P1*rho) hr hY hrho hx hP
  exact scaledPayment_vacancy_interval_positive r lam Y rho u y theta P0 P1 Y a b har hrb
    (scaledPayment_log_interval_positive r lam Y a u y theta (P0+P1*a) lo hi Y hPa hlo hhi ha0 ha1)
    (scaledPayment_log_interval_positive r lam Y b u y theta (P0+P1*b) lo hi Y hPb hlo hhi hb0 hb1)

theorem scaledPayment_response_lower_bound (r : Row) (lam Y rho u y theta P z L : ℝ)
    (hp : 0 < p lam Y) (hz : 0 < z) (hdelta : 0 ≤ delta r lam)
    (hadm : Admissible lam u y) (hJL : childJ lam u ≤ L) :
    responsePolynomial (p lam Y*tangentN r lam Y rho theta P/z)
      (p lam Y*beta r lam*rho) (p lam Y*(2*P-alpha r lam-beta r lam))
      (gamma r lam-delta r lam-p lam Y*z*P) (delta r lam) L (childH u) y ≤
      p lam Y/z*scaledPayment r lam Y rho u y theta P z := by
  have heq : p lam Y/z*scaledPayment r lam Y rho u y theta P z =
      mixedPayment r lam Y rho u y theta P z z := by
    unfold scaledPayment mixedPayment
    field_simp <;> ring
  rw [heq]
  exact mixedPayment_response_lower_bound r lam Y rho u y theta P z z L hdelta hadm hJL

theorem scaledPayment_positive_of_response (r : Row) (lam Y rho u y theta P z L : ℝ)
    (hp : 0 < p lam Y) (hz : 0 < z) (hdelta : 0 ≤ delta r lam)
    (hadm : Admissible lam u y) (hJL : childJ lam u ≤ L)
    (hpos : 0 < responsePolynomial (p lam Y*tangentN r lam Y rho theta P/z)
      (p lam Y*beta r lam*rho) (p lam Y*(2*P-alpha r lam-beta r lam))
      (gamma r lam-delta r lam-p lam Y*z*P) (delta r lam) L (childH u) y) :
    0 < scaledPayment r lam Y rho u y theta P z := by
  have h := hpos.trans_le (scaledPayment_response_lower_bound r lam Y rho u y theta P z L
    hp hz hdelta hadm hJL)
  exact (mul_pos_iff_of_pos_left (div_pos hp hz)).mp h

end F4Heavy.Analysis
