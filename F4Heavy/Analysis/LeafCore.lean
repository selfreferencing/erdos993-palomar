module

public import F4Heavy.Analysis.LeafLogBounds
public import F4Heavy.Analysis.ParentBounds

@[expose] public section
set_option autoImplicit false
namespace F4Heavy.Analysis
open F4Unified

theorem activity_q_bounds (lam a b : ℝ) (ha : 0 < a)
    (hal : a ≤ lam) (hlb : lam ≤ b) : q a ≤ q lam ∧ q lam ≤ q b := by
  have hl : 0 < lam := lt_of_lt_of_le ha hal
  have hb : 0 < b := lt_of_lt_of_le hl hlb
  constructor
  · unfold q
    apply (div_le_div_iff₀ (by linarith : 0 < 1+a) (by linarith : 0 < 1+lam)).2
    nlinarith only [hal]
  · unfold q
    apply (div_le_div_iff₀ (by linarith : 0 < 1+lam) (by linarith : 0 < 1+b)).2
    nlinarith only [hlb]

theorem activity_field_q_coordinate (m n ctr lam : ℝ) (hl : 0 < lam) :
    field m n ctr lam = ((m-n*ctr)*(1-q lam)+n*q lam)/(65536*(1-q lam)) := by
  unfold field q
  field_simp
  <;> ring

theorem leaf_probability (lam : ℝ) : p lam 0 = q lam := by
  simp [p, q]

theorem leaf_cap (lam : ℝ) (hl : 0 < lam) : childCap lam 0 = 0 := by
  simp [childCap, parentH, min_eq_right (q_pos lam hl).le]

theorem leaf_vacancy (lam : ℝ) (hl : 0 < lam) : lowerVacancy lam 0 = 1/(1+q lam) := by
  have hid : lam*(1-q lam) = q lam := by
    unfold q
    field_simp
    <;> ring
  unfold lowerVacancy
  rw [leaf_probability, hid]

theorem leaf_source_identity (lam rho : ℝ) (hl : 0 < lam)
    (hrho : FeasibleVacancy lam 0 rho) :
    source lam 0 rho = (1+q lam)/(2*q lam)*rho+(q lam-1)/(2*q lam) := by
  have hq := q_pos lam hl
  have hq1 := q_lt_one lam hl
  have hr := hrho.1
  rw [leaf_vacancy lam hl] at hr
  have hb : 1 ≤ (1+q lam)*rho := by
    have h := (div_le_iff₀ (by linarith : 0 < 1+q lam)).mp hr
    nlinarith only [h]
  have hb1 : (1+q lam)*(1-rho) ≤ q lam := by nlinarith only [hb]
  have hb2 : q lam ≤ (1+q lam)*(q lam*rho) := by
    nlinarith only [mul_nonneg hq.le (sub_nonneg.mpr hb)]
  unfold source
  rw [leaf_probability, leaf_cap lam hl]
  simp only [mul_zero, max_eq_left (show 0 ≤ 1-rho by linarith [hrho.2])]
  rw [f_second_branch lam (q lam*rho) hl hb2, f_first_branch lam (1-rho) hl hb1]
  field_simp
  <;> ring

theorem inverse_activity_identity (lam : ℝ) (hl : 0 < lam) :
    1/(1+lam) = 1-q lam := by
  unfold q
  field_simp
  <;> ring

noncomputable def leafA (r : Row) (lam : ℝ) : ℝ :=
  (rowData r).price*(1-(q lam)^2)/(2*q lam)
noncomputable def leafB (r : Row) (lam : ℝ) : ℝ :=
  -(rowData r).price*(1-q lam)^2/(2*q lam)-alpha r lam-(1-q lam)
noncomputable def leafC (r : Row) (lam : ℝ) : ℝ :=
  alpha r lam-gamma r lam*(1-q lam/2-(q lam)^2/12-(q lam)^3/24-19*(q lam)^4/720)

theorem leaf_A_positive (r : Row) (lam : ℝ) (hr : InRow r lam) : 0 < leafA r lam := by
  have hl := inRow_activity_pos r lam hr
  have hq := q_pos lam hl
  have hq1 := q_lt_one lam hl
  have hp := row_price_pos r
  have hs : 0 < 1-(q lam)^2 := by nlinarith
  unfold leafA
  positivity

theorem leaf_quadratic_algebra (k t a g V rho : ℝ) (ht : t ≠ 0) :
    k*(1-t^2)/(2*t)*rho^2+(-k*(1-t)^2/(2*t)-a-(1-t))*rho+(a-g*V) =
      k*(1-t)*rho*((1+t)/(2*t)*rho+(t-1)/(2*t))+a*(1-rho)-rho*(1-t)-g*V := by
  field_simp
  <;> ring

theorem leaf_parent_lower (r : Row) (lam rho : ℝ) (hr : InRow r lam)
    (hrho : FeasibleVacancy lam 0 rho) :
    leafA r lam*rho^2+leafB r lam*rho+leafC r lam ≤ parentN r lam 0 rho := by
  have hl := inRow_activity_pos r lam hr
  have hq := q_pos lam hl
  have hq1 := q_lt_one lam hl
  have hparent := mul_le_mul_of_nonneg_left (probability_log_ratio_quartic_upper (q lam) hq hq1)
    (row_gamma_pos r lam hr).le
  have hid : (rowData r).price/(1+lam) = (rowData r).price*(1-q lam) := by
    rw [div_eq_mul_inv, ← one_div, inverse_activity_identity lam hl]
  unfold parentN parentP
  rw [leaf_source_identity lam rho hl hrho, leaf_probability, hid, mul_div_assoc]
  unfold leafA leafB leafC
  rw [leaf_quadratic_algebra _ _ _ _ _ _ (ne_of_gt hq)]
  linarith only [hparent]

theorem leaf_positive_of_discriminant (r : Row)
    (hd : ∀ lam, InRow r lam → 0 < 4*leafA r lam*leafC r lam-(leafB r lam)^2) :
    LeafPositive r := by
  intro lam rho hr hrho
  have hA := leaf_A_positive r lam hr
  have hdisc := hd lam hr
  have hlow := leaf_parent_lower r lam rho hr hrho
  have hN : 0 < parentN r lam 0 rho :=
    lt_of_lt_of_le (quadratic_positive _ _ _ rho hA hdisc) hlow
  exact mul_pos (q_pos lam (inRow_activity_pos r lam hr)) hN

end F4Heavy.Analysis
