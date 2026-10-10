module

public import F4Heavy.Analysis.ActivityLogConstants
public import F4Heavy.Analysis.RationalLogBound
public import F4Heavy.Analysis.SupportSegment
public import F4Heavy.Analysis.HeavyDomain

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem real_log_tangent_upper (x m : ℝ) (hx : 0 < x) (hm : 0 < m) :
    Real.log x ≤ Real.log m + (x - m) / m := by
  have h := Real.log_le_sub_one_of_pos (div_pos hx hm)
  rw [Real.log_div (ne_of_gt hx) (ne_of_gt hm)] at h
  have he : x / m - 1 = (x - m) / m := by field_simp
  rw [he] at h
  linarith

theorem real_log_chord_lower (a b t : ℝ) (ha : 0 < a) (hb : 0 < b)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * Real.log a + t * Real.log b ≤ Real.log ((1 - t) * a + t * b) := by
  let x := (1 - t) * a + t * b
  have hx : 0 < x := positive_chord a b t ha hb ht0 ht1
  have hl := mul_le_mul_of_nonneg_left (real_log_tangent_upper a x ha hx) (sub_nonneg.mpr ht1)
  have hr := mul_le_mul_of_nonneg_left (real_log_tangent_upper b x hb hx) ht0
  have he : (1 - t) * ((a - x) / x) + t * ((b - x) / x) = 0 := by
    field_simp
    dsimp [x]
    ring
  change _ ≤ Real.log x
  nlinarith only [hl, hr, he]

theorem activity_weight_bounds (a b lam : ℝ) (hab : a < b) (hl : a ≤ lam) (hu : lam ≤ b) :
    0 ≤ (lam - a) / (b - a) ∧ (lam - a) / (b - a) ≤ 1 := by
  exact ⟨div_nonneg (sub_nonneg.mpr hl) (sub_pos.mpr hab).le,
    (div_le_one (sub_pos.mpr hab)).2 (by linarith)⟩

theorem activity_log_chord_lower (a b ca cb lam : ℝ) (ha : 0 < 1 + a) (hb : 0 < 1 + b)
    (hab : a < b) (hl : a ≤ lam) (hu : lam ≤ b)
    (hca : ca ≤ Real.log (1 + a)) (hcb : cb ≤ Real.log (1 + b)) :
    ca + (cb - ca) * (lam - a) / (b - a) ≤ Real.log (1 + lam) := by
  have ht := activity_weight_bounds a b lam hab hl hu
  have h := real_log_chord_lower (1 + a) (1 + b) ((lam - a) / (b - a)) ha hb ht.1 ht.2
  have he : (1 - (lam - a) / (b - a)) * (1 + a) + (lam - a) / (b - a) * (1 + b) = 1 + lam := by
    field_simp [ne_of_gt (sub_pos.mpr hab)]
    ring
  rw [he] at h
  have hleft := mul_le_mul_of_nonneg_left hca (sub_nonneg.mpr ht.2)
  have hright := mul_le_mul_of_nonneg_left hcb ht.1
  rw [mul_div_assoc]
  nlinarith only [h, hleft, hright]

theorem activity_log_chord_positive (a b ca cb lam : ℝ) (hab : a < b)
    (hl : a ≤ lam) (hu : lam ≤ b) (hca : 0 < ca) (hcb : 0 < cb) :
    0 < ca + (cb - ca) * (lam - a) / (b - a) := by
  have ht := activity_weight_bounds a b lam hab hl hu
  have h := positive_chord ca cb ((lam - a) / (b - a)) hca hcb ht.1 ht.2
  rw [mul_div_assoc]
  nlinarith only [h]

noncomputable def activityLogLeft : Row → ℝ
  | .D => 293893332451 / 500000000000
  | .E1 => 8329091229 / 10000000000
  | .E2 => 1792176049 / 2000000000
  | .H => 505800455839 / 500000000000

noncomputable def activityLogRight : Row → ℝ
  | .D => 166581824587 / 200000000000
  | .E1 => 1792176049 / 2000000000
  | .E2 => 191102289 / 200000000
  | .H => 48158912173 / 40000000000

noncomputable def activityLogMidpointUpper : Row → ℝ
  | .D => 717839793151 / 1000000000000
  | .E1 => 13839959 / 16000000
  | .E2 => 2315602657 / 2500000000
  | .H => 1112405610801 / 1000000000000

theorem activityLogLeft_correct (r : Row) :
    0 < activityLogLeft r ∧ activityLogLeft r < Real.log (1 + (rowData r).lo) := by
  cases r with
  | D => convert activity_log_D_left using 1 <;> norm_num [activityLogLeft, rowData]
  | E1 => convert activity_log_E1_left using 1 <;> norm_num [activityLogLeft, rowData]
  | E2 => convert activity_log_E2_left using 1 <;> norm_num [activityLogLeft, rowData]
  | H => convert activity_log_H_left using 1 <;> norm_num [activityLogLeft, rowData]

theorem activityLogRight_correct (r : Row) :
    0 < activityLogRight r ∧ activityLogRight r < Real.log (1 + (rowData r).hi) := by
  cases r with
  | D => convert activity_log_D_right using 1 <;> norm_num [activityLogRight, rowData]
  | E1 => convert activity_log_E1_right using 1 <;> norm_num [activityLogRight, rowData]
  | E2 => convert activity_log_E2_right using 1 <;> norm_num [activityLogRight, rowData]
  | H => convert activity_log_H_right using 1 <;> norm_num [activityLogRight, rowData]

theorem activityLogMidpointUpper_correct (r : Row) :
    Real.log (1 + ((rowData r).lo + (rowData r).hi) / 2) < activityLogMidpointUpper r := by
  cases r with
  | D => convert activity_log_D_midpoint using 1 <;> norm_num [activityLogMidpointUpper, rowData]
  | E1 => convert activity_log_E1_midpoint using 1 <;> norm_num [activityLogMidpointUpper, rowData]
  | E2 => convert activity_log_E2_midpoint using 1 <;> norm_num [activityLogMidpointUpper, rowData]
  | H => convert activity_log_H_midpoint using 1 <;> norm_num [activityLogMidpointUpper, rowData]

theorem row_activity_log_domain (r : Row) :
    0 < (rowData r).lo ∧ (rowData r).lo < (rowData r).hi ∧ (1 / 4 : ℝ) ≤ (rowData r).xMin := by
  cases r <;> norm_num [rowData]

noncomputable def activityLogLower (r : Row) (lam : ℝ) : ℝ :=
  activityLogLeft r + (activityLogRight r - activityLogLeft r) *
    (lam - (rowData r).lo) / ((rowData r).hi - (rowData r).lo)

noncomputable def activityLogUpper (r : Row) (lam : ℝ) : ℝ :=
  let m := ((rowData r).lo + (rowData r).hi) / 2
  activityLogMidpointUpper r + (lam - m) / (1 + m)

theorem activityLogLower_correct (r : Row) (lam : ℝ) (hr : InRow r lam) :
    0 < activityLogLower r lam ∧ activityLogLower r lam ≤ Real.log (1 + lam) := by
  have hd := row_activity_log_domain r
  have ha := activityLogLeft_correct r
  have hb := activityLogRight_correct r
  constructor
  · exact activity_log_chord_positive _ _ _ _ lam hd.2.1 hr.1 hr.2 ha.1 hb.1
  · exact activity_log_chord_lower _ _ _ _ lam (by linarith only [hd.1])
      (by linarith only [hd.1, hd.2.1]) hd.2.1 hr.1 hr.2 ha.2.le hb.2.le

theorem activityLogUpper_correct (r : Row) (lam : ℝ) (hr : InRow r lam) :
    Real.log (1 + lam) < activityLogUpper r lam := by
  have hd := row_activity_log_domain r
  have hm : 0 < 1 + ((rowData r).lo + (rowData r).hi) / 2 := by
    linarith only [hd.1, hd.2.1]
  have h := real_log_tangent_upper (1 + lam) (1 + ((rowData r).lo + (rowData r).hi) / 2)
    (by linarith only [inRow_activity_pos r lam hr]) hm
  have hB := activityLogMidpointUpper_correct r
  unfold activityLogUpper
  have he : 1 + lam - (1 + ((rowData r).lo + (rowData r).hi) / 2) =
      lam - ((rowData r).lo + (rowData r).hi) / 2 := by ring
  rw [he] at h
  linarith only [h, hB]

theorem original_parent_log_identity (lam Y : ℝ) (hlam : 0 < lam) :
    Real.log (1 + lam) - Real.log (parentX lam Y) = Y := by
  rw [parentX, Real.log_mul (ne_of_gt (show 0 < 1 + lam by linarith))
    (ne_of_gt (Real.exp_pos (-Y))), Real.log_exp]
  ring

noncomputable def parentLogLower (r : Row) (lam x : ℝ) : ℝ :=
  activityLogLower r lam + 2 * (1 - x) / (1 + x)

noncomputable def parentLogUpper (r : Row) (lam x : ℝ) : ℝ :=
  activityLogUpper r lam + negativeLogUpper x

theorem original_parent_log_enclosure (r : Row) (lam Y : ℝ) (hr : InRow r lam)
    (hx0 : (rowData r).xMin ≤ parentX lam Y) (hx1 : parentX lam Y ≤ 1) :
    0 < parentLogLower r lam (parentX lam Y) ∧
      parentLogLower r lam (parentX lam Y) ≤ Y ∧ Y ≤ parentLogUpper r lam (parentX lam Y) := by
  have hx : (1 / 4 : ℝ) ≤ parentX lam Y := (row_activity_log_domain r).2.2.trans hx0
  have hxpos : 0 < parentX lam Y := by linarith only [hx]
  have hl := activityLogLower_correct r lam hr
  have hu := activityLogUpper_correct r lam hr
  have hn := negative_log_enclosure (parentX lam Y) hx hx1
  have hid := original_parent_log_identity lam Y (inRow_activity_pos r lam hr)
  have hfrac : 0 ≤ 2 * (1 - parentX lam Y) / (1 + parentX lam Y) :=
    div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hx1)) (by linarith)
  refine ⟨add_pos_of_pos_of_nonneg hl.1 hfrac, ?_, ?_⟩
  · unfold parentLogLower
    linarith only [hl.2, hn.1, hid]
  · unfold parentLogUpper
    linarith only [hu, hn.2, hid]

end F4Heavy.Analysis
