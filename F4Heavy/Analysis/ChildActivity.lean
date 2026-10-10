module

public import F4Heavy.Analysis.LogInterpolation
public import F4Heavy.Analysis.ESupportCoverage

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem childH_nonnegative (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1) : 0 ≤ childH u := by
  by_cases hu : u = 0
  · simp [childH, hu]
  · have hup : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hu)
    have hlog := Real.log_le_sub_one_of_pos (sub_pos.mpr hu1)
    have hphi : 0 < -Real.log (1-u) := by linarith only [hlog, hup]
    simp only [childH, phi, if_neg hu]
    exact (div_pos hup hphi).le

theorem childH_linear_upper (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1) : childH u ≤ 1-u/2 := by
  by_cases hu : u = 0
  · simp [childH, hu]
  · have hup : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hu)
    simpa only [childH, phi, if_neg hu] using probability_log_ratio_linear_upper u hup hu1

theorem child_activity_weight_bounds (u qb : ℝ) (hu0 : 0 ≤ u) (huq : u ≤ qb) (hqb : qb < 1) :
    0 ≤ u*childH u ∧ u*childH u ≤ qb*(1-qb/2) := by
  have hu1 := huq.trans_lt hqb
  refine ⟨mul_nonneg hu0 (childH_nonnegative u hu0 hu1), ?_⟩
  have h := mul_le_mul_of_nonneg_left (childH_linear_upper u hu0 hu1) hu0
  have hgap := mul_nonneg (sub_nonneg.mpr huq) (show 0 ≤ 1-(qb+u)/2 by linarith)
  nlinarith only [h, hgap]

theorem childJ_log_activity (lam u : ℝ) (hlam : 0 < lam) (hu0 : 0 < u) (hu1 : u < 1) :
    childJ lam u = u*childH u*(Real.log lam+Real.log ((1-u)/u)) := by
  unfold childJ
  rw [if_neg (ne_of_gt hu0)]
  rw [show lam*(1-u)/u = lam*((1-u)/u) by ring,
    Real.log_mul (ne_of_gt hlam) (ne_of_gt (div_pos (sub_pos.mpr hu1) hu0))]

theorem childJ_activity_chord_difference (a b t u : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hlam : 0 < (1-t)*a+t*b) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    childJ ((1-t)*a+t*b) u-((1-t)*childJ a u+t*childJ b u) =
      u*childH u*(Real.log ((1-t)*a+t*b)-((1-t)*Real.log a+t*Real.log b)) := by
  by_cases hu : u = 0
  · simp [hu, childJ]
  · have hup : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hu)
    rw [childJ_log_activity _ u hlam hup hu1, childJ_log_activity a u ha hup hu1,
      childJ_log_activity b u hb hup hu1]
    ring

theorem childJ_activity_interpolation (a b t u qb : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hu0 : 0 ≤ u) (huq : u ≤ qb) (hqb : qb < 1) :
    childJ ((1-t)*a+t*b) u ≤ (1-t)*childJ a u+t*childJ b u+
      qb*(1-qb/2)*((b-a)^2/(8*a^2)) := by
  have hb := ha.trans_le hab
  have hlam := positive_chord a b t ha hb ht0 ht1
  have hdiff := childJ_activity_chord_difference a b t u ha hb hlam hu0 (huq.trans_lt hqb)
  have hlog := log_chord_uniform_upper a b t ha hab ht0 ht1
  have hw := child_activity_weight_bounds u qb hu0 huq hqb
  have hgap : Real.log ((1-t)*a+t*b)-((1-t)*Real.log a+t*Real.log b) ≤
      (b-a)^2/(8*a^2) := by linarith only [hlog]
  have hfirst := mul_le_mul_of_nonneg_left hgap hw.1
  have hsecond := mul_le_mul_of_nonneg_right hw.2 (show 0 ≤ (b-a)^2/(8*a^2) by positivity)
  linarith only [hdiff, hfirst, hsecond]

theorem child_support_activity_interpolation (a b t u qb s ca cb : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hu0 : 0 ≤ u) (huq : u ≤ qb) (hqb : qb < 1)
    (hla : childJ a u ≤ s*childH u+ca) (hlb : childJ b u ≤ s*childH u+cb) :
    childJ ((1-t)*a+t*b) u ≤ s*childH u+(1-t)*ca+t*cb+
      qb*(1-qb/2)*((b-a)^2/(8*a^2)) := by
  have h := childJ_activity_interpolation a b t u qb ha hab ht0 ht1 hu0 huq hqb
  have hleft := mul_le_mul_of_nonneg_left hla (sub_nonneg.mpr ht1)
  have hright := mul_le_mul_of_nonneg_left hlb ht0
  nlinarith only [h, hleft, hright]

end F4Heavy.Analysis
