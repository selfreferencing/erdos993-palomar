module

public import F4Heavy.Analysis.ChildActivity

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem childJ_log_chord (a b lam t u : ℝ) (ha : 0 < a) (hb : 0 < b) (hlam : 0 < lam)
    (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hlog : Real.log lam = (1-t)*Real.log a+t*Real.log b) :
    childJ lam u = (1-t)*childJ a u+t*childJ b u := by
  by_cases hu : u = 0
  · simp [hu, childJ]
  · have hup : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hu)
    rw [childJ_log_activity lam u hlam hup hu1, childJ_log_activity a u ha hup hu1,
      childJ_log_activity b u hb hup hu1, hlog]
    ring

theorem child_support_log_chord (a b lam t u s ca cb : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hlam : 0 < lam) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hlog : Real.log lam = (1-t)*Real.log a+t*Real.log b)
    (hla : childJ a u ≤ s*childH u+ca) (hlb : childJ b u ≤ s*childH u+cb) :
    childJ lam u ≤ s*childH u+ca+(cb-ca)*t := by
  rw [childJ_log_chord a b lam t u ha hb hlam hu0 hu1 hlog]
  have hl := mul_le_mul_of_nonneg_left hla (sub_nonneg.mpr ht1)
  have hr := mul_le_mul_of_nonneg_left hlb ht0
  nlinarith only [hl, hr]

theorem log_activity_weight (a b lam : ℝ) (ha : 0 < a) (hab : a < b)
    (hl : a ≤ lam) (hu : lam ≤ b) :
    let t := (Real.log lam-Real.log a)/(Real.log b-Real.log a)
    0 ≤ t ∧ t ≤ 1 ∧ Real.log lam = (1-t)*Real.log a+t*Real.log b := by
  have hden := sub_pos.mpr (Real.log_lt_log ha hab)
  have hll := Real.log_le_log ha hl
  have hlu := Real.log_le_log (ha.trans_le hl) hu
  dsimp only
  refine ⟨div_nonneg (sub_nonneg.mpr hll) hden.le, ?_, ?_⟩
  · exact (div_le_one hden).mpr (by linarith only [hlu])
  · field_simp [ne_of_gt hden]
    ring

theorem child_support_log_upper_weight (a b lam u s ca cb ell upper : ℝ)
    (ha : 0 < a) (hab : a < b) (hl : a ≤ lam) (hu : lam ≤ b)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hc : ca ≤ cb) (hell : 0 < ell)
    (helllog : ell ≤ Real.log (b/a)) (hupper : Real.log (lam/a) ≤ upper)
    (hla : childJ a u ≤ s*childH u+ca) (hlb : childJ b u ≤ s*childH u+cb) :
    childJ lam u ≤ s*childH u+ca+(cb-ca)*(upper/ell) := by
  have hb := ha.trans hab
  have hlam := ha.trans_le hl
  rw [Real.log_div (ne_of_gt hb) (ne_of_gt ha)] at helllog
  rw [Real.log_div (ne_of_gt hlam) (ne_of_gt ha)] at hupper
  have ht := log_activity_weight a b lam ha hab hl hu
  have hnum : 0 ≤ Real.log lam-Real.log a := sub_nonneg.mpr (Real.log_le_log ha hl)
  have hweight : (Real.log lam-Real.log a)/(Real.log b-Real.log a) ≤ upper/ell := by
    exact (div_le_div_of_nonneg_left hnum hell helllog).trans
      (div_le_div_of_nonneg_right hupper hell.le)
  have hline := child_support_log_chord a b lam _ u s ca cb ha hb hlam ht.1 ht.2.1
    hu0 hu1 ht.2.2 hla hlb
  have hmono := mul_le_mul_of_nonneg_left hweight (sub_nonneg.mpr hc)
  linarith only [hline, hmono]

theorem activity_log_ratio_upper (a lam : ℝ) (ha : 0 < a) (hl : a ≤ lam) :
    Real.log (lam/a) ≤ 2*((lam-a)/(lam+a))+
      2*((lam-a)/(lam+a))^3/(3*(1-((lam-a)/(lam+a))^2)) := by
  have hlam := ha.trans_le hl
  have hd : 0 < lam+a := add_pos hlam ha
  have hv0 : 0 ≤ (lam-a)/(lam+a) := div_nonneg (sub_nonneg.mpr hl) hd.le
  have hv1 : (lam-a)/(lam+a) < 1 := (div_lt_one hd).mpr (by linarith only [ha])
  have h := log_series_tight_upper 1 ((lam-a)/(lam+a)) hv0 hv1
  have heq : (1+(lam-a)/(lam+a))/(1-(lam-a)/(lam+a)) = lam/a := by
    field_simp [ne_of_gt ha, ne_of_gt hd] <;> ring
  rw [heq] at h
  norm_num [Finset.sum_range_succ] at h
  convert h using 1 <;> ring

end F4Heavy.Analysis
