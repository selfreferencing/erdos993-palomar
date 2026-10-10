module

public import F4Heavy.Analysis.CapReduction
public import F4Heavy.Analysis.CapChildSlope
public import F4Heavy.Analysis.HeavyDomain

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem cap_child_pos (lam Y : ℝ) (hlam : 0 < lam) (hY : 0 < Y) :
    0 < capChild lam Y := by
  apply lt_min
  · exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hY))
  · exact div_pos (q_pos lam hlam) (by norm_num)

theorem cap_child_lt_q (lam Y : ℝ) (hlam : 0 < lam) :
    capChild lam Y < q lam := by
  have hq := q_pos lam hlam
  exact (min_le_right _ _).trans_lt (by linarith)

theorem cap_child_lt_one (lam Y : ℝ) (hlam : 0 < lam) :
    capChild lam Y < 1 := (cap_child_lt_q lam Y hlam).trans (q_lt_one lam hlam)

theorem cap_child_height_bounds (lam Y u : ℝ) (hlam : 0 < lam)
    (hu : 0 < u) (huc : u ≤ capChild lam Y) : 0 < childH u ∧ childH u ≤ 1 := by
  have hu1 := huc.trans_lt (cap_child_lt_one lam Y hlam)
  constructor
  · simpa only [childH, if_neg (ne_of_gt hu)] using div_pos hu (phi_positive u hu hu1)
  · exact childH_upper_one u hu.le hu1

theorem cap_child_reserve_pos (lam Y u : ℝ) (hlam : 0 < lam)
    (hu : 0 < u) (huc : u ≤ capChild lam Y) : 0 < childJ lam u := by
  have huq := huc.trans_lt (cap_child_lt_q lam Y hlam)
  have ht : 1 < lam * (1 - u) / u := by
    apply (lt_div_iff₀ hu).mpr
    have hc := (lt_div_iff₀ (show 0 < 1 + lam by linarith)).mp huq
    nlinarith only [hc]
  simp only [childJ, if_neg (ne_of_gt hu)]
  exact mul_pos (mul_pos hu (cap_child_height_bounds lam Y u hlam hu huc).1) (Real.log_pos ht)

theorem cap_height_increment_on_domain (lam Y u : ℝ) (hlam : 0 < lam)
    (hu : 0 ≤ u) (huc : u ≤ capChild lam Y) :
    (capChild lam Y - u) / 2 ≤ childH u - childH (capChild lam Y) :=
  cap_childH_height_increment u (capChild lam Y) hu huc (cap_child_lt_one lam Y hlam)

theorem cap_parent_probability_lower (lam Y : ℝ) (hlam : 0 < lam)
    (hH : parentH Y ≤ q lam) : lam / (1 + 2 * lam) ≤ p lam Y := by
  have hl1 : 0 < 1 + lam := by linarith
  have hl2 : 0 < 1 + 2 * lam := by linarith
  have he := Real.exp_pos (-Y)
  have hH' : (1 - Real.exp (-Y)) * (1 + lam) ≤ lam :=
    (le_div_iff₀ hl1).mp hH
  have hm : 0 ≤ lam * ((1 + lam) * Real.exp (-Y) - 1) :=
    mul_nonneg hlam.le (by linarith only [hH'])
  unfold p
  apply (div_le_div_iff₀ hl2 (by positivity : 0 < 1 + lam * Real.exp (-Y))).mpr
  nlinarith only [hm]

theorem cap_probability_vacancy_lower (lam Y rho : ℝ) (hlam : 0 < lam)
    (hH : parentH Y ≤ q lam) (hrho : FeasibleVacancy lam Y rho) :
    lam / (lam ^ 2 + 3 * lam + 1) ≤ p lam Y * rho := by
  have hp := p_pos lam Y hlam
  have hp1 := p_lt_one lam Y hlam
  have hd : 0 < 1 + lam * (1 - p lam Y) := by positivity
  have hden : 0 < lam ^ 2 + 3 * lam + 1 := by positivity
  have hl2 : 0 < 1 + 2 * lam := by linarith
  have hc : lam ≤ p lam Y * (1 + 2 * lam) :=
    (div_le_iff₀ hl2).mp (cap_parent_probability_lower lam Y hlam hH)
  have hm := mul_nonneg (show 0 ≤ 1 + lam by linarith)
    (sub_nonneg.mpr hc)
  have hfirst : lam / (lam ^ 2 + 3 * lam + 1) ≤
      p lam Y / (1 + lam * (1 - p lam Y)) := by
    apply (div_le_div_iff₀ hden hd).mpr
    nlinarith only [hm]
  have hsecond := mul_le_mul_of_nonneg_left hrho.1 hp.le
  change p lam Y * (1 / (1 + lam * (1 - p lam Y))) ≤ p lam Y * rho at hsecond
  simp only [mul_one_div] at hsecond
  exact hfirst.trans hsecond

theorem cap_parent_b_lower (r : Row) (lam Y rho : ℝ) (hlam : 0 < lam)
    (hH : parentH Y ≤ q lam) (hrho : FeasibleVacancy lam Y rho)
    (hbeta : 0 ≤ beta r lam) :
    beta r lam * lam / (lam ^ 2 + 3 * lam + 1) ≤ capB r lam Y rho := by
  have h := mul_le_mul_of_nonneg_left (cap_probability_vacancy_lower lam Y rho hlam hH hrho) hbeta
  unfold capB
  convert h using 1 <;> ring

end F4Heavy.Analysis
