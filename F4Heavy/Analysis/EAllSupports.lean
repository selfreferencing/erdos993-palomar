module

public import F4Heavy.Analysis.EFixedSupports

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem e1_child_support_lines (lam u : ℝ) (hr : InRow .E1 lam)
    (hu0 : 0 ≤ u) (huq : u ≤ q lam) :
    childJ lam u ≤ (7/3)*childH u+eSupportIntercept0 .E1 lam ∧
    childJ lam u ≤ (3/10)*childH u+eSupportIntercept1 .E1 lam ∧
    childJ lam u ≤ (-8/15)*childH u+eSupportIntercept2 .E1 lam := by
  have hr' : (13/10 : ℝ) ≤ lam ∧ lam ≤ (29/20 : ℝ) := hr
  have hq : u ≤ (29/49 : ℝ) := by
    apply huq.trans
    unfold q
    apply (div_le_iff₀ (by linarith [hr'.1] : 0 < 1+lam)).mpr
    linarith only [hr'.2]
  let t := (lam-(13/10 : ℝ))/((29/20 : ℝ)-(13/10 : ℝ))
  have ht := activity_weight_bounds (13/10 : ℝ) (29/20 : ℝ) lam (by norm_num) hr'.1 hr'.2
  have heq : (1-t)*(13/10 : ℝ)+t*(29/20 : ℝ) = lam := by dsimp [t]; ring

  have hs0 := child_support_activity_interpolation (13/10 : ℝ) (29/20 : ℝ) t u (29/49 : ℝ)
    (7/3 : ℝ) (-79166889/50000000 : ℝ) (-154103887/100000000 : ℝ)
    (by norm_num) (by norm_num) ht.1 ht.2 hu0 hq (by norm_num)
    (e_fixed_support_00 u hu0 (by linarith only [hq]))
    (e_fixed_support_03 u hu0 (by linarith only [hq]))
  rw [heq] at hs0
  have hs1 := child_support_activity_interpolation (13/10 : ℝ) (29/20 : ℝ) t u (29/49 : ℝ)
    (3/10 : ℝ) (3500567/100000000 : ℝ) (5922933/100000000 : ℝ)
    (by norm_num) (by norm_num) ht.1 ht.2 hu0 hq (by norm_num)
    (e_fixed_support_01 u hu0 (by linarith only [hq]))
    (e_fixed_support_04 u hu0 (by linarith only [hq]))
  rw [heq] at hs1
  have hs2 := child_support_activity_interpolation (13/10 : ℝ) (29/20 : ℝ) t u (29/49 : ℝ)
    (-8/15 : ℝ) (38732233/50000000 : ℝ) (19828959/25000000 : ℝ)
    (by norm_num) (by norm_num) ht.1 ht.2 hu0 hq (by norm_num)
    (e_fixed_support_02 u hu0 (by linarith only [hq]))
    (e_fixed_support_05 u hu0 (by linarith only [hq]))
  rw [heq] at hs2
  refine ⟨?_, ?_, ?_⟩
  · convert hs0 using 1 <;> norm_num [t, eSupportIntercept0] <;> ring
  · convert hs1 using 1 <;> norm_num [t, eSupportIntercept1] <;> ring
  · convert hs2 using 1 <;> norm_num [t, eSupportIntercept2] <;> ring

theorem e2_child_support_lines (lam u : ℝ) (hr : InRow .E2 lam)
    (hu0 : 0 ≤ u) (huq : u ≤ q lam) :
    childJ lam u ≤ (7/3)*childH u+eSupportIntercept0 .E2 lam ∧
    childJ lam u ≤ (3/10)*childH u+eSupportIntercept1 .E2 lam ∧
    childJ lam u ≤ (-8/15)*childH u+eSupportIntercept2 .E2 lam := by
  have hr' : (29/20 : ℝ) ≤ lam ∧ lam ≤ (8/5 : ℝ) := hr
  have hq : u ≤ (8/13 : ℝ) := by
    apply huq.trans
    unfold q
    apply (div_le_iff₀ (by linarith [hr'.1] : 0 < 1+lam)).mpr
    linarith only [hr'.2]
  let t := (lam-(29/20 : ℝ))/((8/5 : ℝ)-(29/20 : ℝ))
  have ht := activity_weight_bounds (29/20 : ℝ) (8/5 : ℝ) lam (by norm_num) hr'.1 hr'.2
  have heq : (1-t)*(29/20 : ℝ)+t*(8/5 : ℝ) = lam := by dsimp [t]; ring

  have hs0 := child_support_activity_interpolation (29/20 : ℝ) (8/5 : ℝ) t u (8/13 : ℝ)
    (7/3 : ℝ) (-154103887/100000000 : ℝ) (-150225069/100000000 : ℝ)
    (by norm_num) (by norm_num) ht.1 ht.2 hu0 hq (by norm_num)
    (e_fixed_support_03 u hu0 (by linarith only [hq]))
    (e_fixed_support_06 u hu0 (by linarith only [hq]))
  rw [heq] at hs0
  have hs1 := child_support_activity_interpolation (29/20 : ℝ) (8/5 : ℝ) t u (8/13 : ℝ)
    (3/10 : ℝ) (5922933/100000000 : ℝ) (1640021/20000000 : ℝ)
    (by norm_num) (by norm_num) ht.1 ht.2 hu0 hq (by norm_num)
    (e_fixed_support_04 u hu0 (by linarith only [hq]))
    (e_fixed_support_07 u hu0 (by linarith only [hq]))
  rw [heq] at hs1
  have hs2 := child_support_activity_interpolation (29/20 : ℝ) (8/5 : ℝ) t u (8/13 : ℝ)
    (-8/15 : ℝ) (19828959/25000000 : ℝ) (81122983/100000000 : ℝ)
    (by norm_num) (by norm_num) ht.1 ht.2 hu0 hq (by norm_num)
    (e_fixed_support_05 u hu0 (by linarith only [hq]))
    (e_fixed_support_08 u hu0 (by linarith only [hq]))
  rw [heq] at hs2
  refine ⟨?_, ?_, ?_⟩
  · convert hs0 using 1 <;> norm_num [t, eSupportIntercept0] <;> ring
  · convert hs1 using 1 <;> norm_num [t, eSupportIntercept1] <;> ring
  · convert hs2 using 1 <;> norm_num [t, eSupportIntercept2] <;> ring

end F4Heavy.Analysis
