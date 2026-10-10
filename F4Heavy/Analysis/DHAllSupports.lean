module

public import F4Heavy.Analysis.DHFixedSupports
public import F4Heavy.Analysis.ChildLogActivity

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

noncomputable def dSupportWeight (lam : ℝ) : ℝ :=
  let v := (lam-(4/5 : ℝ))/(lam+(4/5 : ℝ))
  (2*v+2*v^3/(3*(1-v^2)))/(485507815781/1000000000000 : ℝ)

noncomputable def dSupportIntercept0 (lam : ℝ) : ℝ :=
  (-3326942783/2000000000 : ℝ)+((-23862523/16000000 : ℝ)-(-3326942783/2000000000 : ℝ))*dSupportWeight lam

theorem d_child_support_line_0 (lam u : ℝ) (hr : InRow .D lam)
    (hu0 : 0 ≤ u) (huq : u ≤ q lam) :
    childJ lam u ≤ (11/5 : ℝ)*childH u+dSupportIntercept0 lam := by
  have hr' : (4/5 : ℝ) ≤ lam ∧ lam ≤ (13/10 : ℝ) := hr
  have hq : u ≤ (13/23 : ℝ) := by
    apply huq.trans
    unfold q
    apply (div_le_iff₀ (by linarith [hr'.1] : 0 < 1+lam)).mpr
    linarith only [hr'.2]
  have hell : (485507815781/1000000000000 : ℝ) ≤ Real.log ((13/10 : ℝ)/(4/5 : ℝ)) := by
    convert activity_log_D_ratio.2.le using 1 <;> norm_num
  have hs := child_support_log_upper_weight (4/5 : ℝ) (13/10 : ℝ) lam u (11/5 : ℝ) (-3326942783/2000000000 : ℝ) (-23862523/16000000 : ℝ)
    (485507815781/1000000000000 : ℝ) _ (by norm_num) (by norm_num) hr'.1 hr'.2 hu0
    (by linarith only [hq]) (by norm_num) (by norm_num) hell
    (activity_log_ratio_upper (4/5 : ℝ) lam (by norm_num) hr'.1)
    (dh_fixed_support_00 u hu0 hq)
    (dh_fixed_support_03 u hu0 hq)
  simpa only [dSupportIntercept0, dSupportWeight, add_assoc] using hs

noncomputable def dSupportIntercept1 (lam : ℝ) : ℝ :=
  (-60258643/1000000000 : ℝ)+((174865111/5000000000 : ℝ)-(-60258643/1000000000 : ℝ))*dSupportWeight lam

theorem d_child_support_line_1 (lam u : ℝ) (hr : InRow .D lam)
    (hu0 : 0 ≤ u) (huq : u ≤ q lam) :
    childJ lam u ≤ (3/10 : ℝ)*childH u+dSupportIntercept1 lam := by
  have hr' : (4/5 : ℝ) ≤ lam ∧ lam ≤ (13/10 : ℝ) := hr
  have hq : u ≤ (13/23 : ℝ) := by
    apply huq.trans
    unfold q
    apply (div_le_iff₀ (by linarith [hr'.1] : 0 < 1+lam)).mpr
    linarith only [hr'.2]
  have hell : (485507815781/1000000000000 : ℝ) ≤ Real.log ((13/10 : ℝ)/(4/5 : ℝ)) := by
    convert activity_log_D_ratio.2.le using 1 <;> norm_num
  have hs := child_support_log_upper_weight (4/5 : ℝ) (13/10 : ℝ) lam u (3/10 : ℝ) (-60258643/1000000000 : ℝ) (174865111/5000000000 : ℝ)
    (485507815781/1000000000000 : ℝ) _ (by norm_num) (by norm_num) hr'.1 hr'.2 hu0
    (by linarith only [hq]) (by norm_num) (by norm_num) hell
    (activity_log_ratio_upper (4/5 : ℝ) lam (by norm_num) hr'.1)
    (dh_fixed_support_01 u hu0 hq)
    (dh_fixed_support_04 u hu0 hq)
  simpa only [dSupportIntercept1, dSupportWeight, add_assoc] using hs

noncomputable def dSupportIntercept2 (lam : ℝ) : ℝ :=
  (3819556393/5000000000 : ℝ)+((8346294633/10000000000 : ℝ)-(3819556393/5000000000 : ℝ))*dSupportWeight lam

theorem d_child_support_line_2 (lam u : ℝ) (hr : InRow .D lam)
    (hu0 : 0 ≤ u) (huq : u ≤ q lam) :
    childJ lam u ≤ (-3/5 : ℝ)*childH u+dSupportIntercept2 lam := by
  have hr' : (4/5 : ℝ) ≤ lam ∧ lam ≤ (13/10 : ℝ) := hr
  have hq : u ≤ (13/23 : ℝ) := by
    apply huq.trans
    unfold q
    apply (div_le_iff₀ (by linarith [hr'.1] : 0 < 1+lam)).mpr
    linarith only [hr'.2]
  have hell : (485507815781/1000000000000 : ℝ) ≤ Real.log ((13/10 : ℝ)/(4/5 : ℝ)) := by
    convert activity_log_D_ratio.2.le using 1 <;> norm_num
  have hs := child_support_log_upper_weight (4/5 : ℝ) (13/10 : ℝ) lam u (-3/5 : ℝ) (3819556393/5000000000 : ℝ) (8346294633/10000000000 : ℝ)
    (485507815781/1000000000000 : ℝ) _ (by norm_num) (by norm_num) hr'.1 hr'.2 hu0
    (by linarith only [hq]) (by norm_num) (by norm_num) hell
    (activity_log_ratio_upper (4/5 : ℝ) lam (by norm_num) hr'.1)
    (dh_fixed_support_02 u hu0 hq)
    (dh_fixed_support_05 u hu0 hq)
  simpa only [dSupportIntercept2, dSupportWeight, add_assoc] using hs

noncomputable def hSupportWeight (lam : ℝ) : ℝ :=
  let v := (lam-(7/4 : ℝ))/(lam+(7/4 : ℝ))
  (2*v+2*v^3/(3*(1-v^2)))/(287682072451/1000000000000 : ℝ)

noncomputable def hSupportIntercept0 (lam : ℝ) : ℝ :=
  (-15097571481/10000000000 : ℝ)+((-3484969137/2500000000 : ℝ)-(-15097571481/10000000000 : ℝ))*hSupportWeight lam

theorem h_child_support_line_0 (lam u : ℝ) (hr : InRow .H lam)
    (hu0 : 0 ≤ u) (huq : u ≤ q lam) :
    childJ lam u ≤ (12/5 : ℝ)*childH u+hSupportIntercept0 lam := by
  have hr' : (7/4 : ℝ) ≤ lam ∧ lam ≤ (7/3 : ℝ) := hr
  have hq : u ≤ (7/10 : ℝ) := by
    apply huq.trans
    unfold q
    apply (div_le_iff₀ (by linarith [hr'.1] : 0 < 1+lam)).mpr
    linarith only [hr'.2]
  have hell : (287682072451/1000000000000 : ℝ) ≤ Real.log ((7/3 : ℝ)/(7/4 : ℝ)) := by
    convert activity_log_H_ratio.2.le using 1 <;> norm_num
  have hs := child_support_log_upper_weight (7/4 : ℝ) (7/3 : ℝ) lam u (12/5 : ℝ) (-15097571481/10000000000 : ℝ) (-3484969137/2500000000 : ℝ)
    (287682072451/1000000000000 : ℝ) _ (by norm_num) (by norm_num) hr'.1 hr'.2 hu0
    (by linarith only [hq]) (by norm_num) (by norm_num) hell
    (activity_log_ratio_upper (7/4 : ℝ) lam (by norm_num) hr'.1)
    (dh_fixed_support_06 u hu0 hq)
    (dh_fixed_support_11 u hu0 hq)
  simpa only [hSupportIntercept0, hSupportWeight, add_assoc] using hs

noncomputable def hSupportIntercept1 (lam : ℝ) : ℝ :=
  (516659173/5000000000 : ℝ)+((1762035691/10000000000 : ℝ)-(516659173/5000000000 : ℝ))*hSupportWeight lam

theorem h_child_support_line_1 (lam u : ℝ) (hr : InRow .H lam)
    (hu0 : 0 ≤ u) (huq : u ≤ q lam) :
    childJ lam u ≤ (3/10 : ℝ)*childH u+hSupportIntercept1 lam := by
  have hr' : (7/4 : ℝ) ≤ lam ∧ lam ≤ (7/3 : ℝ) := hr
  have hq : u ≤ (7/10 : ℝ) := by
    apply huq.trans
    unfold q
    apply (div_le_iff₀ (by linarith [hr'.1] : 0 < 1+lam)).mpr
    linarith only [hr'.2]
  have hell : (287682072451/1000000000000 : ℝ) ≤ Real.log ((7/3 : ℝ)/(7/4 : ℝ)) := by
    convert activity_log_H_ratio.2.le using 1 <;> norm_num
  have hs := child_support_log_upper_weight (7/4 : ℝ) (7/3 : ℝ) lam u (3/10 : ℝ) (516659173/5000000000 : ℝ) (1762035691/10000000000 : ℝ)
    (287682072451/1000000000000 : ℝ) _ (by norm_num) (by norm_num) hr'.1 hr'.2 hu0
    (by linarith only [hq]) (by norm_num) (by norm_num) hell
    (activity_log_ratio_upper (7/4 : ℝ) lam (by norm_num) hr'.1)
    (dh_fixed_support_07 u hu0 hq)
    (dh_fixed_support_12 u hu0 hq)
  simpa only [hSupportIntercept1, hSupportWeight, add_assoc] using hs

noncomputable def hSupportIntercept2 (lam : ℝ) : ℝ :=
  (8871047271/10000000000 : ℝ)+((9444767991/10000000000 : ℝ)-(8871047271/10000000000 : ℝ))*hSupportWeight lam

theorem h_child_support_line_2 (lam u : ℝ) (hr : InRow .H lam)
    (hu0 : 0 ≤ u) (huq : u ≤ q lam) :
    childJ lam u ≤ (-3/5 : ℝ)*childH u+hSupportIntercept2 lam := by
  have hr' : (7/4 : ℝ) ≤ lam ∧ lam ≤ (7/3 : ℝ) := hr
  have hq : u ≤ (7/10 : ℝ) := by
    apply huq.trans
    unfold q
    apply (div_le_iff₀ (by linarith [hr'.1] : 0 < 1+lam)).mpr
    linarith only [hr'.2]
  have hell : (287682072451/1000000000000 : ℝ) ≤ Real.log ((7/3 : ℝ)/(7/4 : ℝ)) := by
    convert activity_log_H_ratio.2.le using 1 <;> norm_num
  have hs := child_support_log_upper_weight (7/4 : ℝ) (7/3 : ℝ) lam u (-3/5 : ℝ) (8871047271/10000000000 : ℝ) (9444767991/10000000000 : ℝ)
    (287682072451/1000000000000 : ℝ) _ (by norm_num) (by norm_num) hr'.1 hr'.2 hu0
    (by linarith only [hq]) (by norm_num) (by norm_num) hell
    (activity_log_ratio_upper (7/4 : ℝ) lam (by norm_num) hr'.1)
    (dh_fixed_support_08 u hu0 hq)
    (dh_fixed_support_13 u hu0 hq)
  simpa only [hSupportIntercept2, hSupportWeight, add_assoc] using hs

noncomputable def hSupportIntercept3 (lam : ℝ) : ℝ :=
  (11763427811/5000000000 : ℝ)+((23882112697/10000000000 : ℝ)-(11763427811/5000000000 : ℝ))*hSupportWeight lam

theorem h_child_support_line_3 (lam u : ℝ) (hr : InRow .H lam)
    (hu0 : 0 ≤ u) (huq : u ≤ q lam) :
    childJ lam u ≤ (-11/5 : ℝ)*childH u+hSupportIntercept3 lam := by
  have hr' : (7/4 : ℝ) ≤ lam ∧ lam ≤ (7/3 : ℝ) := hr
  have hq : u ≤ (7/10 : ℝ) := by
    apply huq.trans
    unfold q
    apply (div_le_iff₀ (by linarith [hr'.1] : 0 < 1+lam)).mpr
    linarith only [hr'.2]
  have hell : (287682072451/1000000000000 : ℝ) ≤ Real.log ((7/3 : ℝ)/(7/4 : ℝ)) := by
    convert activity_log_H_ratio.2.le using 1 <;> norm_num
  have hs := child_support_log_upper_weight (7/4 : ℝ) (7/3 : ℝ) lam u (-11/5 : ℝ) (11763427811/5000000000 : ℝ) (23882112697/10000000000 : ℝ)
    (287682072451/1000000000000 : ℝ) _ (by norm_num) (by norm_num) hr'.1 hr'.2 hu0
    (by linarith only [hq]) (by norm_num) (by norm_num) hell
    (activity_log_ratio_upper (7/4 : ℝ) lam (by norm_num) hr'.1)
    (dh_fixed_support_09 u hu0 hq)
    (dh_fixed_support_14 u hu0 hq)
  simpa only [hSupportIntercept3, hSupportWeight, add_assoc] using hs

noncomputable def hSupportIntercept4 (lam : ℝ) : ℝ :=
  (10178601269/2500000000 : ℝ)+((10226130853/2500000000 : ℝ)-(10178601269/2500000000 : ℝ))*hSupportWeight lam

theorem h_child_support_line_4 (lam u : ℝ) (hr : InRow .H lam)
    (hu0 : 0 ≤ u) (huq : u ≤ q lam) :
    childJ lam u ≤ (-4/1 : ℝ)*childH u+hSupportIntercept4 lam := by
  have hr' : (7/4 : ℝ) ≤ lam ∧ lam ≤ (7/3 : ℝ) := hr
  have hq : u ≤ (7/10 : ℝ) := by
    apply huq.trans
    unfold q
    apply (div_le_iff₀ (by linarith [hr'.1] : 0 < 1+lam)).mpr
    linarith only [hr'.2]
  have hell : (287682072451/1000000000000 : ℝ) ≤ Real.log ((7/3 : ℝ)/(7/4 : ℝ)) := by
    convert activity_log_H_ratio.2.le using 1 <;> norm_num
  have hs := child_support_log_upper_weight (7/4 : ℝ) (7/3 : ℝ) lam u (-4/1 : ℝ) (10178601269/2500000000 : ℝ) (10226130853/2500000000 : ℝ)
    (287682072451/1000000000000 : ℝ) _ (by norm_num) (by norm_num) hr'.1 hr'.2 hu0
    (by linarith only [hq]) (by norm_num) (by norm_num) hell
    (activity_log_ratio_upper (7/4 : ℝ) lam (by norm_num) hr'.1)
    (dh_fixed_support_10 u hu0 hq)
    (dh_fixed_support_15 u hu0 hq)
  simpa only [hSupportIntercept4, hSupportWeight, add_assoc] using hs

end F4Heavy.Analysis
