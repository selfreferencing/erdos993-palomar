module

public import F4Heavy.Analysis.DHContact00
public import F4Heavy.Analysis.DHContact01
public import F4Heavy.Analysis.DHContact02
public import F4Heavy.Analysis.DHContact03
public import F4Heavy.Analysis.DHContact04
public import F4Heavy.Analysis.DHContact05
public import F4Heavy.Analysis.DHContact06
public import F4Heavy.Analysis.DHContact07
public import F4Heavy.Analysis.DHContact08
public import F4Heavy.Analysis.DHContact09
public import F4Heavy.Analysis.DHContact10
public import F4Heavy.Analysis.DHContact11
public import F4Heavy.Analysis.DHContact12
public import F4Heavy.Analysis.DHContact13
public import F4Heavy.Analysis.DHContact14
public import F4Heavy.Analysis.DHContact15

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem dh_fixed_support_00 (u : ℝ) (hu0 : 0 ≤ u) (huq : u ≤ (13/23 : ℝ)) :
    childJ (4/5 : ℝ) u ≤ (11/5 : ℝ)*childH u+(-3326942783/2000000000 : ℝ) := by
  apply d_child_line_of_contact (4/5 : ℝ) u (4404409/10000000 : ℝ) (11/5 : ℝ) (-3326942783/2000000000 : ℝ) (by norm_num)
    hu0 huq (by norm_num) (by norm_num) (by norm_num)
  convert dh_contact_00_bound using 1 <;> ring

theorem dh_fixed_support_01 (u : ℝ) (hu0 : 0 ≤ u) (huq : u ≤ (13/23 : ℝ)) :
    childJ (4/5 : ℝ) u ≤ (3/10 : ℝ)*childH u+(-60258643/1000000000 : ℝ) := by
  apply d_child_line_of_contact (4/5 : ℝ) u (19405741/100000000 : ℝ) (3/10 : ℝ) (-60258643/1000000000 : ℝ) (by norm_num)
    hu0 huq (by norm_num) (by norm_num) (by norm_num)
  convert dh_contact_01_bound using 1 <;> ring

theorem dh_fixed_support_02 (u : ℝ) (hu0 : 0 ≤ u) (huq : u ≤ (13/23 : ℝ)) :
    childJ (4/5 : ℝ) u ≤ (-3/5 : ℝ)*childH u+(3819556393/5000000000 : ℝ) := by
  apply d_child_line_of_contact (4/5 : ℝ) u (341129/2500000 : ℝ) (-3/5 : ℝ) (3819556393/5000000000 : ℝ) (by norm_num)
    hu0 huq (by norm_num) (by norm_num) (by norm_num)
  convert dh_contact_02_bound using 1 <;> ring

theorem dh_fixed_support_03 (u : ℝ) (hu0 : 0 ≤ u) (huq : u ≤ (13/23 : ℝ)) :
    childJ (13/10 : ℝ) u ≤ (11/5 : ℝ)*childH u+(-23862523/16000000 : ℝ) := by
  apply d_child_line_of_contact (13/10 : ℝ) u (52787217/100000000 : ℝ) (11/5 : ℝ) (-23862523/16000000 : ℝ) (by norm_num)
    hu0 huq (by norm_num) (by norm_num) (by norm_num)
  convert dh_contact_03_bound using 1 <;> ring

theorem dh_fixed_support_04 (u : ℝ) (hu0 : 0 ≤ u) (huq : u ≤ (13/23 : ℝ)) :
    childJ (13/10 : ℝ) u ≤ (3/10 : ℝ)*childH u+(174865111/5000000000 : ℝ) := by
  apply d_child_line_of_contact (13/10 : ℝ) u (25029329/100000000 : ℝ) (3/10 : ℝ) (174865111/5000000000 : ℝ) (by norm_num)
    hu0 huq (by norm_num) (by norm_num) (by norm_num)
  convert dh_contact_04_bound using 1 <;> ring

theorem dh_fixed_support_05 (u : ℝ) (hu0 : 0 ≤ u) (huq : u ≤ (13/23 : ℝ)) :
    childJ (13/10 : ℝ) u ≤ (-3/5 : ℝ)*childH u+(8346294633/10000000000 : ℝ) := by
  apply d_child_line_of_contact (13/10 : ℝ) u (18182879/100000000 : ℝ) (-3/5 : ℝ) (8346294633/10000000000 : ℝ) (by norm_num)
    hu0 huq (by norm_num) (by norm_num) (by norm_num)
  convert dh_contact_05_bound using 1 <;> ring

theorem dh_fixed_support_06 (u : ℝ) (hu0 : 0 ≤ u) (huq : u ≤ (7/10 : ℝ)) :
    childJ (7/4 : ℝ) u ≤ (12/5 : ℝ)*childH u+(-15097571481/10000000000 : ℝ) := by
  apply h_child_line_of_contact (7/4 : ℝ) u (996057/1562500 : ℝ) (12/5 : ℝ) (-15097571481/10000000000 : ℝ) (by norm_num)
    hu0 huq (by norm_num) (by norm_num) (by norm_num)
  convert dh_contact_06_bound using 1 <;> ring

theorem dh_fixed_support_07 (u : ℝ) (hu0 : 0 ≤ u) (huq : u ≤ (7/10 : ℝ)) :
    childJ (7/4 : ℝ) u ≤ (3/10 : ℝ)*childH u+(516659173/5000000000 : ℝ) := by
  apply h_child_line_of_contact (7/4 : ℝ) u (14253549/50000000 : ℝ) (3/10 : ℝ) (516659173/5000000000 : ℝ) (by norm_num)
    hu0 huq (by norm_num) (by norm_num) (by norm_num)
  convert dh_contact_07_bound using 1 <;> ring

theorem dh_fixed_support_08 (u : ℝ) (hu0 : 0 ≤ u) (huq : u ≤ (7/10 : ℝ)) :
    childJ (7/4 : ℝ) u ≤ (-3/5 : ℝ)*childH u+(8871047271/10000000000 : ℝ) := by
  apply h_child_line_of_contact (7/4 : ℝ) u (21153401/100000000 : ℝ) (-3/5 : ℝ) (8871047271/10000000000 : ℝ) (by norm_num)
    hu0 huq (by norm_num) (by norm_num) (by norm_num)
  convert dh_contact_08_bound using 1 <;> ring

theorem dh_fixed_support_09 (u : ℝ) (hu0 : 0 ≤ u) (huq : u ≤ (7/10 : ℝ)) :
    childJ (7/4 : ℝ) u ≤ (-11/5 : ℝ)*childH u+(11763427811/5000000000 : ℝ) := by
  apply h_child_line_of_contact (7/4 : ℝ) u (12171881/100000000 : ℝ) (-11/5 : ℝ) (11763427811/5000000000 : ℝ) (by norm_num)
    hu0 huq (by norm_num) (by norm_num) (by norm_num)
  convert dh_contact_09_bound using 1 <;> ring

theorem dh_fixed_support_10 (u : ℝ) (hu0 : 0 ≤ u) (huq : u ≤ (7/10 : ℝ)) :
    childJ (7/4 : ℝ) u ≤ (-4/1 : ℝ)*childH u+(10178601269/2500000000 : ℝ) := by
  apply h_child_line_of_contact (7/4 : ℝ) u (3085023/50000000 : ℝ) (-4/1 : ℝ) (10178601269/2500000000 : ℝ) (by norm_num)
    hu0 huq (by norm_num) (by norm_num) (by norm_num)
  convert dh_contact_10_bound using 1 <;> ring

theorem dh_fixed_support_11 (u : ℝ) (hu0 : 0 ≤ u) (huq : u ≤ (7/10 : ℝ)) :
    childJ (7/3 : ℝ) u ≤ (12/5 : ℝ)*childH u+(-3484969137/2500000000 : ℝ) := by
  apply h_child_line_of_contact (7/3 : ℝ) u (1032489/1562500 : ℝ) (12/5 : ℝ) (-3484969137/2500000000 : ℝ) (by norm_num)
    hu0 huq (by norm_num) (by norm_num) (by norm_num)
  convert dh_contact_11_bound using 1 <;> ring

theorem dh_fixed_support_12 (u : ℝ) (hu0 : 0 ≤ u) (huq : u ≤ (7/10 : ℝ)) :
    childJ (7/3 : ℝ) u ≤ (3/10 : ℝ)*childH u+(1762035691/10000000000 : ℝ) := by
  apply h_child_line_of_contact (7/3 : ℝ) u (31777527/100000000 : ℝ) (3/10 : ℝ) (1762035691/10000000000 : ℝ) (by norm_num)
    hu0 huq (by norm_num) (by norm_num) (by norm_num)
  convert dh_contact_12_bound using 1 <;> ring

theorem dh_fixed_support_13 (u : ℝ) (hu0 : 0 ≤ u) (huq : u ≤ (7/10 : ℝ)) :
    childJ (7/3 : ℝ) u ≤ (-3/5 : ℝ)*childH u+(9444767991/10000000000 : ℝ) := by
  apply h_child_line_of_contact (7/3 : ℝ) u (2407311/10000000 : ℝ) (-3/5 : ℝ) (9444767991/10000000000 : ℝ) (by norm_num)
    hu0 huq (by norm_num) (by norm_num) (by norm_num)
  convert dh_contact_13_bound using 1 <;> ring

theorem dh_fixed_support_14 (u : ℝ) (hu0 : 0 ≤ u) (huq : u ≤ (7/10 : ℝ)) :
    childJ (7/3 : ℝ) u ≤ (-11/5 : ℝ)*childH u+(23882112697/10000000000 : ℝ) := by
  apply h_child_line_of_contact (7/3 : ℝ) u (1435151/10000000 : ℝ) (-11/5 : ℝ) (23882112697/10000000000 : ℝ) (by norm_num)
    hu0 huq (by norm_num) (by norm_num) (by norm_num)
  convert dh_contact_14_bound using 1 <;> ring

theorem dh_fixed_support_15 (u : ℝ) (hu0 : 0 ≤ u) (huq : u ≤ (7/10 : ℝ)) :
    childJ (7/3 : ℝ) u ≤ (-4/1 : ℝ)*childH u+(10226130853/2500000000 : ℝ) := by
  apply h_child_line_of_contact (7/3 : ℝ) u (7553331/100000000 : ℝ) (-4/1 : ℝ) (10226130853/2500000000 : ℝ) (by norm_num)
    hu0 huq (by norm_num) (by norm_num) (by norm_num)
  convert dh_contact_15_bound using 1 <;> ring

end F4Heavy.Analysis
