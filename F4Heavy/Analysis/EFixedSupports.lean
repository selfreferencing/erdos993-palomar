module

public import F4Heavy.Analysis.EContact00
public import F4Heavy.Analysis.EContact01
public import F4Heavy.Analysis.EContact02
public import F4Heavy.Analysis.EContact03
public import F4Heavy.Analysis.EContact04
public import F4Heavy.Analysis.EContact05
public import F4Heavy.Analysis.EContact06
public import F4Heavy.Analysis.EContact07
public import F4Heavy.Analysis.EContact08

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem e_fixed_support_00 (u : ℝ) (hu0 : 0 ≤ u) (huq : u ≤ (29/49 : ℝ)) :
    childJ (13/10 : ℝ) u ≤ (7/3 : ℝ)*childH u+(-79166889/50000000 : ℝ) := by
  exact e1_child_line_of_contact (13/10 : ℝ) u (13/23 : ℝ) (7/3 : ℝ) (-79166889/50000000 : ℝ) (by norm_num)
    hu0 huq (by norm_num) (by norm_num) (by norm_num) e_contact_00_bound

theorem e_fixed_support_01 (u : ℝ) (hu0 : 0 ≤ u) (huq : u ≤ (29/49 : ℝ)) :
    childJ (13/10 : ℝ) u ≤ (3/10 : ℝ)*childH u+(3500567/100000000 : ℝ) := by
  exact e1_child_line_of_contact (13/10 : ℝ) u (52/207 : ℝ) (3/10 : ℝ) (3500567/100000000 : ℝ) (by norm_num)
    hu0 huq (by norm_num) (by norm_num) (by norm_num) e_contact_01_bound

theorem e_fixed_support_02 (u : ℝ) (hu0 : 0 ≤ u) (huq : u ≤ (29/49 : ℝ)) :
    childJ (13/10 : ℝ) u ≤ (-8/15 : ℝ)*childH u+(38732233/50000000 : ℝ) := by
  exact e1_child_line_of_contact (13/10 : ℝ) u (13/69 : ℝ) (-8/15 : ℝ) (38732233/50000000 : ℝ) (by norm_num)
    hu0 huq (by norm_num) (by norm_num) (by norm_num) e_contact_02_bound

theorem e_fixed_support_03 (u : ℝ) (hu0 : 0 ≤ u) (huq : u ≤ (8/13 : ℝ)) :
    childJ (29/20 : ℝ) u ≤ (7/3 : ℝ)*childH u+(-154103887/100000000 : ℝ) := by
  exact e2_child_line_of_contact (29/20 : ℝ) u (29/49 : ℝ) (7/3 : ℝ) (-154103887/100000000 : ℝ) (by norm_num)
    hu0 huq (by norm_num) (by norm_num) (by norm_num) e_contact_03_bound

theorem e_fixed_support_04 (u : ℝ) (hu0 : 0 ≤ u) (huq : u ≤ (8/13 : ℝ)) :
    childJ (29/20 : ℝ) u ≤ (3/10 : ℝ)*childH u+(5922933/100000000 : ℝ) := by
  exact e2_child_line_of_contact (29/20 : ℝ) u (116/441 : ℝ) (3/10 : ℝ) (5922933/100000000 : ℝ) (by norm_num)
    hu0 huq (by norm_num) (by norm_num) (by norm_num) e_contact_04_bound

theorem e_fixed_support_05 (u : ℝ) (hu0 : 0 ≤ u) (huq : u ≤ (8/13 : ℝ)) :
    childJ (29/20 : ℝ) u ≤ (-8/15 : ℝ)*childH u+(19828959/25000000 : ℝ) := by
  exact e2_child_line_of_contact (29/20 : ℝ) u (29/147 : ℝ) (-8/15 : ℝ) (19828959/25000000 : ℝ) (by norm_num)
    hu0 huq (by norm_num) (by norm_num) (by norm_num) e_contact_05_bound

theorem e_fixed_support_06 (u : ℝ) (hu0 : 0 ≤ u) (huq : u ≤ (8/13 : ℝ)) :
    childJ (8/5 : ℝ) u ≤ (7/3 : ℝ)*childH u+(-150225069/100000000 : ℝ) := by
  exact e2_child_line_of_contact (8/5 : ℝ) u (8/13 : ℝ) (7/3 : ℝ) (-150225069/100000000 : ℝ) (by norm_num)
    hu0 huq (by norm_num) (by norm_num) (by norm_num) e_contact_06_bound

theorem e_fixed_support_07 (u : ℝ) (hu0 : 0 ≤ u) (huq : u ≤ (8/13 : ℝ)) :
    childJ (8/5 : ℝ) u ≤ (3/10 : ℝ)*childH u+(1640021/20000000 : ℝ) := by
  exact e2_child_line_of_contact (8/5 : ℝ) u (32/117 : ℝ) (3/10 : ℝ) (1640021/20000000 : ℝ) (by norm_num)
    hu0 huq (by norm_num) (by norm_num) (by norm_num) e_contact_07_bound

theorem e_fixed_support_08 (u : ℝ) (hu0 : 0 ≤ u) (huq : u ≤ (8/13 : ℝ)) :
    childJ (8/5 : ℝ) u ≤ (-8/15 : ℝ)*childH u+(81122983/100000000 : ℝ) := by
  exact e2_child_line_of_contact (8/5 : ℝ) u (8/39 : ℝ) (-8/15 : ℝ) (81122983/100000000 : ℝ) (by norm_num)
    hu0 huq (by norm_num) (by norm_num) (by norm_num) e_contact_08_bound

end F4Heavy.Analysis
