module

public import F4Heavy.Analysis.TailRaySemantics
public import F4Heavy.Analysis.TailDefinitions
public import F4Heavy.Finite.TailRayE115

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

theorem tail_ray_E1_15_numerator_positive (lam : ℝ) (hr : InRow .E1 lam) :
    0 < realHorner (tail_ray_E1_15_numerator_power.map fractionValue) lam := by
  apply cap_bernstein_positive_values tail_ray_E1_15_numerator_power tail_ray_E1_15_numerator_controls ⟨13, 10⟩ ⟨29, 20⟩ 15 lam
  · norm_num [tail_ray_E1_15_numerator_power]
  · norm_num
  · norm_num
  · norm_num [tail_ray_E1_15_numerator_power]
  · norm_num [fractionValue]
  · simpa [InRow, rowData, fractionValue] using hr.1
  · simpa [InRow, rowData, fractionValue] using hr.2
  · exact tail_ray_E1_15_numerator_reconstruct
  · intro c hc
    simp only [tail_ray_E1_15_numerator_controls, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact tail_scaled_ray_positive _ _ _ tail_ray_E1_15_numerator_scale_positive tail_ray_E1_15_numerator_coefficient_0 (by norm_num)
    · exact tail_scaled_ray_positive _ _ _ tail_ray_E1_15_numerator_scale_positive tail_ray_E1_15_numerator_coefficient_1 (by norm_num)
    · exact tail_scaled_ray_positive _ _ _ tail_ray_E1_15_numerator_scale_positive tail_ray_E1_15_numerator_coefficient_2 (by norm_num)
    · exact tail_scaled_ray_positive _ _ _ tail_ray_E1_15_numerator_scale_positive tail_ray_E1_15_numerator_coefficient_3 (by norm_num)
    · exact tail_scaled_ray_positive _ _ _ tail_ray_E1_15_numerator_scale_positive tail_ray_E1_15_numerator_coefficient_4 (by norm_num)
    · exact tail_scaled_ray_positive _ _ _ tail_ray_E1_15_numerator_scale_positive tail_ray_E1_15_numerator_coefficient_5 (by norm_num)
    · exact tail_scaled_ray_positive _ _ _ tail_ray_E1_15_numerator_scale_positive tail_ray_E1_15_numerator_coefficient_6 (by norm_num)
    · exact tail_scaled_ray_positive _ _ _ tail_ray_E1_15_numerator_scale_positive tail_ray_E1_15_numerator_coefficient_7 (by norm_num)
    · exact tail_scaled_ray_positive _ _ _ tail_ray_E1_15_numerator_scale_positive tail_ray_E1_15_numerator_coefficient_8 (by norm_num)
    · exact tail_scaled_ray_positive _ _ _ tail_ray_E1_15_numerator_scale_positive tail_ray_E1_15_numerator_coefficient_9 (by norm_num)
    · exact tail_scaled_ray_positive _ _ _ tail_ray_E1_15_numerator_scale_positive tail_ray_E1_15_numerator_coefficient_10 (by norm_num)
    · exact tail_scaled_ray_positive _ _ _ tail_ray_E1_15_numerator_scale_positive tail_ray_E1_15_numerator_coefficient_11 (by norm_num)
    · exact tail_scaled_ray_positive _ _ _ tail_ray_E1_15_numerator_scale_positive tail_ray_E1_15_numerator_coefficient_12 (by norm_num)
    · exact tail_scaled_ray_positive _ _ _ tail_ray_E1_15_numerator_scale_positive tail_ray_E1_15_numerator_coefficient_13 (by norm_num)
    · exact tail_scaled_ray_positive _ _ _ tail_ray_E1_15_numerator_scale_positive tail_ray_E1_15_numerator_coefficient_14 (by norm_num)
    · exact tail_scaled_ray_positive _ _ _ tail_ray_E1_15_numerator_scale_positive tail_ray_E1_15_numerator_coefficient_15 (by norm_num)

theorem tail_ray_E1_15_denominator_positive (lam : ℝ) (hr : InRow .E1 lam) :
    0 < realHorner (tail_ray_E1_15_denominator_power.map fractionValue) lam := by
  apply cap_bernstein_positive_values tail_ray_E1_15_denominator_power tail_ray_E1_15_denominator_controls ⟨13, 10⟩ ⟨29, 20⟩ 11 lam
  · norm_num [tail_ray_E1_15_denominator_power]
  · norm_num
  · norm_num
  · norm_num [tail_ray_E1_15_denominator_power]
  · norm_num [fractionValue]
  · simpa [InRow, rowData, fractionValue] using hr.1
  · simpa [InRow, rowData, fractionValue] using hr.2
  · exact tail_ray_E1_15_denominator_reconstruct
  · intro c hc
    simp only [tail_ray_E1_15_denominator_controls, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact tail_scaled_ray_positive _ _ _ tail_ray_E1_15_denominator_scale_positive tail_ray_E1_15_denominator_coefficient_0 (by norm_num)
    · exact tail_scaled_ray_positive _ _ _ tail_ray_E1_15_denominator_scale_positive tail_ray_E1_15_denominator_coefficient_1 (by norm_num)
    · exact tail_scaled_ray_positive _ _ _ tail_ray_E1_15_denominator_scale_positive tail_ray_E1_15_denominator_coefficient_2 (by norm_num)
    · exact tail_scaled_ray_positive _ _ _ tail_ray_E1_15_denominator_scale_positive tail_ray_E1_15_denominator_coefficient_3 (by norm_num)
    · exact tail_scaled_ray_positive _ _ _ tail_ray_E1_15_denominator_scale_positive tail_ray_E1_15_denominator_coefficient_4 (by norm_num)
    · exact tail_scaled_ray_positive _ _ _ tail_ray_E1_15_denominator_scale_positive tail_ray_E1_15_denominator_coefficient_5 (by norm_num)
    · exact tail_scaled_ray_positive _ _ _ tail_ray_E1_15_denominator_scale_positive tail_ray_E1_15_denominator_coefficient_6 (by norm_num)
    · exact tail_scaled_ray_positive _ _ _ tail_ray_E1_15_denominator_scale_positive tail_ray_E1_15_denominator_coefficient_7 (by norm_num)
    · exact tail_scaled_ray_positive _ _ _ tail_ray_E1_15_denominator_scale_positive tail_ray_E1_15_denominator_coefficient_8 (by norm_num)
    · exact tail_scaled_ray_positive _ _ _ tail_ray_E1_15_denominator_scale_positive tail_ray_E1_15_denominator_coefficient_9 (by norm_num)
    · exact tail_scaled_ray_positive _ _ _ tail_ray_E1_15_denominator_scale_positive tail_ray_E1_15_denominator_coefficient_10 (by norm_num)
    · exact tail_scaled_ray_positive _ _ _ tail_ray_E1_15_denominator_scale_positive tail_ray_E1_15_denominator_coefficient_11 (by norm_num)

end F4Heavy.Analysis
