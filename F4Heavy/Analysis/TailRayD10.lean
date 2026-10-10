module

public import F4Heavy.Analysis.TailRaySemantics
public import F4Heavy.Analysis.TailDefinitions
public import F4Heavy.Finite.TailRayD10

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

theorem tail_ray_D_10_numerator_positive (lam : ℝ) (hr : InRow .D lam) :
    0 < realHorner (tail_ray_D_10_numerator_power.map fractionValue) lam := by
  apply cap_bernstein_positive_values tail_ray_D_10_numerator_power tail_ray_D_10_numerator_controls ⟨4, 5⟩ ⟨13, 10⟩ 3 lam
  · norm_num [tail_ray_D_10_numerator_power]
  · norm_num
  · norm_num
  · norm_num [tail_ray_D_10_numerator_power]
  · norm_num [fractionValue]
  · simpa [InRow, rowData, fractionValue] using hr.1
  · simpa [InRow, rowData, fractionValue] using hr.2
  · exact tail_ray_D_10_numerator_reconstruct
  · intro c hc
    simp only [tail_ray_D_10_numerator_controls, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact tail_scaled_ray_positive _ _ _ tail_ray_D_10_numerator_scale_positive tail_ray_D_10_numerator_coefficient_0 (by norm_num)
    · exact tail_scaled_ray_positive _ _ _ tail_ray_D_10_numerator_scale_positive tail_ray_D_10_numerator_coefficient_1 (by norm_num)
    · exact tail_scaled_ray_positive _ _ _ tail_ray_D_10_numerator_scale_positive tail_ray_D_10_numerator_coefficient_2 (by norm_num)
    · exact tail_scaled_ray_positive _ _ _ tail_ray_D_10_numerator_scale_positive tail_ray_D_10_numerator_coefficient_3 (by norm_num)

theorem tail_ray_D_10_denominator_positive (lam : ℝ) (hr : InRow .D lam) :
    0 < realHorner (tail_ray_D_10_denominator_power.map fractionValue) lam := by
  apply cap_bernstein_positive_values tail_ray_D_10_denominator_power tail_ray_D_10_denominator_controls ⟨4, 5⟩ ⟨13, 10⟩ 2 lam
  · norm_num [tail_ray_D_10_denominator_power]
  · norm_num
  · norm_num
  · norm_num [tail_ray_D_10_denominator_power]
  · norm_num [fractionValue]
  · simpa [InRow, rowData, fractionValue] using hr.1
  · simpa [InRow, rowData, fractionValue] using hr.2
  · exact tail_ray_D_10_denominator_reconstruct
  · intro c hc
    simp only [tail_ray_D_10_denominator_controls, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact tail_scaled_ray_positive _ _ _ tail_ray_D_10_denominator_scale_positive tail_ray_D_10_denominator_coefficient_0 (by norm_num)
    · exact tail_scaled_ray_positive _ _ _ tail_ray_D_10_denominator_scale_positive tail_ray_D_10_denominator_coefficient_1 (by norm_num)
    · exact tail_scaled_ray_positive _ _ _ tail_ray_D_10_denominator_scale_positive tail_ray_D_10_denominator_coefficient_2 (by norm_num)

end F4Heavy.Analysis
