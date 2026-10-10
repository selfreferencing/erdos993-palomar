module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite

def tail_ray_E1_12_numerator_power : List Fraction := [⟨120480480, 1⟩, ⟨242491272, 1⟩, ⟨66600869, 1⟩, ⟨-60595384, 1⟩]
def tail_ray_E1_12_numerator_controls : List Fraction := [Fraction.mul ⟨1, 2000⟩ (Fraction.mul ⟨830293087124, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨1, 2000⟩ (Fraction.mul ⟨2523409741728, 1⟩ ⟨1, 3⟩), Fraction.mul ⟨1, 2000⟩ (Fraction.mul ⟨2548302771297, 1⟩ ⟨1, 3⟩), Fraction.mul ⟨1, 2000⟩ (Fraction.mul ⟨854777097851, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_E1_12_numerator_coefficient_0 : (Fraction.positive ⟨830293087124, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_12_numerator_coefficient_1 : (Fraction.positive ⟨2523409741728, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_12_numerator_coefficient_2 : (Fraction.positive ⟨2548302771297, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_12_numerator_coefficient_3 : (Fraction.positive ⟨854777097851, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_12_numerator_scale_positive : (Fraction.positive ⟨1, 2000⟩) = true := by
  decide +kernel

theorem tail_ray_E1_12_numerator_reconstruct : (Fraction.allEq (bernstein tail_ray_E1_12_numerator_power ⟨13, 10⟩ ⟨29, 20⟩ 3) tail_ray_E1_12_numerator_controls) = true := by
  decide +kernel

def tail_ray_E1_12_denominator_power : List Fraction := [⟨50331648, 1⟩, ⟨125829120, 1⟩, ⟨78643200, 1⟩]
def tail_ray_E1_12_denominator_controls : List Fraction := [Fraction.mul ⟨1769472, 1⟩ (Fraction.mul ⟨196, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨1769472, 1⟩ (Fraction.mul ⟨420, 1⟩ ⟨1, 2⟩), Fraction.mul ⟨1769472, 1⟩ (Fraction.mul ⟨225, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_E1_12_denominator_coefficient_0 : (Fraction.positive ⟨196, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_12_denominator_coefficient_1 : (Fraction.positive ⟨420, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_12_denominator_coefficient_2 : (Fraction.positive ⟨225, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_12_denominator_scale_positive : (Fraction.positive ⟨1769472, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_12_denominator_reconstruct : (Fraction.allEq (bernstein tail_ray_E1_12_denominator_power ⟨13, 10⟩ ⟨29, 20⟩ 2) tail_ray_E1_12_denominator_controls) = true := by
  decide +kernel

end F4Heavy.Finite
