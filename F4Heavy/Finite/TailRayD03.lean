module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite

def tail_ray_D_03_numerator_power : List Fraction := [⟨19185955, 16777216⟩, ⟨-20975, 65536⟩]
def tail_ray_D_03_numerator_controls : List Fraction := [Fraction.mul ⟨25, 16777216⟩ (Fraction.mul ⟨595611, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨25, 16777216⟩ (Fraction.mul ⟨488219, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_D_03_numerator_coefficient_0 : (Fraction.positive ⟨595611, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_03_numerator_coefficient_1 : (Fraction.positive ⟨488219, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_03_numerator_scale_positive : (Fraction.positive ⟨25, 16777216⟩) = true := by
  decide +kernel

theorem tail_ray_D_03_numerator_reconstruct : (Fraction.allEq (bernstein tail_ray_D_03_numerator_power ⟨4, 5⟩ ⟨13, 10⟩ 1) tail_ray_D_03_numerator_controls) = true := by
  decide +kernel

def tail_ray_D_03_denominator_power : List Fraction := [⟨1, 1⟩]
def tail_ray_D_03_denominator_controls : List Fraction := [Fraction.mul ⟨1, 1⟩ (Fraction.mul ⟨1, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_D_03_denominator_coefficient_0 : (Fraction.positive ⟨1, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_03_denominator_scale_positive : (Fraction.positive ⟨1, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_03_denominator_reconstruct : (Fraction.allEq (bernstein tail_ray_D_03_denominator_power ⟨4, 5⟩ ⟨13, 10⟩ 0) tail_ray_D_03_denominator_controls) = true := by
  decide +kernel

end F4Heavy.Finite
