module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite

def tail_ray_E2_03_numerator_power : List Fraction := [⟨3814167, 8388608⟩, ⟨4579, 65536⟩]
def tail_ray_E2_03_numerator_controls : List Fraction := [Fraction.mul ⟨1, 41943040⟩ (Fraction.mul ⟨23320147, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨1, 41943040⟩ (Fraction.mul ⟨23759731, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_E2_03_numerator_coefficient_0 : (Fraction.positive ⟨23320147, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_03_numerator_coefficient_1 : (Fraction.positive ⟨23759731, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_03_numerator_scale_positive : (Fraction.positive ⟨1, 41943040⟩) = true := by
  decide +kernel

theorem tail_ray_E2_03_numerator_reconstruct : (Fraction.allEq (bernstein tail_ray_E2_03_numerator_power ⟨29, 20⟩ ⟨8, 5⟩ 1) tail_ray_E2_03_numerator_controls) = true := by
  decide +kernel

def tail_ray_E2_03_denominator_power : List Fraction := [⟨1, 1⟩]
def tail_ray_E2_03_denominator_controls : List Fraction := [Fraction.mul ⟨1, 1⟩ (Fraction.mul ⟨1, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_E2_03_denominator_coefficient_0 : (Fraction.positive ⟨1, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_03_denominator_scale_positive : (Fraction.positive ⟨1, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_03_denominator_reconstruct : (Fraction.allEq (bernstein tail_ray_E2_03_denominator_power ⟨29, 20⟩ ⟨8, 5⟩ 0) tail_ray_E2_03_denominator_controls) = true := by
  decide +kernel

end F4Heavy.Finite
