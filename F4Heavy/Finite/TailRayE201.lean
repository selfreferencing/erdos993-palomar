module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite

def tail_ray_E2_01_numerator_power : List Fraction := [⟨4, 1⟩, ⟨-1, 1⟩]
def tail_ray_E2_01_numerator_controls : List Fraction := [Fraction.mul ⟨3, 20⟩ (Fraction.mul ⟨17, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨3, 20⟩ (Fraction.mul ⟨16, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_E2_01_numerator_coefficient_0 : (Fraction.positive ⟨17, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_01_numerator_coefficient_1 : (Fraction.positive ⟨16, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_01_numerator_scale_positive : (Fraction.positive ⟨3, 20⟩) = true := by
  decide +kernel

theorem tail_ray_E2_01_numerator_reconstruct : (Fraction.allEq (bernstein tail_ray_E2_01_numerator_power ⟨29, 20⟩ ⟨8, 5⟩ 1) tail_ray_E2_01_numerator_controls) = true := by
  decide +kernel

def tail_ray_E2_01_denominator_power : List Fraction := [⟨24, 1⟩, ⟨30, 1⟩]
def tail_ray_E2_01_denominator_controls : List Fraction := [Fraction.mul ⟨9, 2⟩ (Fraction.mul ⟨15, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨9, 2⟩ (Fraction.mul ⟨16, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_E2_01_denominator_coefficient_0 : (Fraction.positive ⟨15, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_01_denominator_coefficient_1 : (Fraction.positive ⟨16, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_01_denominator_scale_positive : (Fraction.positive ⟨9, 2⟩) = true := by
  decide +kernel

theorem tail_ray_E2_01_denominator_reconstruct : (Fraction.allEq (bernstein tail_ray_E2_01_denominator_power ⟨29, 20⟩ ⟨8, 5⟩ 1) tail_ray_E2_01_denominator_controls) = true := by
  decide +kernel

end F4Heavy.Finite
