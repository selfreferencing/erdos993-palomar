module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite

def tail_ray_D_01_numerator_power : List Fraction := [⟨16, 1⟩, ⟨-9, 1⟩]
def tail_ray_D_01_numerator_controls : List Fraction := [Fraction.mul ⟨1, 10⟩ (Fraction.mul ⟨88, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨1, 10⟩ (Fraction.mul ⟨43, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_D_01_numerator_coefficient_0 : (Fraction.positive ⟨88, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_01_numerator_coefficient_1 : (Fraction.positive ⟨43, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_01_numerator_scale_positive : (Fraction.positive ⟨1, 10⟩) = true := by
  decide +kernel

theorem tail_ray_D_01_numerator_reconstruct : (Fraction.allEq (bernstein tail_ray_D_01_numerator_power ⟨4, 5⟩ ⟨13, 10⟩ 1) tail_ray_D_01_numerator_controls) = true := by
  decide +kernel

def tail_ray_D_01_denominator_power : List Fraction := [⟨96, 1⟩, ⟨126, 1⟩]
def tail_ray_D_01_denominator_controls : List Fraction := [Fraction.mul ⟨3, 5⟩ (Fraction.mul ⟨328, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨3, 5⟩ (Fraction.mul ⟨433, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_D_01_denominator_coefficient_0 : (Fraction.positive ⟨328, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_01_denominator_coefficient_1 : (Fraction.positive ⟨433, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_01_denominator_scale_positive : (Fraction.positive ⟨3, 5⟩) = true := by
  decide +kernel

theorem tail_ray_D_01_denominator_reconstruct : (Fraction.allEq (bernstein tail_ray_D_01_denominator_power ⟨4, 5⟩ ⟨13, 10⟩ 1) tail_ray_D_01_denominator_controls) = true := by
  decide +kernel

end F4Heavy.Finite
