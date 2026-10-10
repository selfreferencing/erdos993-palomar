module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite

def tail_ray_H_01_numerator_power : List Fraction := [⟨4, 1⟩, ⟨-1, 1⟩]
def tail_ray_H_01_numerator_controls : List Fraction := [Fraction.mul ⟨1, 12⟩ (Fraction.mul ⟨27, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨1, 12⟩ (Fraction.mul ⟨20, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_H_01_numerator_coefficient_0 : (Fraction.positive ⟨27, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_01_numerator_coefficient_1 : (Fraction.positive ⟨20, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_01_numerator_scale_positive : (Fraction.positive ⟨1, 12⟩) = true := by
  decide +kernel

theorem tail_ray_H_01_numerator_reconstruct : (Fraction.allEq (bernstein tail_ray_H_01_numerator_power ⟨7, 4⟩ ⟨7, 3⟩ 1) tail_ray_H_01_numerator_controls) = true := by
  decide +kernel

def tail_ray_H_01_denominator_power : List Fraction := [⟨24, 1⟩, ⟨30, 1⟩]
def tail_ray_H_01_denominator_controls : List Fraction := [Fraction.mul ⟨1, 2⟩ (Fraction.mul ⟨153, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨1, 2⟩ (Fraction.mul ⟨188, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_H_01_denominator_coefficient_0 : (Fraction.positive ⟨153, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_01_denominator_coefficient_1 : (Fraction.positive ⟨188, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_01_denominator_scale_positive : (Fraction.positive ⟨1, 2⟩) = true := by
  decide +kernel

theorem tail_ray_H_01_denominator_reconstruct : (Fraction.allEq (bernstein tail_ray_H_01_denominator_power ⟨7, 4⟩ ⟨7, 3⟩ 1) tail_ray_H_01_denominator_controls) = true := by
  decide +kernel

end F4Heavy.Finite
