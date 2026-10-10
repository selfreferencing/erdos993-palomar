module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite

def tail_ray_H_03_numerator_power : List Fraction := [⟨-18040391, 16777216⟩, ⟨40757, 65536⟩]
def tail_ray_H_03_numerator_controls : List Fraction := [Fraction.mul ⟨1, 50331648⟩ (Fraction.mul ⟨656235, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨1, 50331648⟩ (Fraction.mul ⟨18915371, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_H_03_numerator_coefficient_0 : (Fraction.positive ⟨656235, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_03_numerator_coefficient_1 : (Fraction.positive ⟨18915371, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_03_numerator_scale_positive : (Fraction.positive ⟨1, 50331648⟩) = true := by
  decide +kernel

theorem tail_ray_H_03_numerator_reconstruct : (Fraction.allEq (bernstein tail_ray_H_03_numerator_power ⟨7, 4⟩ ⟨7, 3⟩ 1) tail_ray_H_03_numerator_controls) = true := by
  decide +kernel

def tail_ray_H_03_denominator_power : List Fraction := [⟨1, 1⟩]
def tail_ray_H_03_denominator_controls : List Fraction := [Fraction.mul ⟨1, 1⟩ (Fraction.mul ⟨1, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_H_03_denominator_coefficient_0 : (Fraction.positive ⟨1, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_03_denominator_scale_positive : (Fraction.positive ⟨1, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_03_denominator_reconstruct : (Fraction.allEq (bernstein tail_ray_H_03_denominator_power ⟨7, 4⟩ ⟨7, 3⟩ 0) tail_ray_H_03_denominator_controls) = true := by
  decide +kernel

end F4Heavy.Finite
