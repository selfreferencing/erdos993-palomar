module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite

def tail_ray_H_02_numerator_power : List Fraction := [⟨4751530412455543, 57452481900000000⟩, ⟨108879230, 191508273⟩, ⟨-3748376, 63836091⟩]
def tail_ray_H_02_numerator_controls : List Fraction := [Fraction.mul ⟨1, 57452481900000000⟩ (Fraction.mul ⟨51581664812455543, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨1, 57452481900000000⟩ (Fraction.mul ⟨115329553974911086, 1⟩ ⟨1, 2⟩), Fraction.mul ⟨1, 57452481900000000⟩ (Fraction.mul ⟨62599949012455543, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_H_02_numerator_coefficient_0 : (Fraction.positive ⟨51581664812455543, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_02_numerator_coefficient_1 : (Fraction.positive ⟨115329553974911086, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_02_numerator_coefficient_2 : (Fraction.positive ⟨62599949012455543, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_02_numerator_scale_positive : (Fraction.positive ⟨1, 57452481900000000⟩) = true := by
  decide +kernel

theorem tail_ray_H_02_numerator_reconstruct : (Fraction.allEq (bernstein tail_ray_H_02_numerator_power ⟨7, 4⟩ ⟨7, 3⟩ 2) tail_ray_H_02_numerator_controls) = true := by
  decide +kernel

def tail_ray_H_02_denominator_power : List Fraction := [⟨1, 1⟩]
def tail_ray_H_02_denominator_controls : List Fraction := [Fraction.mul ⟨1, 1⟩ (Fraction.mul ⟨1, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_H_02_denominator_coefficient_0 : (Fraction.positive ⟨1, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_02_denominator_scale_positive : (Fraction.positive ⟨1, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_02_denominator_reconstruct : (Fraction.allEq (bernstein tail_ray_H_02_denominator_power ⟨7, 4⟩ ⟨7, 3⟩ 0) tail_ray_H_02_denominator_controls) = true := by
  decide +kernel

end F4Heavy.Finite
