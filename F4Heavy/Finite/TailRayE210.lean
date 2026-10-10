module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite

def tail_ray_E2_10_numerator_power : List Fraction := [⟨51852196, 1⟩, ⟨94085302, 1⟩, ⟨30100749, 1⟩, ⟨-8359808, 1⟩]
def tail_ray_E2_10_numerator_controls : List Fraction := [Fraction.mul ⟨3, 2000⟩ (Fraction.mul ⟨150717859339, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨3, 2000⟩ (Fraction.mul ⟨465018376531, 1⟩ ⟨1, 3⟩), Fraction.mul ⟨3, 2000⟩ (Fraction.mul ⟨477789208808, 1⟩ ⟨1, 3⟩), Fraction.mul ⟨3, 2000⟩ (Fraction.mul ⟨163469882048, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_E2_10_numerator_coefficient_0 : (Fraction.positive ⟨150717859339, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_10_numerator_coefficient_1 : (Fraction.positive ⟨465018376531, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_10_numerator_coefficient_2 : (Fraction.positive ⟨477789208808, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_10_numerator_coefficient_3 : (Fraction.positive ⟨163469882048, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_10_numerator_scale_positive : (Fraction.positive ⟨3, 2000⟩) = true := by
  decide +kernel

theorem tail_ray_E2_10_numerator_reconstruct : (Fraction.allEq (bernstein tail_ray_E2_10_numerator_power ⟨29, 20⟩ ⟨8, 5⟩ 3) tail_ray_E2_10_numerator_controls) = true := by
  decide +kernel

def tail_ray_E2_10_denominator_power : List Fraction := [⟨33554432, 1⟩, ⟨83886080, 1⟩, ⟨52428800, 1⟩]
def tail_ray_E2_10_denominator_controls : List Fraction := [Fraction.mul ⟨1179648, 1⟩ (Fraction.mul ⟨225, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨1179648, 1⟩ (Fraction.mul ⟨480, 1⟩ ⟨1, 2⟩), Fraction.mul ⟨1179648, 1⟩ (Fraction.mul ⟨256, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_E2_10_denominator_coefficient_0 : (Fraction.positive ⟨225, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_10_denominator_coefficient_1 : (Fraction.positive ⟨480, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_10_denominator_coefficient_2 : (Fraction.positive ⟨256, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_10_denominator_scale_positive : (Fraction.positive ⟨1179648, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_10_denominator_reconstruct : (Fraction.allEq (bernstein tail_ray_E2_10_denominator_power ⟨29, 20⟩ ⟨8, 5⟩ 2) tail_ray_E2_10_denominator_controls) = true := by
  decide +kernel

end F4Heavy.Finite
