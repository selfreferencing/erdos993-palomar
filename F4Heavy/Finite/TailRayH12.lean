module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite

def tail_ray_H_12_numerator_power : List Fraction := [⟨4953103008, 1⟩, ⟨10447410936, 1⟩, ⟨4036013387, 1⟩, ⟨-1599455488, 1⟩]
def tail_ray_H_12_numerator_controls : List Fraction := [Fraction.mul ⟨7, 432⟩ (Fraction.mul ⟨1667784222783, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨7, 432⟩ (Fraction.mul ⟨5358977246151, 1⟩ ⟨1, 3⟩), Fraction.mul ⟨7, 432⟩ (Fraction.mul ⟨5623018137528, 1⟩ ⟨1, 3⟩), Fraction.mul ⟨7, 432⟩ (Fraction.mul ⟨1912231784432, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_H_12_numerator_coefficient_0 : (Fraction.positive ⟨1667784222783, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_12_numerator_coefficient_1 : (Fraction.positive ⟨5358977246151, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_12_numerator_coefficient_2 : (Fraction.positive ⟨5623018137528, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_12_numerator_coefficient_3 : (Fraction.positive ⟨1912231784432, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_12_numerator_scale_positive : (Fraction.positive ⟨7, 432⟩) = true := by
  decide +kernel

theorem tail_ray_H_12_numerator_reconstruct : (Fraction.allEq (bernstein tail_ray_H_12_numerator_power ⟨7, 4⟩ ⟨7, 3⟩ 3) tail_ray_H_12_numerator_controls) = true := by
  decide +kernel

def tail_ray_H_12_denominator_power : List Fraction := [⟨1610612736, 1⟩, ⟨4026531840, 1⟩, ⟨2516582400, 1⟩]
def tail_ray_H_12_denominator_controls : List Fraction := [Fraction.mul ⟨2097152, 3⟩ (Fraction.mul ⟨23409, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨2097152, 3⟩ (Fraction.mul ⟨57528, 1⟩ ⟨1, 2⟩), Fraction.mul ⟨2097152, 3⟩ (Fraction.mul ⟨35344, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_H_12_denominator_coefficient_0 : (Fraction.positive ⟨23409, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_12_denominator_coefficient_1 : (Fraction.positive ⟨57528, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_12_denominator_coefficient_2 : (Fraction.positive ⟨35344, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_12_denominator_scale_positive : (Fraction.positive ⟨2097152, 3⟩) = true := by
  decide +kernel

theorem tail_ray_H_12_denominator_reconstruct : (Fraction.allEq (bernstein tail_ray_H_12_denominator_power ⟨7, 4⟩ ⟨7, 3⟩ 2) tail_ray_H_12_denominator_controls) = true := by
  decide +kernel

end F4Heavy.Finite
