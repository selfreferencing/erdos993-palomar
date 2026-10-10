module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite

def tail_ray_E2_12_numerator_power : List Fraction := [⟨155556588, 1⟩, ⟨332057016, 1⟩, ⟨157876975, 1⟩, ⟨-17922688, 1⟩]
def tail_ray_E2_12_numerator_controls : List Fraction := [Fraction.mul ⟨3, 2000⟩ (Fraction.mul ⟨609557364289, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨3, 2000⟩ (Fraction.mul ⟨1896357381761, 1⟩ ⟨1, 3⟩), Fraction.mul ⟨3, 2000⟩ (Fraction.mul ⟨1965241369888, 1⟩ ⟨1, 3⟩), Fraction.mul ⟨3, 2000⟩ (Fraction.mul ⟨678401026368, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_E2_12_numerator_coefficient_0 : (Fraction.positive ⟨609557364289, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_12_numerator_coefficient_1 : (Fraction.positive ⟨1896357381761, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_12_numerator_coefficient_2 : (Fraction.positive ⟨1965241369888, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_12_numerator_coefficient_3 : (Fraction.positive ⟨678401026368, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_12_numerator_scale_positive : (Fraction.positive ⟨3, 2000⟩) = true := by
  decide +kernel

theorem tail_ray_E2_12_numerator_reconstruct : (Fraction.allEq (bernstein tail_ray_E2_12_numerator_power ⟨29, 20⟩ ⟨8, 5⟩ 3) tail_ray_E2_12_numerator_controls) = true := by
  decide +kernel

def tail_ray_E2_12_denominator_power : List Fraction := [⟨100663296, 1⟩, ⟨251658240, 1⟩, ⟨157286400, 1⟩]
def tail_ray_E2_12_denominator_controls : List Fraction := [Fraction.mul ⟨3538944, 1⟩ (Fraction.mul ⟨225, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨3538944, 1⟩ (Fraction.mul ⟨480, 1⟩ ⟨1, 2⟩), Fraction.mul ⟨3538944, 1⟩ (Fraction.mul ⟨256, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_E2_12_denominator_coefficient_0 : (Fraction.positive ⟨225, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_12_denominator_coefficient_1 : (Fraction.positive ⟨480, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_12_denominator_coefficient_2 : (Fraction.positive ⟨256, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_12_denominator_scale_positive : (Fraction.positive ⟨3538944, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_12_denominator_reconstruct : (Fraction.allEq (bernstein tail_ray_E2_12_denominator_power ⟨29, 20⟩ ⟨8, 5⟩ 2) tail_ray_E2_12_denominator_controls) = true := by
  decide +kernel

end F4Heavy.Finite
