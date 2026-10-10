module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite

def tail_ray_E1_02_numerator_power : List Fraction := [⟨381977179873, 439228700000000⟩, ⟨11779595, 17569148⟩, ⟨-398369, 4392287⟩]
def tail_ray_E1_02_numerator_controls : List Fraction := [Fraction.mul ⟨1, 439228700000000⟩ (Fraction.mul ⟨315894453679873, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨1, 439228700000000⟩ (Fraction.mul ⟨660425997609746, 1⟩ ⟨1, 2⟩), Fraction.mul ⟨1, 439228700000000⟩ (Fraction.mul ⟨343635213679873, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_E1_02_numerator_coefficient_0 : (Fraction.positive ⟨315894453679873, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_02_numerator_coefficient_1 : (Fraction.positive ⟨660425997609746, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_02_numerator_coefficient_2 : (Fraction.positive ⟨343635213679873, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_02_numerator_scale_positive : (Fraction.positive ⟨1, 439228700000000⟩) = true := by
  decide +kernel

theorem tail_ray_E1_02_numerator_reconstruct : (Fraction.allEq (bernstein tail_ray_E1_02_numerator_power ⟨13, 10⟩ ⟨29, 20⟩ 2) tail_ray_E1_02_numerator_controls) = true := by
  decide +kernel

def tail_ray_E1_02_denominator_power : List Fraction := [⟨1, 1⟩]
def tail_ray_E1_02_denominator_controls : List Fraction := [Fraction.mul ⟨1, 1⟩ (Fraction.mul ⟨1, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_E1_02_denominator_coefficient_0 : (Fraction.positive ⟨1, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_02_denominator_scale_positive : (Fraction.positive ⟨1, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_02_denominator_reconstruct : (Fraction.allEq (bernstein tail_ray_E1_02_denominator_power ⟨13, 10⟩ ⟨29, 20⟩ 0) tail_ray_E1_02_denominator_controls) = true := by
  decide +kernel

end F4Heavy.Finite
