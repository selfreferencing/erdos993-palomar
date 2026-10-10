module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite

def tail_ray_D_10_numerator_power : List Fraction := [⟨919582528, 1⟩, ⟨1414043896, 1⟩, ⟨582523383, 1⟩, ⟨396995840, 1⟩]
def tail_ray_D_10_numerator_controls : List Fraction := [Fraction.mul ⟨1, 20⟩ (Fraction.mul ⟨52537889600, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨1, 20⟩ (Fraction.mul ⟨188696802016, 1⟩ ⟨1, 3⟩), Fraction.mul ⟨1, 20⟩ (Fraction.mul ⟨227456502227, 1⟩ ⟨1, 3⟩), Fraction.mul ⟨1, 20⟩ (Fraction.mul ⟨92290079411, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_D_10_numerator_coefficient_0 : (Fraction.positive ⟨52537889600, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_10_numerator_coefficient_1 : (Fraction.positive ⟨188696802016, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_10_numerator_coefficient_2 : (Fraction.positive ⟨227456502227, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_10_numerator_coefficient_3 : (Fraction.positive ⟨92290079411, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_10_numerator_scale_positive : (Fraction.positive ⟨1, 20⟩) = true := by
  decide +kernel

theorem tail_ray_D_10_numerator_reconstruct : (Fraction.allEq (bernstein tail_ray_D_10_numerator_power ⟨4, 5⟩ ⟨13, 10⟩ 3) tail_ray_D_10_numerator_controls) = true := by
  decide +kernel

def tail_ray_D_10_denominator_power : List Fraction := [⟨1073741824, 1⟩, ⟨2818572288, 1⟩, ⟨1849688064, 1⟩]
def tail_ray_D_10_denominator_controls : List Fraction := [Fraction.mul ⟨1048576, 25⟩ (Fraction.mul ⟨107584, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨1048576, 25⟩ (Fraction.mul ⟨284048, 1⟩ ⟨1, 2⟩), Fraction.mul ⟨1048576, 25⟩ (Fraction.mul ⟨187489, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_D_10_denominator_coefficient_0 : (Fraction.positive ⟨107584, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_10_denominator_coefficient_1 : (Fraction.positive ⟨284048, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_10_denominator_coefficient_2 : (Fraction.positive ⟨187489, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_10_denominator_scale_positive : (Fraction.positive ⟨1048576, 25⟩) = true := by
  decide +kernel

theorem tail_ray_D_10_denominator_reconstruct : (Fraction.allEq (bernstein tail_ray_D_10_denominator_power ⟨4, 5⟩ ⟨13, 10⟩ 2) tail_ray_D_10_denominator_controls) = true := by
  decide +kernel

end F4Heavy.Finite
