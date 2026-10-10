module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite

def tail_ray_E1_10_numerator_power : List Fraction := [⟨40160160, 1⟩, ⟨73103776, 1⟩, ⟨11286231, 1⟩, ⟨-21946344, 1⟩]
def tail_ray_E1_10_numerator_controls : List Fraction := [Fraction.mul ⟨1, 2000⟩ (Fraction.mul ⟨212105362844, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨1, 2000⟩ (Fraction.mul ⟨633670092288, 1⟩ ⟨1, 3⟩), Fraction.mul ⟨1, 2000⟩ (Fraction.mul ⟨627680393067, 1⟩ ⟨1, 3⟩), Fraction.mul ⟨1, 2000⟩ (Fraction.mul ⟨205967525801, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_E1_10_numerator_coefficient_0 : (Fraction.positive ⟨212105362844, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_10_numerator_coefficient_1 : (Fraction.positive ⟨633670092288, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_10_numerator_coefficient_2 : (Fraction.positive ⟨627680393067, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_10_numerator_coefficient_3 : (Fraction.positive ⟨205967525801, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_10_numerator_scale_positive : (Fraction.positive ⟨1, 2000⟩) = true := by
  decide +kernel

theorem tail_ray_E1_10_numerator_reconstruct : (Fraction.allEq (bernstein tail_ray_E1_10_numerator_power ⟨13, 10⟩ ⟨29, 20⟩ 3) tail_ray_E1_10_numerator_controls) = true := by
  decide +kernel

def tail_ray_E1_10_denominator_power : List Fraction := [⟨16777216, 1⟩, ⟨41943040, 1⟩, ⟨26214400, 1⟩]
def tail_ray_E1_10_denominator_controls : List Fraction := [Fraction.mul ⟨589824, 1⟩ (Fraction.mul ⟨196, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨589824, 1⟩ (Fraction.mul ⟨420, 1⟩ ⟨1, 2⟩), Fraction.mul ⟨589824, 1⟩ (Fraction.mul ⟨225, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_E1_10_denominator_coefficient_0 : (Fraction.positive ⟨196, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_10_denominator_coefficient_1 : (Fraction.positive ⟨420, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_10_denominator_coefficient_2 : (Fraction.positive ⟨225, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_10_denominator_scale_positive : (Fraction.positive ⟨589824, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_10_denominator_reconstruct : (Fraction.allEq (bernstein tail_ray_E1_10_denominator_power ⟨13, 10⟩ ⟨29, 20⟩ 2) tail_ray_E1_10_denominator_controls) = true := by
  decide +kernel

end F4Heavy.Finite
