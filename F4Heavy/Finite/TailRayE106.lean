module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite

def tail_ray_E1_06_numerator_power : List Fraction := [⟨343665216, 1⟩, ⟨1264291992, 1⟩, ⟨1792036255, 1⟩, ⟨1111860575, 1⟩, ⟨220397080, 1⟩]
def tail_ray_E1_06_numerator_controls : List Fraction := [Fraction.mul ⟨1, 8000⟩ (Fraction.mul ⟨64704158880104, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨1, 8000⟩ (Fraction.mul ⟨275013718211564, 1⟩ ⟨1, 4⟩), Fraction.mul ⟨1, 8000⟩ (Fraction.mul ⟨438321562754034, 1⟩ ⟨1, 6⟩), Fraction.mul ⟨1, 8000⟩ (Fraction.mul ⟨310479570379349, 1⟩ ⟨1, 4⟩), Fraction.mul ⟨1, 8000⟩ (Fraction.mul ⟨82468459564949, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_E1_06_numerator_coefficient_0 : (Fraction.positive ⟨64704158880104, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_06_numerator_coefficient_1 : (Fraction.positive ⟨275013718211564, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_06_numerator_coefficient_2 : (Fraction.positive ⟨438321562754034, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_06_numerator_coefficient_3 : (Fraction.positive ⟨310479570379349, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_06_numerator_coefficient_4 : (Fraction.positive ⟨82468459564949, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_06_numerator_scale_positive : (Fraction.positive ⟨1, 8000⟩) = true := by
  decide +kernel

theorem tail_ray_E1_06_numerator_reconstruct : (Fraction.allEq (bernstein tail_ray_E1_06_numerator_power ⟨13, 10⟩ ⟨29, 20⟩ 4) tail_ray_E1_06_numerator_controls) = true := by
  decide +kernel

def tail_ray_E1_06_denominator_power : List Fraction := [⟨503316480, 1⟩, ⟨1761607680, 1⟩, ⟨2044723200, 1⟩, ⟨786432000, 1⟩]
def tail_ray_E1_06_denominator_controls : List Fraction := [Fraction.mul ⟨884736, 1⟩ (Fraction.mul ⟨9016, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨884736, 1⟩ (Fraction.mul ⟨28924, 1⟩ ⟨1, 3⟩), Fraction.mul ⟨884736, 1⟩ (Fraction.mul ⟨30930, 1⟩ ⟨1, 3⟩), Fraction.mul ⟨884736, 1⟩ (Fraction.mul ⟨11025, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_E1_06_denominator_coefficient_0 : (Fraction.positive ⟨9016, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_06_denominator_coefficient_1 : (Fraction.positive ⟨28924, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_06_denominator_coefficient_2 : (Fraction.positive ⟨30930, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_06_denominator_coefficient_3 : (Fraction.positive ⟨11025, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_06_denominator_scale_positive : (Fraction.positive ⟨884736, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_06_denominator_reconstruct : (Fraction.allEq (bernstein tail_ray_E1_06_denominator_power ⟨13, 10⟩ ⟨29, 20⟩ 3) tail_ray_E1_06_denominator_controls) = true := by
  decide +kernel

end F4Heavy.Finite
