module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite

def tail_ray_E2_08_numerator_power : List Fraction := [⟨6356304, 1⟩, ⟨51855000, 1⟩, ⟨104549706, 1⟩, ⟨96426601, 1⟩, ⟨42684032, 1⟩]
def tail_ray_E2_08_numerator_controls : List Fraction := [Fraction.mul ⟨3, 40000⟩ (Fraction.mul ⟨10453538500931, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨3, 40000⟩ (Fraction.mul ⟨44781694726587, 1⟩ ⟨1, 4⟩), Fraction.mul ⟨3, 40000⟩ (Fraction.mul ⟨71942592519384, 1⟩ ⟨1, 6⟩), Fraction.mul ⟨3, 40000⟩ (Fraction.mul ⟨51369734592128, 1⟩ ⟨1, 4⟩), Fraction.mul ⟨3, 40000⟩ (Fraction.mul ⟨13755586415616, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_E2_08_numerator_coefficient_0 : (Fraction.positive ⟨10453538500931, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_08_numerator_coefficient_1 : (Fraction.positive ⟨44781694726587, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_08_numerator_coefficient_2 : (Fraction.positive ⟨71942592519384, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_08_numerator_coefficient_3 : (Fraction.positive ⟨51369734592128, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_08_numerator_coefficient_4 : (Fraction.positive ⟨13755586415616, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_08_numerator_scale_positive : (Fraction.positive ⟨3, 40000⟩) = true := by
  decide +kernel

theorem tail_ray_E2_08_numerator_reconstruct : (Fraction.allEq (bernstein tail_ray_E2_08_numerator_power ⟨29, 20⟩ ⟨8, 5⟩ 4) tail_ray_E2_08_numerator_controls) = true := by
  decide +kernel

def tail_ray_E2_08_denominator_power : List Fraction := [⟨0, 1⟩, ⟨50331648, 1⟩, ⟨125829120, 1⟩, ⟨78643200, 1⟩]
def tail_ray_E2_08_denominator_controls : List Fraction := [Fraction.mul ⟨442368, 5⟩ (Fraction.mul ⟨6525, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨442368, 5⟩ (Fraction.mul ⟨21120, 1⟩ ⟨1, 3⟩), Fraction.mul ⟨442368, 5⟩ (Fraction.mul ⟨22784, 1⟩ ⟨1, 3⟩), Fraction.mul ⟨442368, 5⟩ (Fraction.mul ⟨8192, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_E2_08_denominator_coefficient_0 : (Fraction.positive ⟨6525, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_08_denominator_coefficient_1 : (Fraction.positive ⟨21120, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_08_denominator_coefficient_2 : (Fraction.positive ⟨22784, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_08_denominator_coefficient_3 : (Fraction.positive ⟨8192, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_08_denominator_scale_positive : (Fraction.positive ⟨442368, 5⟩) = true := by
  decide +kernel

theorem tail_ray_E2_08_denominator_reconstruct : (Fraction.allEq (bernstein tail_ray_E2_08_denominator_power ⟨29, 20⟩ ⟨8, 5⟩ 3) tail_ray_E2_08_denominator_controls) = true := by
  decide +kernel

end F4Heavy.Finite
