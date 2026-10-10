module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite

def tail_ray_D_06_numerator_power : List Fraction := [⟨20989320192, 1⟩, ⟨74919847200, 1⟩, ⟨99614439641, 1⟩, ⟨55321744057, 1⟩, ⟨8127881984, 1⟩]
def tail_ray_D_06_numerator_controls : List Fraction := [Fraction.mul ⟨1, 5000⟩ (Fraction.mul ⟨881661763700352, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨1, 5000⟩ (Fraction.mul ⟨4419563558597088, 1⟩ ⟨1, 4⟩), Fraction.mul ⟨1, 5000⟩ (Fraction.mul ⟨8298217208834602, 1⟩ ⟨1, 6⟩), Fraction.mul ⟨1, 5000⟩ (Fraction.mul ⟨6915222650682973, 1⟩ ⟨1, 4⟩), Fraction.mul ⟨1, 5000⟩ (Fraction.mul ⟨2157447199865107, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_D_06_numerator_coefficient_0 : (Fraction.positive ⟨881661763700352, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_06_numerator_coefficient_1 : (Fraction.positive ⟨4419563558597088, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_06_numerator_coefficient_2 : (Fraction.positive ⟨8298217208834602, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_06_numerator_coefficient_3 : (Fraction.positive ⟨6915222650682973, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_06_numerator_coefficient_4 : (Fraction.positive ⟨2157447199865107, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_06_numerator_scale_positive : (Fraction.positive ⟨1, 5000⟩) = true := by
  decide +kernel

theorem tail_ray_D_06_numerator_reconstruct : (Fraction.allEq (bernstein tail_ray_D_06_numerator_power ⟨4, 5⟩ ⟨13, 10⟩ 4) tail_ray_D_06_numerator_controls) = true := by
  decide +kernel

def tail_ray_D_06_denominator_power : List Fraction := [⟨25769803776, 1⟩, ⟨93415538688, 1⟩, ⟨112038248448, 1⟩, ⟨44392513536, 1⟩]
def tail_ray_D_06_denominator_controls : List Fraction := [Fraction.mul ⟨12582912, 125⟩ (Fraction.mul ⟨1936512, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨12582912, 125⟩ (Fraction.mul ⟨7587296, 1⟩ ⟨1, 3⟩), Fraction.mul ⟨12582912, 125⟩ (Fraction.mul ⟨9907906, 1⟩ ⟨1, 3⟩), Fraction.mul ⟨12582912, 125⟩ (Fraction.mul ⟨4312247, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_D_06_denominator_coefficient_0 : (Fraction.positive ⟨1936512, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_06_denominator_coefficient_1 : (Fraction.positive ⟨7587296, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_06_denominator_coefficient_2 : (Fraction.positive ⟨9907906, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_06_denominator_coefficient_3 : (Fraction.positive ⟨4312247, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_06_denominator_scale_positive : (Fraction.positive ⟨12582912, 125⟩) = true := by
  decide +kernel

theorem tail_ray_D_06_denominator_reconstruct : (Fraction.allEq (bernstein tail_ray_D_06_denominator_power ⟨4, 5⟩ ⟨13, 10⟩ 3) tail_ray_D_06_denominator_controls) = true := by
  decide +kernel

end F4Heavy.Finite
