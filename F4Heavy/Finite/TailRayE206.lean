module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite

def tail_ray_E2_06_numerator_power : List Fraction := [⟨3299917248, 1⟩, ⟨11572928616, 1⟩, ⟨15066484865, 1⟩, ⟨8157131865, 1⟩, ⟨1203226240, 1⟩]
def tail_ray_E2_06_numerator_controls : List Fraction := [Fraction.mul ⟨3, 8000⟩ (Fraction.mul ⟨218519609109019, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨3, 8000⟩ (Fraction.mul ⟨922634270974743, 1⟩ ⟨1, 4⟩), Fraction.mul ⟨3, 8000⟩ (Fraction.mul ⟨1460728880719836, 1⟩ ⟨1, 6⟩), Fraction.mul ⟨3, 8000⟩ (Fraction.mul ⟨1027769607548032, 1⟩ ⟨1, 4⟩), Fraction.mul ⟨3, 8000⟩ (Fraction.mul ⟨271157013049344, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_E2_06_numerator_coefficient_0 : (Fraction.positive ⟨218519609109019, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_06_numerator_coefficient_1 : (Fraction.positive ⟨922634270974743, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_06_numerator_coefficient_2 : (Fraction.positive ⟨1460728880719836, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_06_numerator_coefficient_3 : (Fraction.positive ⟨1027769607548032, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_06_numerator_coefficient_4 : (Fraction.positive ⟨271157013049344, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_06_numerator_scale_positive : (Fraction.positive ⟨3, 8000⟩) = true := by
  decide +kernel

theorem tail_ray_E2_06_numerator_reconstruct : (Fraction.allEq (bernstein tail_ray_E2_06_numerator_power ⟨29, 20⟩ ⟨8, 5⟩ 4) tail_ray_E2_06_numerator_controls) = true := by
  decide +kernel

def tail_ray_E2_06_denominator_power : List Fraction := [⟨4026531840, 1⟩, ⟨14092861440, 1⟩, ⟨16357785600, 1⟩, ⟨6291456000, 1⟩]
def tail_ray_E2_06_denominator_controls : List Fraction := [Fraction.mul ⟨7077888, 1⟩ (Fraction.mul ⟨11025, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨7077888, 1⟩ (Fraction.mul ⟨35220, 1⟩ ⟨1, 3⟩), Fraction.mul ⟨7077888, 1⟩ (Fraction.mul ⟨37504, 1⟩ ⟨1, 3⟩), Fraction.mul ⟨7077888, 1⟩ (Fraction.mul ⟨13312, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_E2_06_denominator_coefficient_0 : (Fraction.positive ⟨11025, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_06_denominator_coefficient_1 : (Fraction.positive ⟨35220, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_06_denominator_coefficient_2 : (Fraction.positive ⟨37504, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_06_denominator_coefficient_3 : (Fraction.positive ⟨13312, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_06_denominator_scale_positive : (Fraction.positive ⟨7077888, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_06_denominator_reconstruct : (Fraction.allEq (bernstein tail_ray_E2_06_denominator_power ⟨29, 20⟩ ⟨8, 5⟩ 3) tail_ray_E2_06_denominator_controls) = true := by
  decide +kernel

end F4Heavy.Finite
