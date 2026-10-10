module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite

def tail_ray_E2_02_numerator_power : List Fraction := [⟨1334399627797179, 60006872450000000⟩, ⟨768588130, 1200137449⟩, ⟨-96159400, 1200137449⟩]
def tail_ray_E2_02_numerator_controls : List Fraction := [Fraction.mul ⟨3, 60006872450000000⟩ (Fraction.mul ⟨15649427375932393, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨3, 60006872450000000⟩ (Fraction.mul ⟨32523169426864786, 1⟩ ⟨1, 2⟩), Fraction.mul ⟨3, 60006872450000000⟩ (Fraction.mul ⟨16837682275932393, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_E2_02_numerator_coefficient_0 : (Fraction.positive ⟨15649427375932393, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_02_numerator_coefficient_1 : (Fraction.positive ⟨32523169426864786, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_02_numerator_coefficient_2 : (Fraction.positive ⟨16837682275932393, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_02_numerator_scale_positive : (Fraction.positive ⟨3, 60006872450000000⟩) = true := by
  decide +kernel

theorem tail_ray_E2_02_numerator_reconstruct : (Fraction.allEq (bernstein tail_ray_E2_02_numerator_power ⟨29, 20⟩ ⟨8, 5⟩ 2) tail_ray_E2_02_numerator_controls) = true := by
  decide +kernel

def tail_ray_E2_02_denominator_power : List Fraction := [⟨1, 1⟩]
def tail_ray_E2_02_denominator_controls : List Fraction := [Fraction.mul ⟨1, 1⟩ (Fraction.mul ⟨1, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_E2_02_denominator_coefficient_0 : (Fraction.positive ⟨1, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_02_denominator_scale_positive : (Fraction.positive ⟨1, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_02_denominator_reconstruct : (Fraction.allEq (bernstein tail_ray_E2_02_denominator_power ⟨29, 20⟩ ⟨8, 5⟩ 0) tail_ray_E2_02_denominator_controls) = true := by
  decide +kernel

end F4Heavy.Finite
