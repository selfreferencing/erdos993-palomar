module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite

def tail_ray_H_08_numerator_power : List Fraction := [⟨-135507360, 1⟩, ⟨-283639728, 1⟩, ⟨14643, 1⟩, ⟨412172402, 1⟩, ⟨293431808, 1⟩]
def tail_ray_H_08_numerator_controls : List Fraction := [Fraction.mul ⟨1, 2592⟩ (Fraction.mul ⟨11221348206645, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨1, 2592⟩ (Fraction.mul ⟨59693451879591, 1⟩ ⟨1, 4⟩), Fraction.mul ⟨1, 2592⟩ (Fraction.mul ⟨118416419575794, 1⟩ ⟨1, 6⟩), Fraction.mul ⟨1, 2592⟩ (Fraction.mul ⟨103906733696736, 1⟩ ⟨1, 4⟩), Fraction.mul ⟨1, 2592⟩ (Fraction.mul ⟨34050484015264, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_H_08_numerator_coefficient_0 : (Fraction.positive ⟨11221348206645, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_08_numerator_coefficient_1 : (Fraction.positive ⟨59693451879591, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_08_numerator_coefficient_2 : (Fraction.positive ⟨118416419575794, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_08_numerator_coefficient_3 : (Fraction.positive ⟨103906733696736, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_08_numerator_coefficient_4 : (Fraction.positive ⟨34050484015264, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_08_numerator_scale_positive : (Fraction.positive ⟨1, 2592⟩) = true := by
  decide +kernel

theorem tail_ray_H_08_numerator_reconstruct : (Fraction.allEq (bernstein tail_ray_H_08_numerator_power ⟨7, 4⟩ ⟨7, 3⟩ 4) tail_ray_H_08_numerator_controls) = true := by
  decide +kernel

def tail_ray_H_08_denominator_power : List Fraction := [⟨0, 1⟩, ⟨201326592, 1⟩, ⟨503316480, 1⟩, ⟨314572800, 1⟩]
def tail_ray_H_08_denominator_controls : List Fraction := [Fraction.mul ⟨458752, 9⟩ (Fraction.mul ⟨70227, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨458752, 9⟩ (Fraction.mul ⟨266220, 1⟩ ⟨1, 3⟩), Fraction.mul ⟨458752, 9⟩ (Fraction.mul ⟨336144, 1⟩ ⟨1, 3⟩), Fraction.mul ⟨458752, 9⟩ (Fraction.mul ⟨141376, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_H_08_denominator_coefficient_0 : (Fraction.positive ⟨70227, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_08_denominator_coefficient_1 : (Fraction.positive ⟨266220, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_08_denominator_coefficient_2 : (Fraction.positive ⟨336144, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_08_denominator_coefficient_3 : (Fraction.positive ⟨141376, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_08_denominator_scale_positive : (Fraction.positive ⟨458752, 9⟩) = true := by
  decide +kernel

theorem tail_ray_H_08_denominator_reconstruct : (Fraction.allEq (bernstein tail_ray_H_08_denominator_power ⟨7, 4⟩ ⟨7, 3⟩ 3) tail_ray_H_08_denominator_controls) = true := by
  decide +kernel

end F4Heavy.Finite
