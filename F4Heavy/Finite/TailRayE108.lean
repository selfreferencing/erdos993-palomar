module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite

def tail_ray_E1_08_numerator_power : List Fraction := [⟨-7483680, 1⟩, ⟨-16628976, 1⟩, ⟨173721, 1⟩, ⟨23067338, 1⟩, ⟨14288144, 1⟩]
def tail_ray_E1_08_numerator_controls : List Fraction := [Fraction.mul ⟨1, 20000⟩ (Fraction.mul ⟨1253590987088, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨1, 20000⟩ (Fraction.mul ⟨5693378883548, 1⟩ ⟨1, 4⟩), Fraction.mul ⟨1, 20000⟩ (Fraction.mul ⟨9664348881828, 1⟩ ⟨1, 6⟩), Fraction.mul ⟨1, 20000⟩ (Fraction.mul ⟨7269497245223, 1⟩ ⟨1, 4⟩), Fraction.mul ⟨1, 20000⟩ (Fraction.mul ⟨2045080927313, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_E1_08_numerator_coefficient_0 : (Fraction.positive ⟨1253590987088, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_08_numerator_coefficient_1 : (Fraction.positive ⟨5693378883548, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_08_numerator_coefficient_2 : (Fraction.positive ⟨9664348881828, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_08_numerator_coefficient_3 : (Fraction.positive ⟨7269497245223, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_08_numerator_coefficient_4 : (Fraction.positive ⟨2045080927313, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_08_numerator_scale_positive : (Fraction.positive ⟨1, 20000⟩) = true := by
  decide +kernel

theorem tail_ray_E1_08_numerator_reconstruct : (Fraction.allEq (bernstein tail_ray_E1_08_numerator_power ⟨13, 10⟩ ⟨29, 20⟩ 4) tail_ray_E1_08_numerator_controls) = true := by
  decide +kernel

def tail_ray_E1_08_denominator_power : List Fraction := [⟨0, 1⟩, ⟨6291456, 1⟩, ⟨15728640, 1⟩, ⟨9830400, 1⟩]
def tail_ray_E1_08_denominator_controls : List Fraction := [Fraction.mul ⟨55296, 5⟩ (Fraction.mul ⟨5096, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨55296, 5⟩ (Fraction.mul ⟨16604, 1⟩ ⟨1, 3⟩), Fraction.mul ⟨55296, 5⟩ (Fraction.mul ⟨18030, 1⟩ ⟨1, 3⟩), Fraction.mul ⟨55296, 5⟩ (Fraction.mul ⟨6525, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_E1_08_denominator_coefficient_0 : (Fraction.positive ⟨5096, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_08_denominator_coefficient_1 : (Fraction.positive ⟨16604, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_08_denominator_coefficient_2 : (Fraction.positive ⟨18030, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_08_denominator_coefficient_3 : (Fraction.positive ⟨6525, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_08_denominator_scale_positive : (Fraction.positive ⟨55296, 5⟩) = true := by
  decide +kernel

theorem tail_ray_E1_08_denominator_reconstruct : (Fraction.allEq (bernstein tail_ray_E1_08_denominator_power ⟨13, 10⟩ ⟨29, 20⟩ 3) tail_ray_E1_08_denominator_controls) = true := by
  decide +kernel

end F4Heavy.Finite
