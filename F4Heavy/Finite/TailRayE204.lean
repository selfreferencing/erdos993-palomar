module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite

def tail_ray_E2_04_numerator_power : List Fraction := [⟨63570320563570800000000, 1⟩, ⟨391814029102941498570361, 1⟩, ⟨212546220958630971312256, 1⟩, ⟨-68458129955972000000000, 1⟩, ⟨8237313676800000000000, 1⟩]
def tail_ray_E2_04_numerator_controls : List Fraction := [Fraction.mul ⟨3, 100⟩ (Fraction.mul ⟨30209634082761244387034723, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨3, 100⟩ (Fraction.mul ⟨124222778015132055175018409, 1⟩ ⟨1, 4⟩), Fraction.mul ⟨3, 100⟩ (Fraction.mul ⟨191424529849590937781331081, 1⟩ ⟨1, 6⟩), Fraction.mul ⟨3, 100⟩ (Fraction.mul ⟨131016935292384752735745827, 1⟩ ⟨1, 4⟩), Fraction.mul ⟨3, 100⟩ (Fraction.mul ⟨33605688379832921742398432, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_E2_04_numerator_coefficient_0 : (Fraction.positive ⟨30209634082761244387034723, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_04_numerator_coefficient_1 : (Fraction.positive ⟨124222778015132055175018409, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_04_numerator_coefficient_2 : (Fraction.positive ⟨191424529849590937781331081, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_04_numerator_coefficient_3 : (Fraction.positive ⟨131016935292384752735745827, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_04_numerator_coefficient_4 : (Fraction.positive ⟨33605688379832921742398432, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_04_numerator_scale_positive : (Fraction.positive ⟨3, 100⟩) = true := by
  decide +kernel

theorem tail_ray_E2_04_numerator_reconstruct : (Fraction.allEq (bernstein tail_ray_E2_04_numerator_power ⟨29, 20⟩ ⟨8, 5⟩ 4) tail_ray_E2_04_numerator_controls) = true := by
  decide +kernel

def tail_ray_E2_04_denominator_power : List Fraction := [⟨2013496521156198400000000, 1⟩, ⟨2516870651445248000000000, 1⟩]
def tail_ray_E2_04_denominator_controls : List Fraction := [Fraction.mul ⟨377530597716787200000000, 1⟩ (Fraction.mul ⟨15, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨377530597716787200000000, 1⟩ (Fraction.mul ⟨16, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_E2_04_denominator_coefficient_0 : (Fraction.positive ⟨15, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_04_denominator_coefficient_1 : (Fraction.positive ⟨16, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_04_denominator_scale_positive : (Fraction.positive ⟨377530597716787200000000, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_04_denominator_reconstruct : (Fraction.allEq (bernstein tail_ray_E2_04_denominator_power ⟨29, 20⟩ ⟨8, 5⟩ 1) tail_ray_E2_04_denominator_controls) = true := by
  decide +kernel

end F4Heavy.Finite
