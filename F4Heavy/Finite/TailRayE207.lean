module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite

def tail_ray_E2_07_numerator_power : List Fraction := [⟨34773681442739358602852352, 1⟩, ⟨96809918439171306707005719, 1⟩, ⟨106921143745805894819932715, 1⟩, ⟨54257083052762989491311380, 1⟩, ⟨5186432140422791426245120, 1⟩, ⟨367420822128560000000000, 1⟩, ⟨164746273536000000000000, 1⟩]
def tail_ray_E2_07_numerator_controls : List Fraction := [Fraction.mul ⟨9, 2000⟩ (Fraction.mul ⟨131593814197623557368245844596, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨9, 2000⟩ (Fraction.mul ⟨817123236599195201742345175499, 1⟩ ⟨1, 6⟩), Fraction.mul ⟨9, 2000⟩ (Fraction.mul ⟨2113861427574086781634284305589, 1⟩ ⟨1, 15⟩), Fraction.mul ⟨9, 2000⟩ (Fraction.mul ⟨2916166209560177987913925009093, 1⟩ ⟨1, 20⟩), Fraction.mul ⟨9, 2000⟩ (Fraction.mul ⟨2262656683929465961686618732371, 1⟩ ⟨1, 15⟩), Fraction.mul ⟨9, 2000⟩ (Fraction.mul ⟨936207182051549078589798849900, 1⟩ ⟨1, 6⟩), Fraction.mul ⟨9, 2000⟩ (Fraction.mul ⟨161384702926759972444920151936, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_E2_07_numerator_coefficient_0 : (Fraction.positive ⟨131593814197623557368245844596, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_07_numerator_coefficient_1 : (Fraction.positive ⟨817123236599195201742345175499, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_07_numerator_coefficient_2 : (Fraction.positive ⟨2113861427574086781634284305589, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_07_numerator_coefficient_3 : (Fraction.positive ⟨2916166209560177987913925009093, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_07_numerator_coefficient_4 : (Fraction.positive ⟨2262656683929465961686618732371, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_07_numerator_coefficient_5 : (Fraction.positive ⟨936207182051549078589798849900, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_07_numerator_coefficient_6 : (Fraction.positive ⟨161384702926759972444920151936, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_07_numerator_scale_positive : (Fraction.positive ⟨9, 2000⟩) = true := by
  decide +kernel

theorem tail_ray_E2_07_numerator_reconstruct : (Fraction.allEq (bernstein tail_ray_E2_07_numerator_power ⟨29, 20⟩ ⟨8, 5⟩ 6) tail_ray_E2_07_numerator_controls) = true := by
  decide +kernel

def tail_ray_E2_07_denominator_power : List Fraction := [⟨60404895634685952000000000, 1⟩, ⟨211417134721400832000000000, 1⟩, ⟨245394888515911680000000000, 1⟩, ⟨94382649429196800000000000, 1⟩]
def tail_ray_E2_07_denominator_controls : List Fraction := [Fraction.mul ⟨106180480607846400000000, 1⟩ (Fraction.mul ⟨11025, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨106180480607846400000000, 1⟩ (Fraction.mul ⟨35220, 1⟩ ⟨1, 3⟩), Fraction.mul ⟨106180480607846400000000, 1⟩ (Fraction.mul ⟨37504, 1⟩ ⟨1, 3⟩), Fraction.mul ⟨106180480607846400000000, 1⟩ (Fraction.mul ⟨13312, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_E2_07_denominator_coefficient_0 : (Fraction.positive ⟨11025, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_07_denominator_coefficient_1 : (Fraction.positive ⟨35220, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_07_denominator_coefficient_2 : (Fraction.positive ⟨37504, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_07_denominator_coefficient_3 : (Fraction.positive ⟨13312, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_07_denominator_scale_positive : (Fraction.positive ⟨106180480607846400000000, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_07_denominator_reconstruct : (Fraction.allEq (bernstein tail_ray_E2_07_denominator_power ⟨29, 20⟩ ⟨8, 5⟩ 3) tail_ray_E2_07_denominator_controls) = true := by
  decide +kernel

end F4Heavy.Finite
