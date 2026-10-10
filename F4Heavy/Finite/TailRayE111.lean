module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite

def tail_ray_E1_11_numerator_power : List Fraction := [⟨168572160, 1⟩, ⟨578716224, 1⟩, ⟨455753904, 1⟩, ⟨-214651932, 1⟩, ⟨-234646319, 1⟩, ⟨34057384, 1⟩]
def tail_ray_E1_11_numerator_controls : List Fraction := [Fraction.mul ⟨1, 800000⟩ (Fraction.mul ⟨540653108348176, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨1, 800000⟩ (Fraction.mul ⟨2595226625740880, 1⟩ ⟨1, 5⟩), Fraction.mul ⟨1, 800000⟩ (Fraction.mul ⟨4938151111060120, 1⟩ ⟨1, 10⟩), Fraction.mul ⟨1, 800000⟩ (Fraction.mul ⟨4647304706113600, 1⟩ ⟨1, 10⟩), Fraction.mul ⟨1, 800000⟩ (Fraction.mul ⟨2157791664573665, 1⟩ ⟨1, 5⟩), Fraction.mul ⟨1, 800000⟩ (Fraction.mul ⟨394066621113559, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_E1_11_numerator_coefficient_0 : (Fraction.positive ⟨540653108348176, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_11_numerator_coefficient_1 : (Fraction.positive ⟨2595226625740880, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_11_numerator_coefficient_2 : (Fraction.positive ⟨4938151111060120, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_11_numerator_coefficient_3 : (Fraction.positive ⟨4647304706113600, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_11_numerator_coefficient_4 : (Fraction.positive ⟨2157791664573665, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_11_numerator_coefficient_5 : (Fraction.positive ⟨394066621113559, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_11_numerator_scale_positive : (Fraction.positive ⟨1, 800000⟩) = true := by
  decide +kernel

theorem tail_ray_E1_11_numerator_reconstruct : (Fraction.allEq (bernstein tail_ray_E1_11_numerator_power ⟨13, 10⟩ ⟨29, 20⟩ 5) tail_ray_E1_11_numerator_controls) = true := by
  decide +kernel

def tail_ray_E1_11_denominator_power : List Fraction := [⟨603979776, 1⟩, ⟨2365587456, 1⟩, ⟨3208642560, 1⟩, ⟨1651507200, 1⟩, ⟨196608000, 1⟩]
def tail_ray_E1_11_denominator_controls : List Fraction := [Fraction.mul ⟨165888, 5⟩ (Fraction.mul ⟨400624, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨165888, 5⟩ (Fraction.mul ⟨1696576, 1⟩ ⟨1, 4⟩), Fraction.mul ⟨165888, 5⟩ (Fraction.mul ⟨2693880, 1⟩ ⟨1, 6⟩), Fraction.mul ⟨165888, 5⟩ (Fraction.mul ⟨1900800, 1⟩ ⟨1, 4⟩), Fraction.mul ⟨165888, 5⟩ (Fraction.mul ⟨502875, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_E1_11_denominator_coefficient_0 : (Fraction.positive ⟨400624, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_11_denominator_coefficient_1 : (Fraction.positive ⟨1696576, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_11_denominator_coefficient_2 : (Fraction.positive ⟨2693880, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_11_denominator_coefficient_3 : (Fraction.positive ⟨1900800, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_11_denominator_coefficient_4 : (Fraction.positive ⟨502875, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_11_denominator_scale_positive : (Fraction.positive ⟨165888, 5⟩) = true := by
  decide +kernel

theorem tail_ray_E1_11_denominator_reconstruct : (Fraction.allEq (bernstein tail_ray_E1_11_denominator_power ⟨13, 10⟩ ⟨29, 20⟩ 4) tail_ray_E1_11_denominator_controls) = true := by
  decide +kernel

end F4Heavy.Finite
