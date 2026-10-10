module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite

def tail_ray_D_12_numerator_power : List Fraction := [⟨2758747584, 1⟩, ⟨6257403648, 1⟩, ⟨4603163399, 1⟩, ⟨1488968960, 1⟩]
def tail_ray_D_12_numerator_controls : List Fraction := [Fraction.mul ⟨1, 100⟩ (Fraction.mul ⟨1147304718528, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨1, 100⟩ (Fraction.mul ⟨4265978430064, 1⟩ ⟨1, 3⟩), Fraction.mul ⟨1, 100⟩ (Fraction.mul ⟨5294459927119, 1⟩ ⟨1, 3⟩), Fraction.mul ⟨1, 100⟩ (Fraction.mul ⟨2194398327583, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_D_12_numerator_coefficient_0 : (Fraction.positive ⟨1147304718528, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_12_numerator_coefficient_1 : (Fraction.positive ⟨4265978430064, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_12_numerator_coefficient_2 : (Fraction.positive ⟨5294459927119, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_12_numerator_coefficient_3 : (Fraction.positive ⟨2194398327583, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_12_numerator_scale_positive : (Fraction.positive ⟨1, 100⟩) = true := by
  decide +kernel

theorem tail_ray_D_12_numerator_reconstruct : (Fraction.allEq (bernstein tail_ray_D_12_numerator_power ⟨4, 5⟩ ⟨13, 10⟩ 3) tail_ray_D_12_numerator_controls) = true := by
  decide +kernel

def tail_ray_D_12_denominator_power : List Fraction := [⟨3221225472, 1⟩, ⟨8455716864, 1⟩, ⟨5549064192, 1⟩]
def tail_ray_D_12_denominator_controls : List Fraction := [Fraction.mul ⟨3145728, 25⟩ (Fraction.mul ⟨107584, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨3145728, 25⟩ (Fraction.mul ⟨284048, 1⟩ ⟨1, 2⟩), Fraction.mul ⟨3145728, 25⟩ (Fraction.mul ⟨187489, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_D_12_denominator_coefficient_0 : (Fraction.positive ⟨107584, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_12_denominator_coefficient_1 : (Fraction.positive ⟨284048, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_12_denominator_coefficient_2 : (Fraction.positive ⟨187489, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_12_denominator_scale_positive : (Fraction.positive ⟨3145728, 25⟩) = true := by
  decide +kernel

theorem tail_ray_D_12_denominator_reconstruct : (Fraction.allEq (bernstein tail_ray_D_12_denominator_power ⟨4, 5⟩ ⟨13, 10⟩ 2) tail_ray_D_12_denominator_controls) = true := by
  decide +kernel

end F4Heavy.Finite
