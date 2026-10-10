module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite

def tail_ray_D_08_numerator_power : List Fraction := [⟨-116530176, 1⟩, ⟨4435368576, 1⟩, ⟨12064677384, 1⟩, ⟨13780278511, 1⟩, ⟨7623349504, 1⟩]
def tail_ray_D_08_numerator_controls : List Fraction := [Fraction.mul ⟨1, 5000⟩ (Fraction.mul ⟨106655923825152, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨1, 5000⟩ (Fraction.mul ⟨591147712589888, 1⟩ ⟨1, 4⟩), Fraction.mul ⟨1, 5000⟩ (Fraction.mul ⟨1226521354700952, 1⟩ ⟨1, 6⟩), Fraction.mul ⟨1, 5000⟩ (Fraction.mul ⟨1130082640010223, 1⟩ ⟨1, 4⟩), Fraction.mul ⟨1, 5000⟩ (Fraction.mul ⟨390435370794007, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_D_08_numerator_coefficient_0 : (Fraction.positive ⟨106655923825152, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_08_numerator_coefficient_1 : (Fraction.positive ⟨591147712589888, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_08_numerator_coefficient_2 : (Fraction.positive ⟨1226521354700952, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_08_numerator_coefficient_3 : (Fraction.positive ⟨1130082640010223, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_08_numerator_coefficient_4 : (Fraction.positive ⟨390435370794007, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_08_numerator_scale_positive : (Fraction.positive ⟨1, 5000⟩) = true := by
  decide +kernel

theorem tail_ray_D_08_numerator_reconstruct : (Fraction.allEq (bernstein tail_ray_D_08_numerator_power ⟨4, 5⟩ ⟨13, 10⟩ 4) tail_ray_D_08_numerator_controls) = true := by
  decide +kernel

def tail_ray_D_08_denominator_power : List Fraction := [⟨0, 1⟩, ⟨8053063680, 1⟩, ⟨21139292160, 1⟩, ⟨13872660480, 1⟩]
def tail_ray_D_08_denominator_controls : List Fraction := [Fraction.mul ⟨786432, 25⟩ (Fraction.mul ⟨860672, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨786432, 25⟩ (Fraction.mul ⟨3670976, 1⟩ ⟨1, 3⟩), Fraction.mul ⟨786432, 25⟩ (Fraction.mul ⟨5192536, 1⟩ ⟨1, 3⟩), Fraction.mul ⟨786432, 25⟩ (Fraction.mul ⟨2437357, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_D_08_denominator_coefficient_0 : (Fraction.positive ⟨860672, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_08_denominator_coefficient_1 : (Fraction.positive ⟨3670976, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_08_denominator_coefficient_2 : (Fraction.positive ⟨5192536, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_08_denominator_coefficient_3 : (Fraction.positive ⟨2437357, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_08_denominator_scale_positive : (Fraction.positive ⟨786432, 25⟩) = true := by
  decide +kernel

theorem tail_ray_D_08_denominator_reconstruct : (Fraction.allEq (bernstein tail_ray_D_08_denominator_power ⟨4, 5⟩ ⟨13, 10⟩ 3) tail_ray_D_08_denominator_controls) = true := by
  decide +kernel

end F4Heavy.Finite
