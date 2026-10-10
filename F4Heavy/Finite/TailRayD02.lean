module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite

def tail_ray_D_02_numerator_power : List Fraction := [⟨-284028487163, 1021207500000⟩, ⟨7525855, 9803592⟩, ⟨-1959725, 14705388⟩]
def tail_ray_D_02_numerator_controls : List Fraction := [Fraction.mul ⟨1, 9190867500000⟩ (Fraction.mul ⟨2304244865533, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨1, 9190867500000⟩ (Fraction.mul ⟨7156371762316, 1⟩ ⟨1, 2⟩), Fraction.mul ⟨1, 9190867500000⟩ (Fraction.mul ⟨4545919865533, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_D_02_numerator_coefficient_0 : (Fraction.positive ⟨2304244865533, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_02_numerator_coefficient_1 : (Fraction.positive ⟨7156371762316, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_02_numerator_coefficient_2 : (Fraction.positive ⟨4545919865533, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_02_numerator_scale_positive : (Fraction.positive ⟨1, 9190867500000⟩) = true := by
  decide +kernel

theorem tail_ray_D_02_numerator_reconstruct : (Fraction.allEq (bernstein tail_ray_D_02_numerator_power ⟨4, 5⟩ ⟨13, 10⟩ 2) tail_ray_D_02_numerator_controls) = true := by
  decide +kernel

def tail_ray_D_02_denominator_power : List Fraction := [⟨1, 1⟩]
def tail_ray_D_02_denominator_controls : List Fraction := [Fraction.mul ⟨1, 1⟩ (Fraction.mul ⟨1, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_D_02_denominator_coefficient_0 : (Fraction.positive ⟨1, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_02_denominator_scale_positive : (Fraction.positive ⟨1, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_02_denominator_reconstruct : (Fraction.allEq (bernstein tail_ray_D_02_denominator_power ⟨4, 5⟩ ⟨13, 10⟩ 0) tail_ray_D_02_denominator_controls) = true := by
  decide +kernel

end F4Heavy.Finite
