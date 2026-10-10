module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite

def tail_ray_D_04_numerator_power : List Fraction := [⟨-44625558640320000000, 1⟩, ⟨1794030533185089775761, 1⟩, ⟨1629622062223496257056, 1⟩, ⟨-455367143566625000000, 1⟩, ⟨67461026080000000000, 1⟩]
def tail_ray_D_04_numerator_controls : List Fraction := [Fraction.mul ⟨1, 50⟩ (Fraction.mul ⟨111402052325352271256232, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨1, 50⟩ (Fraction.mul ⟨537240236764074179701193, 1⟩ ⟨1, 4⟩), Fraction.mul ⟨1, 50⟩ (Fraction.mul ⟨953255787062743864779387, 1⟩ ⟨1, 6⟩), Fraction.mul ⟨1, 50⟩ (Fraction.mul ⟨738902249008982869230123, 1⟩ ⟨1, 4⟩), Fraction.mul ⟨1, 50⟩ (Fraction.mul ⟨211695462091460912895697, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_D_04_numerator_coefficient_0 : (Fraction.positive ⟨111402052325352271256232, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_04_numerator_coefficient_1 : (Fraction.positive ⟨537240236764074179701193, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_04_numerator_coefficient_2 : (Fraction.positive ⟨953255787062743864779387, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_04_numerator_coefficient_3 : (Fraction.positive ⟨738902249008982869230123, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_04_numerator_coefficient_4 : (Fraction.positive ⟨211695462091460912895697, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_04_numerator_scale_positive : (Fraction.positive ⟨1, 50⟩) = true := by
  decide +kernel

theorem tail_ray_D_04_numerator_reconstruct : (Fraction.allEq (bernstein tail_ray_D_04_numerator_power ⟨4, 5⟩ ⟨13, 10⟩ 4) tail_ray_D_04_numerator_controls) = true := by
  decide +kernel

def tail_ray_D_04_denominator_power : List Fraction := [⟨9868618833592320000000, 1⟩, ⟨12952562219089920000000, 1⟩]
def tail_ray_D_04_denominator_controls : List Fraction := [Fraction.mul ⟨61678867709952000000, 1⟩ (Fraction.mul ⟨328, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨61678867709952000000, 1⟩ (Fraction.mul ⟨433, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_D_04_denominator_coefficient_0 : (Fraction.positive ⟨328, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_04_denominator_coefficient_1 : (Fraction.positive ⟨433, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_04_denominator_scale_positive : (Fraction.positive ⟨61678867709952000000, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_04_denominator_reconstruct : (Fraction.allEq (bernstein tail_ray_D_04_denominator_power ⟨4, 5⟩ ⟨13, 10⟩ 1) tail_ray_D_04_denominator_controls) = true := by
  decide +kernel

end F4Heavy.Finite
