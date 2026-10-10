module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite

def tail_ray_H_04_numerator_power : List Fraction := [⟨-324384756154866000000000, 1⟩, ⟨-198346877632341015911221, 1⟩, ⟨437263657196977503706112, 1⟩, ⟨-9312510672250800000000, 1⟩, ⟨1573121758924800000000, 1⟩]
def tail_ray_H_04_numerator_controls : List Fraction := [Fraction.mul ⟨1, 36⟩ (Fraction.mul ⟨22769030979611189856191925, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨1, 36⟩ (Fraction.mul ⟨117961185516162014288031291, 1⟩ ⟨1, 4⟩), Fraction.mul ⟨1, 36⟩ (Fraction.mul ⟨222381039504795727772342195, 1⟩ ⟨1, 6⟩), Fraction.mul ⟨1, 36⟩ (Fraction.mul ⟨181966789591687597530358217, 1⟩ ⟨1, 4⟩), Fraction.mul ⟨1, 36⟩ (Fraction.mul ⟨54784462028552378989855388, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_H_04_numerator_coefficient_0 : (Fraction.positive ⟨22769030979611189856191925, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_04_numerator_coefficient_1 : (Fraction.positive ⟨117961185516162014288031291, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_04_numerator_coefficient_2 : (Fraction.positive ⟨222381039504795727772342195, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_04_numerator_coefficient_3 : (Fraction.positive ⟨181966789591687597530358217, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_04_numerator_coefficient_4 : (Fraction.positive ⟨54784462028552378989855388, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_04_numerator_scale_positive : (Fraction.positive ⟨1, 36⟩) = true := by
  decide +kernel

theorem tail_ray_H_04_numerator_reconstruct : (Fraction.allEq (bernstein tail_ray_H_04_numerator_power ⟨7, 4⟩ ⟨7, 3⟩ 4) tail_ray_H_04_numerator_controls) = true := by
  decide +kernel

def tail_ray_H_04_denominator_power : List Fraction := [⟨1927785397144780800000000, 1⟩, ⟨2409731746430976000000000, 1⟩]
def tail_ray_H_04_denominator_controls : List Fraction := [Fraction.mul ⟨40162195773849600000000, 1⟩ (Fraction.mul ⟨153, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨40162195773849600000000, 1⟩ (Fraction.mul ⟨188, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_H_04_denominator_coefficient_0 : (Fraction.positive ⟨153, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_04_denominator_coefficient_1 : (Fraction.positive ⟨188, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_04_denominator_scale_positive : (Fraction.positive ⟨40162195773849600000000, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_04_denominator_reconstruct : (Fraction.allEq (bernstein tail_ray_H_04_denominator_power ⟨7, 4⟩ ⟨7, 3⟩ 1) tail_ray_H_04_denominator_controls) = true := by
  decide +kernel

end F4Heavy.Finite
