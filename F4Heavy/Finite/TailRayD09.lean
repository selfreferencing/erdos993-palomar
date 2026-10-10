module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite

def tail_ray_D_09_numerator_power : List Fraction := [⟨-3427242903576576000000, 1⟩, ⟨-64000099794438144000000, 1⟩, ⟨-141967607102015973351732, 1⟩, ⟨24277999376943348428493, 1⟩, ⟨252460666650256281806427, 1⟩, ⟨147957128669970055369952, 1⟩, ⟨4384944502567375000000, 1⟩, ⟨1146837443360000000000, 1⟩]
def tail_ray_D_09_numerator_controls : List Fraction := [Fraction.mul ⟨1, 50000⟩ (Fraction.mul ⟨1011211075729059702290915328, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨1, 50000⟩ (Fraction.mul ⟨21734646030922514857965396096, 1⟩ ⟨1, 7⟩), Fraction.mul ⟨1, 50000⟩ (Fraction.mul ⟨130148966829173549416026718688, 1⟩ ⟨1, 21⟩), Fraction.mul ⟨1, 50000⟩ (Fraction.mul ⟨371620160391546305569439389730, 1⟩ ⟨1, 35⟩), Fraction.mul ⟨1, 50000⟩ (Fraction.mul ⟨587125681165944793519385741855, 1⟩ ⟨1, 35⟩), Fraction.mul ⟨1, 50000⟩ (Fraction.mul ⟨528649645250391215704431904513, 1⟩ ⟨1, 21⟩), Fraction.mul ⟨1, 50000⟩ (Fraction.mul ⟨254995896230404528041805268221, 1⟩ ⟨1, 7⟩), Fraction.mul ⟨1, 50000⟩ (Fraction.mul ⟨51277751611768207047671953753, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_D_09_numerator_coefficient_0 : (Fraction.positive ⟨1011211075729059702290915328, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_09_numerator_coefficient_1 : (Fraction.positive ⟨21734646030922514857965396096, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_09_numerator_coefficient_2 : (Fraction.positive ⟨130148966829173549416026718688, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_09_numerator_coefficient_3 : (Fraction.positive ⟨371620160391546305569439389730, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_09_numerator_coefficient_4 : (Fraction.positive ⟨587125681165944793519385741855, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_09_numerator_coefficient_5 : (Fraction.positive ⟨528649645250391215704431904513, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_09_numerator_coefficient_6 : (Fraction.positive ⟨254995896230404528041805268221, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_09_numerator_coefficient_7 : (Fraction.positive ⟨51277751611768207047671953753, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_09_numerator_scale_positive : (Fraction.positive ⟨1, 50000⟩) = true := by
  decide +kernel

theorem tail_ray_D_09_numerator_reconstruct : (Fraction.allEq (bernstein tail_ray_D_09_numerator_power ⟨4, 5⟩ ⟨13, 10⟩ 7) tail_ray_D_09_numerator_controls) = true := by
  decide +kernel

def tail_ray_D_09_denominator_power : List Fraction := [⟨0, 1⟩, ⟨236846852006215680000000, 1⟩, ⟨932584479774474240000000, 1⟩, ⟨1224017129703997440000000, 1⟩, ⟨535507494245498880000000, 1⟩]
def tail_ray_D_09_denominator_controls : List Fraction := [Fraction.mul ⟨5782393847808000, 1⟩ (Fraction.mul ⟨282300416, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨5782393847808000, 1⟩ (Fraction.mul ⟨1576751104, 1⟩ ⟨1, 4⟩), Fraction.mul ⟨5782393847808000, 1⟩ (Fraction.mul ⟨3292684416, 1⟩ ⟨1, 6⟩), Fraction.mul ⟨5782393847808000, 1⟩ (Fraction.mul ⟨3047821184, 1⟩ ⟨1, 4⟩), Fraction.mul ⟨5782393847808000, 1⟩ (Fraction.mul ⟨1055375581, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_D_09_denominator_coefficient_0 : (Fraction.positive ⟨282300416, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_09_denominator_coefficient_1 : (Fraction.positive ⟨1576751104, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_09_denominator_coefficient_2 : (Fraction.positive ⟨3292684416, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_09_denominator_coefficient_3 : (Fraction.positive ⟨3047821184, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_09_denominator_coefficient_4 : (Fraction.positive ⟨1055375581, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_09_denominator_scale_positive : (Fraction.positive ⟨5782393847808000, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_09_denominator_reconstruct : (Fraction.allEq (bernstein tail_ray_D_09_denominator_power ⟨4, 5⟩ ⟨13, 10⟩ 4) tail_ray_D_09_denominator_controls) = true := by
  decide +kernel

end F4Heavy.Finite
