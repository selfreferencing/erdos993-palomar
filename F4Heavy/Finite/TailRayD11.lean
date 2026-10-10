module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite

def tail_ray_D_11_numerator_power : List Fraction := [⟨1007308800, 1⟩, ⟨7295619840, 1⟩, ⟨11945062800, 1⟩, ⟨5914640745, 1⟩, ⟨-1257261500, 1⟩, ⟨-2531087360, 1⟩]
def tail_ray_D_11_numerator_controls : List Fraction := [Fraction.mul ⟨1, 5000⟩ (Fraction.mul ⟨80862899544576, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨1, 5000⟩ (Fraction.mul ⟨479327727935680, 1⟩ ⟨1, 5⟩), Fraction.mul ⟨1, 5000⟩ (Fraction.mul ⟨1119123352727960, 1⟩ ⟨1, 10⟩), Fraction.mul ⟨1, 5000⟩ (Fraction.mul ⟨1281090464041185, 1⟩ ⟨1, 10⟩), Fraction.mul ⟨1, 5000⟩ (Fraction.mul ⟨714250530499580, 1⟩ ⟨1, 5⟩), Fraction.mul ⟨1, 5000⟩ (Fraction.mul ⟨153423108395251, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_D_11_numerator_coefficient_0 : (Fraction.positive ⟨80862899544576, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_11_numerator_coefficient_1 : (Fraction.positive ⟨479327727935680, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_11_numerator_coefficient_2 : (Fraction.positive ⟨1119123352727960, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_11_numerator_coefficient_3 : (Fraction.positive ⟨1281090464041185, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_11_numerator_coefficient_4 : (Fraction.positive ⟨714250530499580, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_11_numerator_coefficient_5 : (Fraction.positive ⟨153423108395251, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_11_numerator_scale_positive : (Fraction.positive ⟨1, 5000⟩) = true := by
  decide +kernel

theorem tail_ray_D_11_numerator_reconstruct : (Fraction.allEq (bernstein tail_ray_D_11_numerator_power ⟨4, 5⟩ ⟨13, 10⟩ 5) tail_ray_D_11_numerator_controls) = true := by
  decide +kernel

def tail_ray_D_11_denominator_power : List Fraction := [⟨77309411328, 1⟩, ⟨317290708992, 1⟩, ⟨450266923008, 1⟩, ⟨241384292352, 1⟩, ⟨29132587008, 1⟩]
def tail_ray_D_11_denominator_controls : List Fraction := [Fraction.mul ⟨196608, 625⟩ (Fraction.mul ⟨2399553536, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨196608, 625⟩ (Fraction.mul ⟨12079101184, 1⟩ ⟨1, 4⟩), Fraction.mul ⟨196608, 625⟩ (Fraction.mul ⟨22747131936, 1⟩ ⟨1, 6⟩), Fraction.mul ⟨196608, 625⟩ (Fraction.mul ⟨18988135964, 1⟩ ⟨1, 4⟩), Fraction.mul ⟨196608, 625⟩ (Fraction.mul ⟨5926339801, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_D_11_denominator_coefficient_0 : (Fraction.positive ⟨2399553536, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_11_denominator_coefficient_1 : (Fraction.positive ⟨12079101184, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_11_denominator_coefficient_2 : (Fraction.positive ⟨22747131936, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_11_denominator_coefficient_3 : (Fraction.positive ⟨18988135964, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_11_denominator_coefficient_4 : (Fraction.positive ⟨5926339801, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_11_denominator_scale_positive : (Fraction.positive ⟨196608, 625⟩) = true := by
  decide +kernel

theorem tail_ray_D_11_denominator_reconstruct : (Fraction.allEq (bernstein tail_ray_D_11_denominator_power ⟨4, 5⟩ ⟨13, 10⟩ 4) tail_ray_D_11_denominator_controls) = true := by
  decide +kernel

end F4Heavy.Finite
