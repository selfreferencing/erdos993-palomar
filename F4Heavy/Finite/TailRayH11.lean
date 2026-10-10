module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite

def tail_ray_H_11_numerator_power : List Fraction := [⟨18830386944, 1⟩, ⟨67157526720, 1⟩, ⟨69253607568, 1⟩, ⟨6006935724, 1⟩, ⟨-15939046937, 1⟩, ⟨-547296512, 1⟩]
def tail_ray_H_11_numerator_controls : List Fraction := [Fraction.mul ⟨1, 62208⟩ (Fraction.mul ⟨13820440407438933, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨1, 62208⟩ (Fraction.mul ⟨69006958486711605, 1⟩ ⟨1, 5⟩), Fraction.mul ⟨1, 62208⟩ (Fraction.mul ⟨133136376601416768, 1⟩ ⟨1, 10⟩), Fraction.mul ⟨1, 62208⟩ (Fraction.mul ⟨122061284858906784, 1⟩ ⟨1, 10⟩), Fraction.mul ⟨1, 62208⟩ (Fraction.mul ⟨51489768821338368, 1⟩ ⟨1, 5⟩), Fraction.mul ⟨1, 62208⟩ (Fraction.mul ⟨7376042881456384, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_H_11_numerator_coefficient_0 : (Fraction.positive ⟨13820440407438933, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_11_numerator_coefficient_1 : (Fraction.positive ⟨69006958486711605, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_11_numerator_coefficient_2 : (Fraction.positive ⟨133136376601416768, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_11_numerator_coefficient_3 : (Fraction.positive ⟨122061284858906784, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_11_numerator_coefficient_4 : (Fraction.positive ⟨51489768821338368, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_11_numerator_coefficient_5 : (Fraction.positive ⟨7376042881456384, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_11_numerator_scale_positive : (Fraction.positive ⟨1, 62208⟩) = true := by
  decide +kernel

theorem tail_ray_H_11_numerator_reconstruct : (Fraction.allEq (bernstein tail_ray_H_11_numerator_power ⟨7, 4⟩ ⟨7, 3⟩ 5) tail_ray_H_11_numerator_controls) = true := by
  decide +kernel

def tail_ray_H_11_denominator_power : List Fraction := [⟨19327352832, 1⟩, ⟨75698798592, 1⟩, ⟨102676561920, 1⟩, ⟨52848230400, 1⟩, ⟨6291456000, 1⟩]
def tail_ray_H_11_denominator_controls : List Fraction := [Fraction.mul ⟨65536, 27⟩ (Fraction.mul ⟨333086661, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨65536, 27⟩ (Fraction.mul ⟨1586006568, 1⟩ ⟨1, 4⟩), Fraction.mul ⟨65536, 27⟩ (Fraction.mul ⟨2828996928, 1⟩ ⟨1, 6⟩), Fraction.mul ⟨65536, 27⟩ (Fraction.mul ⟨2240244096, 1⟩ ⟨1, 4⟩), Fraction.mul ⟨65536, 27⟩ (Fraction.mul ⟨664467200, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_H_11_denominator_coefficient_0 : (Fraction.positive ⟨333086661, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_11_denominator_coefficient_1 : (Fraction.positive ⟨1586006568, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_11_denominator_coefficient_2 : (Fraction.positive ⟨2828996928, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_11_denominator_coefficient_3 : (Fraction.positive ⟨2240244096, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_11_denominator_coefficient_4 : (Fraction.positive ⟨664467200, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_11_denominator_scale_positive : (Fraction.positive ⟨65536, 27⟩) = true := by
  decide +kernel

theorem tail_ray_H_11_denominator_reconstruct : (Fraction.allEq (bernstein tail_ray_H_11_denominator_power ⟨7, 4⟩ ⟨7, 3⟩ 4) tail_ray_H_11_denominator_controls) = true := by
  decide +kernel

end F4Heavy.Finite
