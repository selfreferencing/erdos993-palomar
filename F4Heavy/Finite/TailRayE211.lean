module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite

def tail_ray_E2_11_numerator_power : List Fraction := [⟨-63603648, 1⟩, ⟨-169119408, 1⟩, ⟨-102359394, 1⟩, ⟨85028067, 1⟩, ⟨119093200, 1⟩, ⟨35001344, 1⟩]
def tail_ray_E2_11_numerator_controls : List Fraction := [Fraction.mul ⟨3, 200000⟩ (Fraction.mul ⟨32398854471697, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨3, 200000⟩ (Fraction.mul ⟨184956804448030, 1⟩ ⟨1, 5⟩), Fraction.mul ⟨3, 200000⟩ (Fraction.mul ⟨420094072783605, 1⟩ ⟨1, 10⟩), Fraction.mul ⟨3, 200000⟩ (Fraction.mul ⟨474870062553640, 1⟩ ⟨1, 10⟩), Fraction.mul ⟨3, 200000⟩ (Fraction.mul ⟨267303435976960, 1⟩ ⟨1, 5⟩), Fraction.mul ⟨3, 200000⟩ (Fraction.mul ⟨59969673424896, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_E2_11_numerator_coefficient_0 : (Fraction.positive ⟨32398854471697, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_11_numerator_coefficient_1 : (Fraction.positive ⟨184956804448030, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_11_numerator_coefficient_2 : (Fraction.positive ⟨420094072783605, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_11_numerator_coefficient_3 : (Fraction.positive ⟨474870062553640, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_11_numerator_coefficient_4 : (Fraction.positive ⟨267303435976960, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_11_numerator_coefficient_5 : (Fraction.positive ⟨59969673424896, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_11_numerator_scale_positive : (Fraction.positive ⟨3, 200000⟩) = true := by
  decide +kernel

theorem tail_ray_E2_11_numerator_reconstruct : (Fraction.allEq (bernstein tail_ray_E2_11_numerator_power ⟨29, 20⟩ ⟨8, 5⟩ 5) tail_ray_E2_11_numerator_controls) = true := by
  decide +kernel

def tail_ray_E2_11_denominator_power : List Fraction := [⟨603979776, 1⟩, ⟨2365587456, 1⟩, ⟨3208642560, 1⟩, ⟨1651507200, 1⟩, ⟨196608000, 1⟩]
def tail_ray_E2_11_denominator_controls : List Fraction := [Fraction.mul ⟨165888, 5⟩ (Fraction.mul ⟨502875, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨165888, 5⟩ (Fraction.mul ⟨2122200, 1⟩ ⟨1, 4⟩), Fraction.mul ⟨165888, 5⟩ (Fraction.mul ⟨3358080, 1⟩ ⟨1, 6⟩), Fraction.mul ⟨165888, 5⟩ (Fraction.mul ⟨2361344, 1⟩ ⟨1, 4⟩), Fraction.mul ⟨165888, 5⟩ (Fraction.mul ⟨622592, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_E2_11_denominator_coefficient_0 : (Fraction.positive ⟨502875, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_11_denominator_coefficient_1 : (Fraction.positive ⟨2122200, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_11_denominator_coefficient_2 : (Fraction.positive ⟨3358080, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_11_denominator_coefficient_3 : (Fraction.positive ⟨2361344, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_11_denominator_coefficient_4 : (Fraction.positive ⟨622592, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_11_denominator_scale_positive : (Fraction.positive ⟨165888, 5⟩) = true := by
  decide +kernel

theorem tail_ray_E2_11_denominator_reconstruct : (Fraction.allEq (bernstein tail_ray_E2_11_denominator_power ⟨29, 20⟩ ⟨8, 5⟩ 4) tail_ray_E2_11_denominator_controls) = true := by
  decide +kernel

end F4Heavy.Finite
