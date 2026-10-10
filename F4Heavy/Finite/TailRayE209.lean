module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite

def tail_ray_E2_09_numerator_power : List Fraction := [⟨1525687693525699200000000, 1⟩, ⟨2527443382315958400000000, 1⟩, ⟨-1879699325581310950452885, 1⟩, ⟨127609281591449562560367, 1⟩, ⟨9412540993924142582637276, 1⟩, ⟨6425577965266685885249024, 1⟩, ⟨73484164425712000000000, 1⟩, ⟨32949254707200000000000, 1⟩]
def tail_ray_E2_09_numerator_controls : List Fraction := [Fraction.mul ⟨3, 200000⟩ (Fraction.mul ⟨5703259839709349206937534240102, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨3, 200000⟩ (Fraction.mul ⟨42519355903123238797313208455979, 1⟩ ⟨1, 7⟩), Fraction.mul ⟨3, 200000⟩ (Fraction.mul ⟨135831599867670023933636522202897, 1⟩ ⟨1, 21⟩), Fraction.mul ⟨3, 200000⟩ (Fraction.mul ⟨241026619387192236666263006470285, 1⟩ ⟨1, 35⟩), Fraction.mul ⟨3, 200000⟩ (Fraction.mul ⟨256565589348898810340553735446805, 1⟩ ⟨1, 35⟩), Fraction.mul ⟨3, 200000⟩ (Fraction.mul ⟨163831211618181958160956675823316, 1⟩ ⟨1, 21⟩), Fraction.mul ⟨3, 200000⟩ (Fraction.mul ⟨58107450250623866970005121228032, 1⟩ ⟨1, 7⟩), Fraction.mul ⟨3, 200000⟩ (Fraction.mul ⟨8830712402157742870592022368256, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_E2_09_numerator_coefficient_0 : (Fraction.positive ⟨5703259839709349206937534240102, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_09_numerator_coefficient_1 : (Fraction.positive ⟨42519355903123238797313208455979, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_09_numerator_coefficient_2 : (Fraction.positive ⟨135831599867670023933636522202897, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_09_numerator_coefficient_3 : (Fraction.positive ⟨241026619387192236666263006470285, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_09_numerator_coefficient_4 : (Fraction.positive ⟨256565589348898810340553735446805, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_09_numerator_coefficient_5 : (Fraction.positive ⟨163831211618181958160956675823316, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_09_numerator_coefficient_6 : (Fraction.positive ⟨58107450250623866970005121228032, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_09_numerator_coefficient_7 : (Fraction.positive ⟨8830712402157742870592022368256, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_09_numerator_scale_positive : (Fraction.positive ⟨3, 200000⟩) = true := by
  decide +kernel

theorem tail_ray_E2_09_numerator_reconstruct : (Fraction.allEq (bernstein tail_ray_E2_09_numerator_power ⟨29, 20⟩ ⟨8, 5⟩ 7) tail_ray_E2_09_numerator_controls) = true := by
  decide +kernel

def tail_ray_E2_09_denominator_power : List Fraction := [⟨0, 1⟩, ⟨12080979126937190400000000, 1⟩, ⟨45303671726014464000000000, 1⟩, ⟨56629589657518080000000000, 1⟩, ⟨23595662357299200000000000, 1⟩]
def tail_ray_E2_09_denominator_controls : List Fraction := [Fraction.mul ⟨3981768022794240000000, 1⟩ (Fraction.mul ⟨97875, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨3981768022794240000000, 1⟩ (Fraction.mul ⟨421200, 1⟩ ⟨1, 4⟩), Fraction.mul ⟨3981768022794240000000, 1⟩ (Fraction.mul ⟨679680, 1⟩ ⟨1, 6⟩), Fraction.mul ⟨3981768022794240000000, 1⟩ (Fraction.mul ⟨487424, 1⟩ ⟨1, 4⟩), Fraction.mul ⟨3981768022794240000000, 1⟩ (Fraction.mul ⟨131072, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_E2_09_denominator_coefficient_0 : (Fraction.positive ⟨97875, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_09_denominator_coefficient_1 : (Fraction.positive ⟨421200, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_09_denominator_coefficient_2 : (Fraction.positive ⟨679680, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_09_denominator_coefficient_3 : (Fraction.positive ⟨487424, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_09_denominator_coefficient_4 : (Fraction.positive ⟨131072, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_09_denominator_scale_positive : (Fraction.positive ⟨3981768022794240000000, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_09_denominator_reconstruct : (Fraction.allEq (bernstein tail_ray_E2_09_denominator_power ⟨29, 20⟩ ⟨8, 5⟩ 4) tail_ray_E2_09_denominator_controls) = true := by
  decide +kernel

end F4Heavy.Finite
