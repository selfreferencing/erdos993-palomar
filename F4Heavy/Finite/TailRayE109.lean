module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite

def tail_ray_E1_09_numerator_power : List Fraction := [⟨-164352351880800000000, 1⟩, ⟨-686999630122020000000, 1⟩, ⟨-884775664850543830497, 1⟩, ⟨-78554266328590766185, 1⟩, ⟨580869745516674256063, 1⟩, ⟨296019615514105332376, 1⟩, ⟨-229687582870000000, 1⟩, ⟨623205926160000000, 1⟩]
def tail_ray_E1_09_numerator_controls : List Fraction := [Fraction.mul ⟨9, 800000⟩ (Fraction.mul ⟨3166008010065018335464976, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨9, 800000⟩ (Fraction.mul ⟨101658652633663519373680992, 1⟩ ⟨1, 7⟩), Fraction.mul ⟨9, 800000⟩ (Fraction.mul ⟨565948117646292052017243536, 1⟩ ⟨1, 21⟩), Fraction.mul ⟨9, 800000⟩ (Fraction.mul ⟨1418070150664509576075026060, 1⟩ ⟨1, 35⟩), Fraction.mul ⟨9, 800000⟩ (Fraction.mul ⟨1935276817839974640352757375, 1⟩ ⟨1, 35⟩), Fraction.mul ⟨9, 800000⟩ (Fraction.mul ⟨1498499240035206717399794279, 1⟩ ⟨1, 21⟩), Fraction.mul ⟨9, 800000⟩ (Fraction.mul ⟨621497906218098470349859113, 1⟩ ⟨1, 7⟩), Fraction.mul ⟨9, 800000⟩ (Fraction.mul ⟨107660806475699768242373669, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_E1_09_numerator_coefficient_0 : (Fraction.positive ⟨3166008010065018335464976, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_09_numerator_coefficient_1 : (Fraction.positive ⟨101658652633663519373680992, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_09_numerator_coefficient_2 : (Fraction.positive ⟨565948117646292052017243536, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_09_numerator_coefficient_3 : (Fraction.positive ⟨1418070150664509576075026060, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_09_numerator_coefficient_4 : (Fraction.positive ⟨1935276817839974640352757375, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_09_numerator_coefficient_5 : (Fraction.positive ⟨1498499240035206717399794279, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_09_numerator_coefficient_6 : (Fraction.positive ⟨621497906218098470349859113, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_09_numerator_coefficient_7 : (Fraction.positive ⟨107660806475699768242373669, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_09_numerator_scale_positive : (Fraction.positive ⟨9, 800000⟩) = true := by
  decide +kernel

theorem tail_ray_E1_09_numerator_reconstruct : (Fraction.allEq (bernstein tail_ray_E1_09_numerator_power ⟨13, 10⟩ ⟨29, 20⟩ 7) tail_ray_E1_09_numerator_controls) = true := by
  decide +kernel

def tail_ray_E1_09_denominator_power : List Fraction := [⟨0, 1⟩, ⟨138169401999360000000, 1⟩, ⟨518135257497600000000, 1⟩, ⟨647669071872000000000, 1⟩, ⟨269862113280000000000, 1⟩]
def tail_ray_E1_09_denominator_controls : List Fraction := [Fraction.mul ⟨45539231616000000, 1⟩ (Fraction.mul ⟨71344, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨45539231616000000, 1⟩ (Fraction.mul ⟨308896, 1⟩ ⟨1, 4⟩), Fraction.mul ⟨45539231616000000, 1⟩ (Fraction.mul ⟨501480, 1⟩ ⟨1, 6⟩), Fraction.mul ⟨45539231616000000, 1⟩ (Fraction.mul ⟨361800, 1⟩ ⟨1, 4⟩), Fraction.mul ⟨45539231616000000, 1⟩ (Fraction.mul ⟨97875, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_E1_09_denominator_coefficient_0 : (Fraction.positive ⟨71344, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_09_denominator_coefficient_1 : (Fraction.positive ⟨308896, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_09_denominator_coefficient_2 : (Fraction.positive ⟨501480, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_09_denominator_coefficient_3 : (Fraction.positive ⟨361800, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_09_denominator_coefficient_4 : (Fraction.positive ⟨97875, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_09_denominator_scale_positive : (Fraction.positive ⟨45539231616000000, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_09_denominator_reconstruct : (Fraction.allEq (bernstein tail_ray_E1_09_denominator_power ⟨13, 10⟩ ⟨29, 20⟩ 4) tail_ray_E1_09_denominator_controls) = true := by
  decide +kernel

end F4Heavy.Finite
