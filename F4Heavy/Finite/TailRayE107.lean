module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite

def tail_ray_E1_07_numerator_power : List Fraction := [⟨305604516095702477568, 1⟩, ⟨882931501614488899611, 1⟩, ⟨1134257734934113612995, 1⟩, ⟨743167483614736358440, 1⟩, ⟨133447295622229786880, 1⟩, ⟨-1148437914350000000, 1⟩, ⟨3116029630800000000, 1⟩]
def tail_ray_E1_07_numerator_controls : List Fraction := [Fraction.mul ⟨1, 2000⟩ (Fraction.mul ⟨10789930466084601797048996, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨1, 2000⟩ (Fraction.mul ⟨67387266672521019368331048, 1⟩ ⟨1, 6⟩), Fraction.mul ⟨1, 2000⟩ (Fraction.mul ⟨175334607752885148872664639, 1⟩ ⟨1, 15⟩), Fraction.mul ⟨1, 2000⟩ (Fraction.mul ⟨243274867179366445134016954, 1⟩ ⟨1, 20⟩), Fraction.mul ⟨1, 2000⟩ (Fraction.mul ⟨189840872290702432625110284, 1⟩ ⟨1, 15⟩), Fraction.mul ⟨1, 2000⟩ (Fraction.mul ⟨78998827005656232424010748, 1⟩ ⟨1, 6⟩), Fraction.mul ⟨1, 2000⟩ (Fraction.mul ⟨13695550418858563658197331, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_E1_07_numerator_coefficient_0 : (Fraction.positive ⟨10789930466084601797048996, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_07_numerator_coefficient_1 : (Fraction.positive ⟨67387266672521019368331048, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_07_numerator_coefficient_2 : (Fraction.positive ⟨175334607752885148872664639, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_07_numerator_coefficient_3 : (Fraction.positive ⟨243274867179366445134016954, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_07_numerator_coefficient_4 : (Fraction.positive ⟨189840872290702432625110284, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_07_numerator_coefficient_5 : (Fraction.positive ⟨78998827005656232424010748, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_07_numerator_coefficient_6 : (Fraction.positive ⟨13695550418858563658197331, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_07_numerator_scale_positive : (Fraction.positive ⟨1, 2000⟩) = true := by
  decide +kernel

theorem tail_ray_E1_07_numerator_reconstruct : (Fraction.allEq (bernstein tail_ray_E1_07_numerator_power ⟨13, 10⟩ ⟨29, 20⟩ 6) tail_ray_E1_07_numerator_controls) = true := by
  decide +kernel

def tail_ray_E1_07_denominator_power : List Fraction := [⟨690847009996800000000, 1⟩, ⟨2417964534988800000000, 1⟩, ⟨2806565978112000000000, 1⟩, ⟨1079448453120000000000, 1⟩]
def tail_ray_E1_07_denominator_controls : List Fraction := [Fraction.mul ⟨1214379509760000000, 1⟩ (Fraction.mul ⟨9016, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨1214379509760000000, 1⟩ (Fraction.mul ⟨28924, 1⟩ ⟨1, 3⟩), Fraction.mul ⟨1214379509760000000, 1⟩ (Fraction.mul ⟨30930, 1⟩ ⟨1, 3⟩), Fraction.mul ⟨1214379509760000000, 1⟩ (Fraction.mul ⟨11025, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_E1_07_denominator_coefficient_0 : (Fraction.positive ⟨9016, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_07_denominator_coefficient_1 : (Fraction.positive ⟨28924, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_07_denominator_coefficient_2 : (Fraction.positive ⟨30930, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_07_denominator_coefficient_3 : (Fraction.positive ⟨11025, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_07_denominator_scale_positive : (Fraction.positive ⟨1214379509760000000, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_07_denominator_reconstruct : (Fraction.allEq (bernstein tail_ray_E1_07_denominator_power ⟨13, 10⟩ ⟨29, 20⟩ 3) tail_ray_E1_07_denominator_controls) = true := by
  decide +kernel

end F4Heavy.Finite
