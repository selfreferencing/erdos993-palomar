module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite

def tail_ray_E2_05_numerator_power : List Fraction := [⟨51018638443453967217254400000000, 1⟩, ⟨326841738118120308310663752093008, 1⟩, ⟨1058560781617744175824208413420024, 1⟩, ⟨1863864803732525380038243462985981, 1⟩, ⟨1577535287740483852699915949244245, 1⟩, ⟨395296089650321762529490197011200, 1⟩, ⟨-146169917283015988058438510397440, 1⟩, ⟨-37179147196760688542720000000000, 1⟩, ⟨10659663077506080768000000000000, 1⟩]
def tail_ray_E2_05_numerator_controls : List Fraction := [Fraction.mul ⟨9, 800000⟩ (Fraction.mul ⟨1447890769626927353603039011231995975733, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨9, 800000⟩ (Fraction.mul ⟨12066275992546291946326972507156839986200, 1⟩ ⟨1, 8⟩), Fraction.mul ⟨9, 800000⟩ (Fraction.mul ⟨43981381283202301827698823012135131153806, 1⟩ ⟨1, 28⟩), Fraction.mul ⟨9, 800000⟩ (Fraction.mul ⟨91580920840513382670393645557766588405164, 1⟩ ⟨1, 56⟩), Fraction.mul ⟨9, 800000⟩ (Fraction.mul ⟨119151153244361005744613323701094672162565, 1⟩ ⟨1, 70⟩), Fraction.mul ⟨9, 800000⟩ (Fraction.mul ⟨99185248884271359292014145681704709534724, 1⟩ ⟨1, 56⟩), Fraction.mul ⟨9, 800000⟩ (Fraction.mul ⟨51588170742961563011977008590660172985600, 1⟩ ⟨1, 28⟩), Fraction.mul ⟨9, 800000⟩ (Fraction.mul ⟨15328085529524422391413397984919238816768, 1⟩ ⟨1, 8⟩), Fraction.mul ⟨9, 800000⟩ (Fraction.mul ⟨1991935206946498811740402818921404465152, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_E2_05_numerator_coefficient_0 : (Fraction.positive ⟨1447890769626927353603039011231995975733, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_05_numerator_coefficient_1 : (Fraction.positive ⟨12066275992546291946326972507156839986200, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_05_numerator_coefficient_2 : (Fraction.positive ⟨43981381283202301827698823012135131153806, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_05_numerator_coefficient_3 : (Fraction.positive ⟨91580920840513382670393645557766588405164, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_05_numerator_coefficient_4 : (Fraction.positive ⟨119151153244361005744613323701094672162565, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_05_numerator_coefficient_5 : (Fraction.positive ⟨99185248884271359292014145681704709534724, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_05_numerator_coefficient_6 : (Fraction.positive ⟨51588170742961563011977008590660172985600, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_05_numerator_coefficient_7 : (Fraction.positive ⟨15328085529524422391413397984919238816768, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_05_numerator_coefficient_8 : (Fraction.positive ⟨1991935206946498811740402818921404465152, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_05_numerator_scale_positive : (Fraction.positive ⟨9, 800000⟩) = true := by
  decide +kernel

theorem tail_ray_E2_05_numerator_reconstruct : (Fraction.allEq (bernstein tail_ray_E2_05_numerator_power ⟨29, 20⟩ ⟨8, 5⟩ 8) tail_ray_E2_05_numerator_controls) = true := by
  decide +kernel

def tail_ray_E2_05_denominator_power : List Fraction := [⟨2702469284054888823652352000000000, 1⟩, ⟨12836729099260721912348672000000000, 1⟩, ⟨22802084584213124449566720000000000, 1⟩, ⟨17946085089426996094566400000000000, 1⟩, ⟨5278260320419704733696000000000000, 1⟩]
def tail_ray_E2_05_denominator_controls : List Fraction := [Fraction.mul ⟨890706429070825173811200000000, 1⟩ (Fraction.mul ⟨165375, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨890706429070825173811200000000, 1⟩ (Fraction.mul ⟨704700, 1⟩ ⟨1, 4⟩), Fraction.mul ⟨890706429070825173811200000000, 1⟩ (Fraction.mul ⟨1126080, 1⟩ ⟨1, 6⟩), Fraction.mul ⟨890706429070825173811200000000, 1⟩ (Fraction.mul ⟨799744, 1⟩ ⟨1, 4⟩), Fraction.mul ⟨890706429070825173811200000000, 1⟩ (Fraction.mul ⟨212992, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_E2_05_denominator_coefficient_0 : (Fraction.positive ⟨165375, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_05_denominator_coefficient_1 : (Fraction.positive ⟨704700, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_05_denominator_coefficient_2 : (Fraction.positive ⟨1126080, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_05_denominator_coefficient_3 : (Fraction.positive ⟨799744, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_05_denominator_coefficient_4 : (Fraction.positive ⟨212992, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_05_denominator_scale_positive : (Fraction.positive ⟨890706429070825173811200000000, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_05_denominator_reconstruct : (Fraction.allEq (bernstein tail_ray_E2_05_denominator_power ⟨29, 20⟩ ⟨8, 5⟩ 4) tail_ray_E2_05_denominator_controls) = true := by
  decide +kernel

end F4Heavy.Finite
