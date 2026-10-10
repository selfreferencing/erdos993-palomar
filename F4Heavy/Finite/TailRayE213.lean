module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite

def tail_ray_E2_13_numerator_power : List Fraction := [⟨-59030946023376122880000000, 1⟩, ⟨-155272293060963321600000000, 1⟩, ⟨-91168415111885830551737664, 1⟩, ⟨87237969405790196516232072, 1⟩, ⟨120508148457254023887257125, 1⟩, ⟨29584824985284243282996864, 1⟩, ⟨-5390046289151668000000000, 1⟩, ⟨2215837379059200000000000, 1⟩]
def tail_ray_E2_13_numerator_controls : List Fraction := [Fraction.mul ⟨3, 800000⟩ (Fraction.mul ⟨131253953237325329150023597899203, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨3, 800000⟩ (Fraction.mul ⟨1006413515580574449589010979677001, 1⟩ ⟨1, 7⟩), Fraction.mul ⟨3, 800000⟩ (Fraction.mul ⟨3298055982962616375448748373935913, 1⟩ ⟨1, 21⟩), Fraction.mul ⟨3, 800000⟩ (Fraction.mul ⟨5989245696205387118465744700212995, 1⟩ ⟨1, 35⟩), Fraction.mul ⟨3, 800000⟩ (Fraction.mul ⟨6510859098379439805673497491453280, 1⟩ ⟨1, 35⟩), Fraction.mul ⟨3, 800000⟩ (Fraction.mul ⟨4237794862462564137694047453855744, 1⟩ ⟨1, 21⟩), Fraction.mul ⟨3, 800000⟩ (Fraction.mul ⟨1529418772560830539929596507291648, 1⟩ ⟨1, 7⟩), Fraction.mul ⟨3, 800000⟩ (Fraction.mul ⟨236133733901277250286910836834304, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_E2_13_numerator_coefficient_0 : (Fraction.positive ⟨131253953237325329150023597899203, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_13_numerator_coefficient_1 : (Fraction.positive ⟨1006413515580574449589010979677001, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_13_numerator_coefficient_2 : (Fraction.positive ⟨3298055982962616375448748373935913, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_13_numerator_coefficient_3 : (Fraction.positive ⟨5989245696205387118465744700212995, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_13_numerator_coefficient_4 : (Fraction.positive ⟨6510859098379439805673497491453280, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_13_numerator_coefficient_5 : (Fraction.positive ⟨4237794862462564137694047453855744, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_13_numerator_coefficient_6 : (Fraction.positive ⟨1529418772560830539929596507291648, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_13_numerator_coefficient_7 : (Fraction.positive ⟨236133733901277250286910836834304, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_13_numerator_scale_positive : (Fraction.positive ⟨3, 800000⟩) = true := by
  decide +kernel

theorem tail_ray_E2_13_numerator_reconstruct : (Fraction.allEq (bernstein tail_ray_E2_13_numerator_power ⟨29, 20⟩ ⟨8, 5⟩ 7) tail_ray_E2_13_numerator_controls) = true := by
  decide +kernel

def tail_ray_E2_13_denominator_power : List Fraction := [⟨0, 1⟩, ⟨280278715744942817280000000, 1⟩, ⟨797344622377854566400000000, 1⟩, ⟨679555075890216960000000000, 1⟩, ⟨151012239086714880000000000, 1⟩]
def tail_ray_E2_13_denominator_controls : List Fraction := [Fraction.mul ⟨25483315345883136000000, 1⟩ (Fraction.mul ⟨189225, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨25483315345883136000000, 1⟩ (Fraction.mul ⟨808230, 1⟩ ⟨1, 4⟩), Fraction.mul ⟨25483315345883136000000, 1⟩ (Fraction.mul ⟨1294336, 1⟩ ⟨1, 6⟩), Fraction.mul ⟨25483315345883136000000, 1⟩ (Fraction.mul ⟨921088, 1⟩ ⟨1, 4⟩), Fraction.mul ⟨25483315345883136000000, 1⟩ (Fraction.mul ⟨245760, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_E2_13_denominator_coefficient_0 : (Fraction.positive ⟨189225, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_13_denominator_coefficient_1 : (Fraction.positive ⟨808230, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_13_denominator_coefficient_2 : (Fraction.positive ⟨1294336, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_13_denominator_coefficient_3 : (Fraction.positive ⟨921088, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_13_denominator_coefficient_4 : (Fraction.positive ⟨245760, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_13_denominator_scale_positive : (Fraction.positive ⟨25483315345883136000000, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E2_13_denominator_reconstruct : (Fraction.allEq (bernstein tail_ray_E2_13_denominator_power ⟨29, 20⟩ ⟨8, 5⟩ 4) tail_ray_E2_13_denominator_controls) = true := by
  decide +kernel

end F4Heavy.Finite
