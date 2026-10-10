module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite

def tail_ray_E1_13_numerator_power : List Fraction := [⟨1789341825080640000000, 1⟩, ⟨5146867359345456000000, 1⟩, ⟨2503171013120157034176, 1⟩, ⟨-2912231396653075816536, 1⟩, ⟨-1042402111087645725871, 1⟩, ⟨887676693132036883536, 1⟩, ⟨-149533310191122500000, 1⟩, ⟨41910598534260000000, 1⟩]
def tail_ray_E1_13_numerator_controls : List Fraction := [Fraction.mul ⟨3, 800000⟩ (Fraction.mul ⟨1645959158330591048878534768, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨3, 800000⟩ (Fraction.mul ⟨11461344387330813983199006576, 1⟩ ⟨1, 7⟩), Fraction.mul ⟨3, 800000⟩ (Fraction.mul ⟨34184560220783877787072946808, 1⟩ ⟨1, 21⟩), Fraction.mul ⟨3, 800000⟩ (Fraction.mul ⟨56615065080713629648068976160, 1⟩ ⟨1, 35⟩), Fraction.mul ⟨3, 800000⟩ (Fraction.mul ⟨56233536858292788045559036455, 1⟩ ⟨1, 35⟩), Fraction.mul ⟨3, 800000⟩ (Fraction.mul ⟨33500823290076882746374718577, 1⟩ ⟨1, 21⟩), Fraction.mul ⟨3, 800000⟩ (Fraction.mul ⟨11084848144135179599607425719, 1⟩ ⟨1, 7⟩), Fraction.mul ⟨3, 800000⟩ (Fraction.mul ⟨1571671642516626560647454937, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_E1_13_numerator_coefficient_0 : (Fraction.positive ⟨1645959158330591048878534768, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_13_numerator_coefficient_1 : (Fraction.positive ⟨11461344387330813983199006576, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_13_numerator_coefficient_2 : (Fraction.positive ⟨34184560220783877787072946808, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_13_numerator_coefficient_3 : (Fraction.positive ⟨56615065080713629648068976160, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_13_numerator_coefficient_4 : (Fraction.positive ⟨56233536858292788045559036455, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_13_numerator_coefficient_5 : (Fraction.positive ⟨33500823290076882746374718577, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_13_numerator_coefficient_6 : (Fraction.positive ⟨11084848144135179599607425719, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_13_numerator_coefficient_7 : (Fraction.positive ⟨1571671642516626560647454937, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_13_numerator_scale_positive : (Fraction.positive ⟨3, 800000⟩) = true := by
  decide +kernel

theorem tail_ray_E1_13_numerator_reconstruct : (Fraction.allEq (bernstein tail_ray_E1_13_numerator_power ⟨13, 10⟩ ⟨29, 20⟩ 7) tail_ray_E1_13_numerator_controls) = true := by
  decide +kernel

def tail_ray_E1_13_denominator_power : List Fraction := [⟨0, 1⟩, ⟨3205530126385152000000, 1⟩, ⟨9119180531957760000000, 1⟩, ⟨7772028862464000000000, 1⟩, ⟨1727117524992000000000, 1⟩]
def tail_ray_E1_13_denominator_controls : List Fraction := [Fraction.mul ⟨291451082342400000, 1⟩ (Fraction.mul ⟨142688, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨291451082342400000, 1⟩ (Fraction.mul ⟨612696, 1⟩ ⟨1, 4⟩), Fraction.mul ⟨291451082342400000, 1⟩ (Fraction.mul ⟨986356, 1⟩ ⟨1, 6⟩), Fraction.mul ⟨291451082342400000, 1⟩ (Fraction.mul ⟨705570, 1⟩ ⟨1, 4⟩), Fraction.mul ⟨291451082342400000, 1⟩ (Fraction.mul ⟨189225, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_E1_13_denominator_coefficient_0 : (Fraction.positive ⟨142688, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_13_denominator_coefficient_1 : (Fraction.positive ⟨612696, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_13_denominator_coefficient_2 : (Fraction.positive ⟨986356, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_13_denominator_coefficient_3 : (Fraction.positive ⟨705570, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_13_denominator_coefficient_4 : (Fraction.positive ⟨189225, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_13_denominator_scale_positive : (Fraction.positive ⟨291451082342400000, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_13_denominator_reconstruct : (Fraction.allEq (bernstein tail_ray_E1_13_denominator_power ⟨13, 10⟩ ⟨29, 20⟩ 4) tail_ray_E1_13_denominator_controls) = true := by
  decide +kernel

end F4Heavy.Finite
