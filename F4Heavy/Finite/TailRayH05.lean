module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite

def tail_ray_H_05_numerator_power : List Fraction := [⟨-53884055290026343612032000000000, 1⟩, ⟨-489892994174065000795120855188368, 1⟩, ⟨-958340895481325314883084356944200, 1⟩, ⟨-221229248677395073332148290174561, 1⟩, ⟨796923106747286730431040184239703, 1⟩, ⟨455622224299396301012627198642944, 1⟩, ⟨-96586124353877677991632407100416, 1⟩, ⟨-46634784668254108995379200000000, 1⟩, ⟨4349032437440802167193600000000, 1⟩]
def tail_ray_H_05_numerator_controls : List Fraction := [Fraction.mul ⟨1, 62208⟩ (Fraction.mul ⟨322541680993879473004926889298101694625, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨1, 62208⟩ (Fraction.mul ⟨3140415988553714985789489812881789738128, 1⟩ ⟨1, 8⟩), Fraction.mul ⟨1, 62208⟩ (Fraction.mul ⟨13179891946331505398311356565079612161350, 1⟩ ⟨1, 28⟩), Fraction.mul ⟨1, 62208⟩ (Fraction.mul ⟨31163892268239179546130770268850605479052, 1⟩ ⟨1, 56⟩), Fraction.mul ⟨1, 62208⟩ (Fraction.mul ⟨45417778173763394515041767900174349497649, 1⟩ ⟨1, 70⟩), Fraction.mul ⟨1, 62208⟩ (Fraction.mul ⟨41768339124829626602371705544423129665804, 1⟩ ⟨1, 56⟩), Fraction.mul ⟨1, 62208⟩ (Fraction.mul ⟨23655737624922658144489430247911756498768, 1⟩ ⟨1, 28⟩), Fraction.mul ⟨1, 62208⟩ (Fraction.mul ⟨7534902811775782054122437326210052953664, 1⟩ ⟨1, 8⟩), Fraction.mul ⟨1, 62208⟩ (Fraction.mul ⟨1031604394601354140086275261914557984256, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_H_05_numerator_coefficient_0 : (Fraction.positive ⟨322541680993879473004926889298101694625, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_05_numerator_coefficient_1 : (Fraction.positive ⟨3140415988553714985789489812881789738128, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_05_numerator_coefficient_2 : (Fraction.positive ⟨13179891946331505398311356565079612161350, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_05_numerator_coefficient_3 : (Fraction.positive ⟨31163892268239179546130770268850605479052, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_05_numerator_coefficient_4 : (Fraction.positive ⟨45417778173763394515041767900174349497649, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_05_numerator_coefficient_5 : (Fraction.positive ⟨41768339124829626602371705544423129665804, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_05_numerator_coefficient_6 : (Fraction.positive ⟨23655737624922658144489430247911756498768, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_05_numerator_coefficient_7 : (Fraction.positive ⟨7534902811775782054122437326210052953664, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_05_numerator_coefficient_8 : (Fraction.positive ⟨1031604394601354140086275261914557984256, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_05_numerator_scale_positive : (Fraction.positive ⟨1, 62208⟩) = true := by
  decide +kernel

theorem tail_ray_H_05_numerator_reconstruct : (Fraction.allEq (bernstein tail_ray_H_05_numerator_power ⟨7, 4⟩ ⟨7, 3⟩ 8) tail_ray_H_05_numerator_controls) = true := by
  decide +kernel

def tail_ray_H_05_denominator_power : List Fraction := [⟨517485952152700332068044800000000, 1⟩, ⟨2458058272725326577323212800000000, 1⟩, ⟨4366287721288409051824128000000000, 1⟩, ⟨3436430151014025642639360000000000, 1⟩, ⟨1010714750298242836070400000000000, 1⟩]
def tail_ray_H_05_denominator_controls : List Fraction := [Fraction.mul ⟨389936246257038131200000000, 1⟩ (Fraction.mul ⟨118192041, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨389936246257038131200000000, 1⟩ (Fraction.mul ⟨578951388, 1⟩ ⟨1, 4⟩), Fraction.mul ⟨389936246257038131200000000, 1⟩ (Fraction.mul ⟨1063462608, 1⟩ ⟨1, 6⟩), Fraction.mul ⟨389936246257038131200000000, 1⟩ (Fraction.mul ⟨868190016, 1⟩ ⟨1, 4⟩), Fraction.mul ⟨389936246257038131200000000, 1⟩ (Fraction.mul ⟨265786880, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_H_05_denominator_coefficient_0 : (Fraction.positive ⟨118192041, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_05_denominator_coefficient_1 : (Fraction.positive ⟨578951388, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_05_denominator_coefficient_2 : (Fraction.positive ⟨1063462608, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_05_denominator_coefficient_3 : (Fraction.positive ⟨868190016, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_05_denominator_coefficient_4 : (Fraction.positive ⟨265786880, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_05_denominator_scale_positive : (Fraction.positive ⟨389936246257038131200000000, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_05_denominator_reconstruct : (Fraction.allEq (bernstein tail_ray_H_05_denominator_power ⟨7, 4⟩ ⟨7, 3⟩ 4) tail_ray_H_05_denominator_controls) = true := by
  decide +kernel

end F4Heavy.Finite
