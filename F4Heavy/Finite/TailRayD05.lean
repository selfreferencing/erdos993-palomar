module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite

def tail_ray_D_05_numerator_power : List Fraction := [⟨-914491772320202346332160000000, 1⟩, ⟨-9759681838305994274302283557632, 1⟩, ⟨-2851516708286956635396595780704, 1⟩, ⟨48642817707717158553068671833397, 1⟩, ⟨61790693443193876165985756222517, 1⟩, ⟨8180132076478099771479947106912, 1⟩, ⟨-8708638120504706443009312047936, 1⟩, ⟨2064101459551193893696000000000, 1⟩, ⟨-399261119324127764480000000000, 1⟩]
def tail_ray_D_05_numerator_controls : List Fraction := [Fraction.mul ⟨1, 250000⟩ (Fraction.mul ⟨10107704940447637173536472013646214144, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨1, 250000⟩ (Fraction.mul ⟨106907672841423095345825341871773265792, 1⟩ ⟨1, 8⟩), Fraction.mul ⟨1, 250000⟩ (Fraction.mul ⟨487264032990594775697188825720242910512, 1⟩ ⟨1, 28⟩), Fraction.mul ⟨1, 250000⟩ (Fraction.mul ⟨1251798729710784703391870585761495109754, 1⟩ ⟨1, 56⟩), Fraction.mul ⟨1, 250000⟩ (Fraction.mul ⟨1984831878862446821093961934888629631855, 1⟩ ⟨1, 70⟩), Fraction.mul ⟨1, 250000⟩ (Fraction.mul ⟨1990748434883947938417520261481524479464, 1⟩ ⟨1, 56⟩), Fraction.mul ⟨1, 250000⟩ (Fraction.mul ⟨1234309410886856220466341604724060422722, 1⟩ ⟨1, 28⟩), Fraction.mul ⟨1, 250000⟩ (Fraction.mul ⟨432798552279092111575782198078804701382, 1⟩ ⟨1, 8⟩), Fraction.mul ⟨1, 250000⟩ (Fraction.mul ⟨65739972131465554331449549847018377159, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_D_05_numerator_coefficient_0 : (Fraction.positive ⟨10107704940447637173536472013646214144, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_05_numerator_coefficient_1 : (Fraction.positive ⟨106907672841423095345825341871773265792, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_05_numerator_coefficient_2 : (Fraction.positive ⟨487264032990594775697188825720242910512, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_05_numerator_coefficient_3 : (Fraction.positive ⟨1251798729710784703391870585761495109754, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_05_numerator_coefficient_4 : (Fraction.positive ⟨1984831878862446821093961934888629631855, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_05_numerator_coefficient_5 : (Fraction.positive ⟨1990748434883947938417520261481524479464, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_05_numerator_coefficient_6 : (Fraction.positive ⟨1234309410886856220466341604724060422722, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_05_numerator_coefficient_7 : (Fraction.positive ⟨432798552279092111575782198078804701382, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_05_numerator_coefficient_8 : (Fraction.positive ⟨65739972131465554331449549847018377159, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_05_numerator_scale_positive : (Fraction.positive ⟨1, 250000⟩) = true := by
  decide +kernel

theorem tail_ray_D_05_numerator_reconstruct : (Fraction.allEq (bernstein tail_ray_D_05_numerator_power ⟨4, 5⟩ ⟨13, 10⟩ 8) tail_ray_D_05_numerator_controls) = true := by
  decide +kernel

def tail_ray_D_05_denominator_power : List Fraction := [⟨84770790293937361193533440000000, 1⟩, ⟨418555777076315720893071360000000, 1⟩, ⟨771877781934249956805181440000000, 1⟩, ⟨629758393030815420839362560000000, 1⟩, ⟨191665597878943823733719040000000, 1⟩]
def tail_ray_D_05_denominator_controls : List Fraction := [Fraction.mul ⟨2069599372410580107264000, 1⟩ (Fraction.mul ⟨635175936, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨2069599372410580107264000, 1⟩ (Fraction.mul ⟨3327142784, 1⟩ ⟨1, 4⟩), Fraction.mul ⟨2069599372410580107264000, 1⟩ (Fraction.mul ⟨6535092336, 1⟩ ⟨1, 6⟩), Fraction.mul ⟨2069599372410580107264000, 1⟩ (Fraction.mul ⟨5704540314, 1⟩ ⟨1, 4⟩), Fraction.mul ⟨2069599372410580107264000, 1⟩ (Fraction.mul ⟨1867202951, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_D_05_denominator_coefficient_0 : (Fraction.positive ⟨635175936, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_05_denominator_coefficient_1 : (Fraction.positive ⟨3327142784, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_05_denominator_coefficient_2 : (Fraction.positive ⟨6535092336, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_05_denominator_coefficient_3 : (Fraction.positive ⟨5704540314, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_05_denominator_coefficient_4 : (Fraction.positive ⟨1867202951, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_05_denominator_scale_positive : (Fraction.positive ⟨2069599372410580107264000, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_05_denominator_reconstruct : (Fraction.allEq (bernstein tail_ray_D_05_denominator_power ⟨4, 5⟩ ⟨13, 10⟩ 4) tail_ray_D_05_denominator_controls) = true := by
  decide +kernel

end F4Heavy.Finite
