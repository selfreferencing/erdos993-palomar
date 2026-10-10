module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite

def tail_ray_D_07_numerator_power : List Fraction := [⟨686245519804046704017408, 1⟩, ⟨1899574635685542600299004, 1⟩, ⟨1965566599839399800188161, 1⟩, ⟨885437343115979790750885, 1⟩, ⟨49398461028217356849760, 1⟩, ⟨21924722512836875000000, 1⟩, ⟨5734187216800000000000, 1⟩]
def tail_ray_D_07_numerator_controls : List Fraction := [Fraction.mul ⟨1, 1000⟩ (Fraction.mul ⟨3946132857409003345007149056, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨1, 1000⟩ (Fraction.mul ⟨27127729466907294414877928976, 1⟩ ⟨1, 6⟩), Fraction.mul ⟨1, 1000⟩ (Fraction.mul ⟨77553602408199384386355749890, 1⟩ ⟨1, 15⟩), Fraction.mul ⟨1, 1000⟩ (Fraction.mul ⟨118015090701853218213370455545, 1⟩ ⟨1, 20⟩), Fraction.mul ⟨1, 1000⟩ (Fraction.mul ⟨100820968561073795099202031215, 1⟩ ⟨1, 15⟩), Fraction.mul ⟨1, 1000⟩ (Fraction.mul ⟨45850769734964067251712694811, 1⟩ ⟨1, 6⟩), Fraction.mul ⟨1, 1000⟩ (Fraction.mul ⟨8672975673717659549396149171, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_D_07_numerator_coefficient_0 : (Fraction.positive ⟨3946132857409003345007149056, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_07_numerator_coefficient_1 : (Fraction.positive ⟨27127729466907294414877928976, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_07_numerator_coefficient_2 : (Fraction.positive ⟨77553602408199384386355749890, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_07_numerator_coefficient_3 : (Fraction.positive ⟨118015090701853218213370455545, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_07_numerator_coefficient_4 : (Fraction.positive ⟨100820968561073795099202031215, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_07_numerator_coefficient_5 : (Fraction.positive ⟨45850769734964067251712694811, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_07_numerator_coefficient_6 : (Fraction.positive ⟨8672975673717659549396149171, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_07_numerator_scale_positive : (Fraction.positive ⟨1, 1000⟩) = true := by
  decide +kernel

theorem tail_ray_D_07_numerator_reconstruct : (Fraction.allEq (bernstein tail_ray_D_07_numerator_power ⟨4, 5⟩ ⟨13, 10⟩ 6) tail_ray_D_07_numerator_controls) = true := by
  decide +kernel

def tail_ray_D_07_denominator_power : List Fraction := [⟨1184234260031078400000000, 1⟩, ⟨4292849192612659200000000, 1⟩, ⟨5148643482088243200000000, 1⟩, ⟨2040028549506662400000000, 1⟩]
def tail_ray_D_07_denominator_controls : List Fraction := [Fraction.mul ⟨4625915078246400000, 1⟩ (Fraction.mul ⟨1936512, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨4625915078246400000, 1⟩ (Fraction.mul ⟨7587296, 1⟩ ⟨1, 3⟩), Fraction.mul ⟨4625915078246400000, 1⟩ (Fraction.mul ⟨9907906, 1⟩ ⟨1, 3⟩), Fraction.mul ⟨4625915078246400000, 1⟩ (Fraction.mul ⟨4312247, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_D_07_denominator_coefficient_0 : (Fraction.positive ⟨1936512, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_07_denominator_coefficient_1 : (Fraction.positive ⟨7587296, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_07_denominator_coefficient_2 : (Fraction.positive ⟨9907906, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_07_denominator_coefficient_3 : (Fraction.positive ⟨4312247, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_07_denominator_scale_positive : (Fraction.positive ⟨4625915078246400000, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_07_denominator_reconstruct : (Fraction.allEq (bernstein tail_ray_D_07_denominator_power ⟨4, 5⟩ ⟨13, 10⟩ 3) tail_ray_D_07_denominator_controls) = true := by
  decide +kernel

end F4Heavy.Finite
