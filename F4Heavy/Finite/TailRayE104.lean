module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite

def tail_ray_E1_04_numerator_power : List Fraction := [⟨-6848014661700000000, 1⟩, ⟨1562274399994787605, 1⟩, ⟨8823789750642739344, 1⟩, ⟨-1264746462812500000, 1⟩, ⟨155801481540000000, 1⟩]
def tail_ray_E1_04_numerator_controls : List Fraction := [Fraction.mul ⟨3, 100⟩ (Fraction.mul ⟨258716112316892829262, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨3, 100⟩ (Fraction.mul ⟨1132169682292471591545, 1⟩ ⟨1, 4⟩), Fraction.mul ⟨3, 100⟩ (Fraction.mul ⟨1848315702152424991071, 1⟩ ⟨1, 6⟩), Fraction.mul ⟨3, 100⟩ (Fraction.mul ⟨1334935666584641018305, 1⟩ ⟨1, 4⟩), Fraction.mul ⟨3, 100⟩ (Fraction.mul ⟨360076163557795777017, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_E1_04_numerator_coefficient_0 : (Fraction.positive ⟨258716112316892829262, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_04_numerator_coefficient_1 : (Fraction.positive ⟨1132169682292471591545, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_04_numerator_coefficient_2 : (Fraction.positive ⟨1848315702152424991071, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_04_numerator_coefficient_3 : (Fraction.positive ⟨1334935666584641018305, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_04_numerator_coefficient_4 : (Fraction.positive ⟨360076163557795777017, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_04_numerator_scale_positive : (Fraction.positive ⟨3, 100⟩) = true := by
  decide +kernel

theorem tail_ray_E1_04_numerator_reconstruct : (Fraction.allEq (bernstein tail_ray_E1_04_numerator_power ⟨13, 10⟩ ⟨29, 20⟩ 4) tail_ray_E1_04_numerator_controls) = true := by
  decide +kernel

def tail_ray_E1_04_denominator_power : List Fraction := [⟨23028233666560000000, 1⟩, ⟨28785292083200000000, 1⟩]
def tail_ray_E1_04_denominator_controls : List Fraction := [Fraction.mul ⟨4317793812480000000, 1⟩ (Fraction.mul ⟨14, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨4317793812480000000, 1⟩ (Fraction.mul ⟨15, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_E1_04_denominator_coefficient_0 : (Fraction.positive ⟨14, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_04_denominator_coefficient_1 : (Fraction.positive ⟨15, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_04_denominator_scale_positive : (Fraction.positive ⟨4317793812480000000, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_04_denominator_reconstruct : (Fraction.allEq (bernstein tail_ray_E1_04_denominator_power ⟨13, 10⟩ ⟨29, 20⟩ 1) tail_ray_E1_04_denominator_controls) = true := by
  decide +kernel

end F4Heavy.Finite
