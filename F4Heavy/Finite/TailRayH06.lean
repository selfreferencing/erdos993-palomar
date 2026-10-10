module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite

def tail_ray_H_06_numerator_power : List Fraction := [⟨3644415168, 1⟩, ⟨12185721096, 1⟩, ⟨14361767141, 1⟩, ⟨6269843869, 1⟩, ⟨298387712, 1⟩]
def tail_ray_H_06_numerator_controls : List Fraction := [Fraction.mul ⟨1, 5184⟩ (Fraction.mul ⟨546151682511135, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨1, 5184⟩ (Fraction.mul ⟨2566999946477439, 1⟩ ⟨1, 4⟩), Fraction.mul ⟨1, 5184⟩ (Fraction.mul ⟨4517160715775952, 1⟩ ⟨1, 6⟩), Fraction.mul ⟨1, 5184⟩ (Fraction.mul ⟨3526529278194864, 1⟩ ⟨1, 4⟩), Fraction.mul ⟨1, 5184⟩ (Fraction.mul ⟨1030395933609344, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_H_06_numerator_coefficient_0 : (Fraction.positive ⟨546151682511135, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_06_numerator_coefficient_1 : (Fraction.positive ⟨2566999946477439, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_06_numerator_coefficient_2 : (Fraction.positive ⟨4517160715775952, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_06_numerator_coefficient_3 : (Fraction.positive ⟨3526529278194864, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_06_numerator_coefficient_4 : (Fraction.positive ⟨1030395933609344, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_06_numerator_scale_positive : (Fraction.positive ⟨1, 5184⟩) = true := by
  decide +kernel

theorem tail_ray_H_06_numerator_reconstruct : (Fraction.allEq (bernstein tail_ray_H_06_numerator_power ⟨7, 4⟩ ⟨7, 3⟩ 4) tail_ray_H_06_numerator_controls) = true := by
  decide +kernel

def tail_ray_H_06_denominator_power : List Fraction := [⟨3221225472, 1⟩, ⟨11274289152, 1⟩, ⟨13086228480, 1⟩, ⟨5033164800, 1⟩]
def tail_ray_H_06_denominator_controls : List Fraction := [Fraction.mul ⟨1048576, 9⟩ (Fraction.mul ⟨772497, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨1048576, 9⟩ (Fraction.mul ⟨2834784, 1⟩ ⟨1, 3⟩), Fraction.mul ⟨1048576, 9⟩ (Fraction.mul ⟨3467472, 1⟩ ⟨1, 3⟩), Fraction.mul ⟨1048576, 9⟩ (Fraction.mul ⟨1413760, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_H_06_denominator_coefficient_0 : (Fraction.positive ⟨772497, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_06_denominator_coefficient_1 : (Fraction.positive ⟨2834784, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_06_denominator_coefficient_2 : (Fraction.positive ⟨3467472, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_06_denominator_coefficient_3 : (Fraction.positive ⟨1413760, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_06_denominator_scale_positive : (Fraction.positive ⟨1048576, 9⟩) = true := by
  decide +kernel

theorem tail_ray_H_06_denominator_reconstruct : (Fraction.allEq (bernstein tail_ray_H_06_denominator_power ⟨7, 4⟩ ⟨7, 3⟩ 3) tail_ray_H_06_denominator_controls) = true := by
  decide +kernel

end F4Heavy.Finite
