module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite

def tail_ray_H_07_numerator_power : List Fraction := [⟨9569267713752227277677568, 1⟩, ⟨25738664146919254591621857, 1⟩, ⟨24917462487107881120716413, 1⟩, ⟨8859383171994190702177180, 1⟩, ⟨-849888639909712785175552, 1⟩, ⟨152211107326382400000000, 1⟩, ⟨6292487035699200000000, 1⟩]
def tail_ray_H_07_numerator_controls : List Fraction := [Fraction.mul ⟨1, 1296⟩ (Fraction.mul ⟨224351055217032259132456182954, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨1, 1296⟩ (Fraction.mul ⟨1485122197834030270996647121023, 1⟩ ⟨1, 6⟩), Fraction.mul ⟨1, 1296⟩ (Fraction.mul ⟨4088946363254891837598022576245, 1⟩ ⟨1, 15⟩), Fraction.mul ⟨1, 1296⟩ (Fraction.mul ⟨5993705889224681349235222958121, 1⟩ ⟨1, 20⟩), Fraction.mul ⟨1, 1296⟩ (Fraction.mul ⟨4933511339369101154789711476541, 1⟩ ⟨1, 15⟩), Fraction.mul ⟨1, 1296⟩ (Fraction.mul ⟨2162204913868328900471970876308, 1⟩ ⟨1, 6⟩), Fraction.mul ⟨1, 1296⟩ (Fraction.mul ⟨394224564398865643738850719712, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_H_07_numerator_coefficient_0 : (Fraction.positive ⟨224351055217032259132456182954, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_07_numerator_coefficient_1 : (Fraction.positive ⟨1485122197834030270996647121023, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_07_numerator_coefficient_2 : (Fraction.positive ⟨4088946363254891837598022576245, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_07_numerator_coefficient_3 : (Fraction.positive ⟨5993705889224681349235222958121, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_07_numerator_coefficient_4 : (Fraction.positive ⟨4933511339369101154789711476541, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_07_numerator_coefficient_5 : (Fraction.positive ⟨2162204913868328900471970876308, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_07_numerator_coefficient_6 : (Fraction.positive ⟨394224564398865643738850719712, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_07_numerator_scale_positive : (Fraction.positive ⟨1, 1296⟩) = true := by
  decide +kernel

theorem tail_ray_H_07_numerator_reconstruct : (Fraction.allEq (bernstein tail_ray_H_07_numerator_power ⟨7, 4⟩ ⟨7, 3⟩ 6) tail_ray_H_07_numerator_controls) = true := by
  decide +kernel

def tail_ray_H_07_denominator_power : List Fraction := [⟨11566712382868684800000000, 1⟩, ⟨40483493340040396800000000, 1⟩, ⟨46989769055404032000000000, 1⟩, ⟨18072988098232320000000000, 1⟩]
def tail_ray_H_07_denominator_controls : List Fraction := [Fraction.mul ⟨418356205977600000000, 1⟩ (Fraction.mul ⟨772497, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨418356205977600000000, 1⟩ (Fraction.mul ⟨2834784, 1⟩ ⟨1, 3⟩), Fraction.mul ⟨418356205977600000000, 1⟩ (Fraction.mul ⟨3467472, 1⟩ ⟨1, 3⟩), Fraction.mul ⟨418356205977600000000, 1⟩ (Fraction.mul ⟨1413760, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_H_07_denominator_coefficient_0 : (Fraction.positive ⟨772497, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_07_denominator_coefficient_1 : (Fraction.positive ⟨2834784, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_07_denominator_coefficient_2 : (Fraction.positive ⟨3467472, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_07_denominator_coefficient_3 : (Fraction.positive ⟨1413760, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_07_denominator_scale_positive : (Fraction.positive ⟨418356205977600000000, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_07_denominator_reconstruct : (Fraction.allEq (bernstein tail_ray_H_07_denominator_power ⟨7, 4⟩ ⟨7, 3⟩ 3) tail_ray_H_07_denominator_controls) = true := by
  decide +kernel

end F4Heavy.Finite
