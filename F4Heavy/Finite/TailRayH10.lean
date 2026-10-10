module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite

def tail_ray_H_10_numerator_power : List Fraction := [⟨1651034336, 1⟩, ⟨3171236128, 1⟩, ⟨943854521, 1⟩, ⟨-544983808, 1⟩]
def tail_ray_H_10_numerator_controls : List Fraction := [Fraction.mul ⟨7, 432⟩ (Fraction.mul ⟨442521016533, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨7, 432⟩ (Fraction.mul ⟨1380399825357, 1⟩ ⟨1, 3⟩), Fraction.mul ⟨7, 432⟩ (Fraction.mul ⟨1392973081224, 1⟩ ⟨1, 3⟩), Fraction.mul ⟨7, 432⟩ (Fraction.mul ⟨448418220752, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_H_10_numerator_coefficient_0 : (Fraction.positive ⟨442521016533, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_10_numerator_coefficient_1 : (Fraction.positive ⟨1380399825357, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_10_numerator_coefficient_2 : (Fraction.positive ⟨1392973081224, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_10_numerator_coefficient_3 : (Fraction.positive ⟨448418220752, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_10_numerator_scale_positive : (Fraction.positive ⟨7, 432⟩) = true := by
  decide +kernel

theorem tail_ray_H_10_numerator_reconstruct : (Fraction.allEq (bernstein tail_ray_H_10_numerator_power ⟨7, 4⟩ ⟨7, 3⟩ 3) tail_ray_H_10_numerator_controls) = true := by
  decide +kernel

def tail_ray_H_10_denominator_power : List Fraction := [⟨536870912, 1⟩, ⟨1342177280, 1⟩, ⟨838860800, 1⟩]
def tail_ray_H_10_denominator_controls : List Fraction := [Fraction.mul ⟨2097152, 9⟩ (Fraction.mul ⟨23409, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨2097152, 9⟩ (Fraction.mul ⟨57528, 1⟩ ⟨1, 2⟩), Fraction.mul ⟨2097152, 9⟩ (Fraction.mul ⟨35344, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_H_10_denominator_coefficient_0 : (Fraction.positive ⟨23409, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_10_denominator_coefficient_1 : (Fraction.positive ⟨57528, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_10_denominator_coefficient_2 : (Fraction.positive ⟨35344, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_10_denominator_scale_positive : (Fraction.positive ⟨2097152, 9⟩) = true := by
  decide +kernel

theorem tail_ray_H_10_denominator_reconstruct : (Fraction.allEq (bernstein tail_ray_H_10_denominator_power ⟨7, 4⟩ ⟨7, 3⟩ 2) tail_ray_H_10_denominator_controls) = true := by
  decide +kernel

end F4Heavy.Finite
