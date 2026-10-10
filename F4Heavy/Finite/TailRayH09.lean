module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite

def tail_ray_H_09_numerator_power : List Fraction := [⟨-7785234147716784000000000, 1⟩, ⟨-40125729886913254320000000, 1⟩, ⟨-69381461509468700960830239, 1⟩, ⟨-33973137327531660148477507, 1⟩, ⟨20784263234667274003739680, 1⟩, ⟨17863314220414292414824448, 1⟩, ⟨152211107326382400000000, 1⟩, ⟨6292487035699200000000, 1⟩]
def tail_ray_H_09_numerator_controls : List Fraction := [Fraction.mul ⟨1, 15552⟩ (Fraction.mul ⟨314978301472138655314162106853, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨1, 15552⟩ (Fraction.mul ⟨8595346703420829486907356193260, 1⟩ ⟨1, 7⟩), Fraction.mul ⟨1, 15552⟩ (Fraction.mul ⟨50858723772577991703128574212838, 1⟩ ⟨1, 21⟩), Fraction.mul ⟨1, 15552⟩ (Fraction.mul ⟨138477438748093895926879906634796, 1⟩ ⟨1, 35⟩), Fraction.mul ⟨1, 15552⟩ (Fraction.mul ⟨206538819157068912177991651106349, 1⟩ ⟨1, 35⟩), Fraction.mul ⟨1, 15552⟩ (Fraction.mul ⟨175044274706736247083315564139760, 1⟩ ⟨1, 21⟩), Fraction.mul ⟨1, 15552⟩ (Fraction.mul ⟨79455600683109174643199507847056, 1⟩ ⟨1, 7⟩), Fraction.mul ⟨1, 15552⟩ (Fraction.mul ⟨15051064005167197304417468305280, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_H_09_numerator_coefficient_0 : (Fraction.positive ⟨314978301472138655314162106853, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_09_numerator_coefficient_1 : (Fraction.positive ⟨8595346703420829486907356193260, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_09_numerator_coefficient_2 : (Fraction.positive ⟨50858723772577991703128574212838, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_09_numerator_coefficient_3 : (Fraction.positive ⟨138477438748093895926879906634796, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_09_numerator_coefficient_4 : (Fraction.positive ⟨206538819157068912177991651106349, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_09_numerator_coefficient_5 : (Fraction.positive ⟨175044274706736247083315564139760, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_09_numerator_coefficient_6 : (Fraction.positive ⟨79455600683109174643199507847056, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_09_numerator_coefficient_7 : (Fraction.positive ⟨15051064005167197304417468305280, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_09_numerator_scale_positive : (Fraction.positive ⟨1, 15552⟩) = true := by
  decide +kernel

theorem tail_ray_H_09_numerator_reconstruct : (Fraction.allEq (bernstein tail_ray_H_09_numerator_power ⟨7, 4⟩ ⟨7, 3⟩ 7) tail_ray_H_09_numerator_controls) = true := by
  decide +kernel

def tail_ray_H_09_denominator_power : List Fraction := [⟨0, 1⟩, ⟨11566712382868684800000000, 1⟩, ⟨43375171435757568000000000, 1⟩, ⟨54218964294696960000000000, 1⟩, ⟨22591235122790400000000000, 1⟩]
def tail_ray_H_09_denominator_controls : List Fraction := [Fraction.mul ⟨61010280038400000000, 1⟩ (Fraction.mul ⟨10744731, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨61010280038400000000, 1⟩ (Fraction.mul ⟨53934336, 1⟩ ⟨1, 4⟩), Fraction.mul ⟨61010280038400000000, 1⟩ (Fraction.mul ⟨101479392, 1⟩ ⟨1, 6⟩), Fraction.mul ⟨61010280038400000000, 1⟩ (Fraction.mul ⟨84825600, 1⟩ ⟨1, 4⟩), Fraction.mul ⟨61010280038400000000, 1⟩ (Fraction.mul ⟨26578688, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_H_09_denominator_coefficient_0 : (Fraction.positive ⟨10744731, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_09_denominator_coefficient_1 : (Fraction.positive ⟨53934336, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_09_denominator_coefficient_2 : (Fraction.positive ⟨101479392, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_09_denominator_coefficient_3 : (Fraction.positive ⟨84825600, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_09_denominator_coefficient_4 : (Fraction.positive ⟨26578688, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_09_denominator_scale_positive : (Fraction.positive ⟨61010280038400000000, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_09_denominator_reconstruct : (Fraction.allEq (bernstein tail_ray_H_09_denominator_power ⟨7, 4⟩ ⟨7, 3⟩ 4) tail_ray_H_09_denominator_controls) = true := by
  decide +kernel

end F4Heavy.Finite
