module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite

def tail_ray_E1_05_numerator_power : List Fraction := [⟨-185587114016737708800000000, 1⟩, ⟨-845054130129060185349416400, 1⟩, ⟨-1044458529795691563257002024, 1⟩, ⟨628098913762703690098990827, 1⟩, ⟨2011050594410108027937284395, 1⟩, ⟨748626986474923936901963400, 1⟩, ⟨-448998811980244657204426080, 1⟩, ⟨-167117533750892430000000000, 1⟩, ⟨28461426558353647200000000, 1⟩]
def tail_ray_E1_05_numerator_controls : List Fraction := [Fraction.mul ⟨3, 800000⟩ (Fraction.mul ⟨1032080391264978774575327920773808, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨3, 800000⟩ (Fraction.mul ⟨8807335428929509244745155326037008, 1⟩ ⟨1, 8⟩), Fraction.mul ⟨3, 800000⟩ (Fraction.mul ⟨32812046465749725017966900998742112, 1⟩ ⟨1, 28⟩), Fraction.mul ⟨3, 800000⟩ (Fraction.mul ⟨69708635159180179242813975539675972, 1⟩ ⟨1, 56⟩), Fraction.mul ⟨3, 800000⟩ (Fraction.mul ⟨92372016619623325216423681927501445, 1⟩ ⟨1, 70⟩), Fraction.mul ⟨3, 800000⟩ (Fraction.mul ⟨78182301146291550485517063876385782, 1⟩ ⟨1, 56⟩), Fraction.mul ⟨3, 800000⟩ (Fraction.mul ⟨41276249486508400238018197017343042, 1⟩ ⟨1, 28⟩), Fraction.mul ⟨3, 800000⟩ (Fraction.mul ⟨12428060197567712693806388331988738, 1⟩ ⟨1, 8⟩), Fraction.mul ⟨3, 800000⟩ (Fraction.mul ⟨1633938970767683041245957285552093, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_E1_05_numerator_coefficient_0 : (Fraction.positive ⟨1032080391264978774575327920773808, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_05_numerator_coefficient_1 : (Fraction.positive ⟨8807335428929509244745155326037008, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_05_numerator_coefficient_2 : (Fraction.positive ⟨32812046465749725017966900998742112, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_05_numerator_coefficient_3 : (Fraction.positive ⟨69708635159180179242813975539675972, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_05_numerator_coefficient_4 : (Fraction.positive ⟨92372016619623325216423681927501445, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_05_numerator_coefficient_5 : (Fraction.positive ⟨78182301146291550485517063876385782, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_05_numerator_coefficient_6 : (Fraction.positive ⟨41276249486508400238018197017343042, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_05_numerator_coefficient_7 : (Fraction.positive ⟨12428060197567712693806388331988738, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_05_numerator_coefficient_8 : (Fraction.positive ⟨1633938970767683041245957285552093, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_05_numerator_scale_positive : (Fraction.positive ⟨3, 800000⟩) = true := by
  decide +kernel

theorem tail_ray_E1_05_numerator_reconstruct : (Fraction.allEq (bernstein tail_ray_E1_05_numerator_power ⟨13, 10⟩ ⟨29, 20⟩ 8) tail_ray_E1_05_numerator_controls) = true := by
  decide +kernel

def tail_ray_E1_05_denominator_power : List Fraction := [⟨965874125805872742400000000, 1⟩, ⟨4587902097577895526400000000, 1⟩, ⟨8149562936487051264000000000, 1⟩, ⟨6414007866679623680000000000, 1⟩, ⟨1886472901964595200000000000, 1⟩]
def tail_ray_E1_05_denominator_controls : List Fraction := [Fraction.mul ⟨318342302206525440000000, 1⟩ (Fraction.mul ⟨126224, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨318342302206525440000000, 1⟩ (Fraction.mul ⟨540176, 1⟩ ⟨1, 4⟩), Fraction.mul ⟨318342302206525440000000, 1⟩ (Fraction.mul ⟨866880, 1⟩ ⟨1, 6⟩), Fraction.mul ⟨318342302206525440000000, 1⟩ (Fraction.mul ⟨618300, 1⟩ ⟨1, 4⟩), Fraction.mul ⟨318342302206525440000000, 1⟩ (Fraction.mul ⟨165375, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_E1_05_denominator_coefficient_0 : (Fraction.positive ⟨126224, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_05_denominator_coefficient_1 : (Fraction.positive ⟨540176, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_05_denominator_coefficient_2 : (Fraction.positive ⟨866880, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_05_denominator_coefficient_3 : (Fraction.positive ⟨618300, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_05_denominator_coefficient_4 : (Fraction.positive ⟨165375, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_05_denominator_scale_positive : (Fraction.positive ⟨318342302206525440000000, 1⟩) = true := by
  decide +kernel

theorem tail_ray_E1_05_denominator_reconstruct : (Fraction.allEq (bernstein tail_ray_E1_05_denominator_power ⟨13, 10⟩ ⟨29, 20⟩ 4) tail_ray_E1_05_denominator_controls) = true := by
  decide +kernel

end F4Heavy.Finite
