module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite

def cap_d13_D_13_numerator : List Fraction := [⟨-76892550000000, 1⟩, ⟨-639850102500000, 1⟩, ⟨-1889786981575616, 1⟩, ⟨-386967427023616, 1⟩, ⟨2191955824155200, 1⟩, ⟨2469663657339642, 1⟩, ⟨1120955653607145, 1⟩, ⟨184682990252800, 1⟩]
def cap_d13_D_13_denominator : List Fraction := [⟨0, 1⟩, ⟨0, 1⟩, ⟨3810743287808000, 1⟩, ⟨16532067319808000, 1⟩, ⟨21376951910400000, 1⟩, ⟨12234657890304000, 1⟩, ⟨3270891274240000, 1⟩, ⟨334731673600000, 1⟩]
def cap_d13_D_13_controls : List Fraction := [⟨216517495315968, 5⟩, ⟨103619277601269552, 175⟩, ⟨3819946842585694832, 2625⟩, ⟨2417796177304596072, 875⟩, ⟨8213263603513784203, 1750⟩, ⟨62872470070953610969, 8400⟩, ⟨18334908716307577103, 1600⟩, ⟨136376203248902270073, 8000⟩]

theorem cap_d13_D_13_coefficient_0 : (Fraction.lt ⟨10000000000000, 1⟩ ⟨216517495315968, 5⟩) = true := by
  decide +kernel

theorem cap_d13_D_13_coefficient_1 : (Fraction.lt ⟨10000000000000, 1⟩ ⟨103619277601269552, 175⟩) = true := by
  decide +kernel

theorem cap_d13_D_13_coefficient_2 : (Fraction.lt ⟨10000000000000, 1⟩ ⟨3819946842585694832, 2625⟩) = true := by
  decide +kernel

theorem cap_d13_D_13_coefficient_3 : (Fraction.lt ⟨10000000000000, 1⟩ ⟨2417796177304596072, 875⟩) = true := by
  decide +kernel

theorem cap_d13_D_13_coefficient_4 : (Fraction.lt ⟨10000000000000, 1⟩ ⟨8213263603513784203, 1750⟩) = true := by
  decide +kernel

theorem cap_d13_D_13_coefficient_5 : (Fraction.lt ⟨10000000000000, 1⟩ ⟨62872470070953610969, 8400⟩) = true := by
  decide +kernel

theorem cap_d13_D_13_coefficient_6 : (Fraction.lt ⟨10000000000000, 1⟩ ⟨18334908716307577103, 1600⟩) = true := by
  decide +kernel

theorem cap_d13_D_13_coefficient_7 : (Fraction.lt ⟨10000000000000, 1⟩ ⟨136376203248902270073, 8000⟩) = true := by
  decide +kernel

theorem cap_d13_D_13_reconstruct : (Fraction.allEq (bernstein cap_d13_D_13_numerator ⟨4, 5⟩ ⟨13, 10⟩ 7) cap_d13_D_13_controls) = true := by
  decide +kernel

end F4Heavy.Finite
