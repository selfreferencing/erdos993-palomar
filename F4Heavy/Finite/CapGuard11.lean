module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite

def cap_guard11_D_numerator : List Fraction := [⟨655800, 1⟩, ⟨4790740, 1⟩, ⟨-2732077, 1⟩, ⟨9523632, 1⟩, ⟨-5861376, 1⟩]
def cap_guard11_D_denominator : List Fraction := [⟨50331648, 1⟩, ⟨209715200, 1⟩, ⟨234881024, 1⟩, ⟨33554432, 1⟩]
def cap_guard11_D_controls : List Fraction := [⟨3259464184, 625⟩, ⟨7565911523, 1250⟩, ⟨101865333611, 15000⟩, ⟨35707488307, 5000⟩, ⟨16123238451, 2500⟩]

theorem cap_guard11_D_coefficient_0 : (Fraction.lt ⟨1000000, 1⟩ ⟨3259464184, 625⟩) = true := by
  decide +kernel

theorem cap_guard11_D_coefficient_1 : (Fraction.lt ⟨1000000, 1⟩ ⟨7565911523, 1250⟩) = true := by
  decide +kernel

theorem cap_guard11_D_coefficient_2 : (Fraction.lt ⟨1000000, 1⟩ ⟨101865333611, 15000⟩) = true := by
  decide +kernel

theorem cap_guard11_D_coefficient_3 : (Fraction.lt ⟨1000000, 1⟩ ⟨35707488307, 5000⟩) = true := by
  decide +kernel

theorem cap_guard11_D_coefficient_4 : (Fraction.lt ⟨1000000, 1⟩ ⟨16123238451, 2500⟩) = true := by
  decide +kernel

theorem cap_guard11_D_reconstruct : (Fraction.allEq (bernstein cap_guard11_D_numerator ⟨4, 5⟩ ⟨13, 10⟩ 4) cap_guard11_D_controls) = true := by
  decide +kernel

def cap_guard11_E1_numerator : List Fraction := [⟨438990, 1⟩, ⟨1616821, 1⟩, ⟨-90985, 1⟩, ⟨-1872167, 1⟩, ⟨762536, 1⟩]
def cap_guard11_E1_denominator : List Fraction := [⟨1572864, 1⟩, ⟨6553600, 1⟩, ⟨7340032, 1⟩, ⟨1048576, 1⟩]
def cap_guard11_E1_controls : List Fraction := [⟨2259104103, 5000⟩, ⟨15957142341, 40000⟩, ⟨13892403669, 40000⟩, ⟨47797024959, 160000⟩, ⟨10213780839, 40000⟩]

theorem cap_guard11_E1_coefficient_0 : (Fraction.lt ⟨100000, 1⟩ ⟨2259104103, 5000⟩) = true := by
  decide +kernel

theorem cap_guard11_E1_coefficient_1 : (Fraction.lt ⟨100000, 1⟩ ⟨15957142341, 40000⟩) = true := by
  decide +kernel

theorem cap_guard11_E1_coefficient_2 : (Fraction.lt ⟨100000, 1⟩ ⟨13892403669, 40000⟩) = true := by
  decide +kernel

theorem cap_guard11_E1_coefficient_3 : (Fraction.lt ⟨100000, 1⟩ ⟨47797024959, 160000⟩) = true := by
  decide +kernel

theorem cap_guard11_E1_coefficient_4 : (Fraction.lt ⟨100000, 1⟩ ⟨10213780839, 40000⟩) = true := by
  decide +kernel

theorem cap_guard11_E1_reconstruct : (Fraction.allEq (bernstein cap_guard11_E1_numerator ⟨13, 10⟩ ⟨29, 20⟩ 4) cap_guard11_E1_controls) = true := by
  decide +kernel

def cap_guard11_E2_numerator : List Fraction := [⟨-2650152, 1⟩, ⟨-7709180, 1⟩, ⟨-11442425, 1⟩, ⟨5048176, 1⟩, ⟨5183488, 1⟩]
def cap_guard11_E2_denominator : List Fraction := [⟨25165824, 1⟩, ⟨104857600, 1⟩, ⟨117440512, 1⟩, ⟨16777216, 1⟩]
def cap_guard11_E2_controls : List Fraction := [⟨4174750963, 10000⟩, ⟨48968903453, 20000⟩, ⟨95281318109, 20000⟩, ⟨18484908469, 2500⟩, ⟨6481492408, 625⟩]

theorem cap_guard11_E2_coefficient_0 : (Fraction.lt ⟨100000, 1⟩ ⟨4174750963, 10000⟩) = true := by
  decide +kernel

theorem cap_guard11_E2_coefficient_1 : (Fraction.lt ⟨100000, 1⟩ ⟨48968903453, 20000⟩) = true := by
  decide +kernel

theorem cap_guard11_E2_coefficient_2 : (Fraction.lt ⟨100000, 1⟩ ⟨95281318109, 20000⟩) = true := by
  decide +kernel

theorem cap_guard11_E2_coefficient_3 : (Fraction.lt ⟨100000, 1⟩ ⟨18484908469, 2500⟩) = true := by
  decide +kernel

theorem cap_guard11_E2_coefficient_4 : (Fraction.lt ⟨100000, 1⟩ ⟨6481492408, 625⟩) = true := by
  decide +kernel

theorem cap_guard11_E2_reconstruct : (Fraction.allEq (bernstein cap_guard11_E2_numerator ⟨29, 20⟩ ⟨8, 5⟩ 4) cap_guard11_E2_controls) = true := by
  decide +kernel

def cap_guard11_H_numerator : List Fraction := [⟨7631067857968872, 1⟩, ⟨-3845172700945717, 1⟩, ⟨591293067394560, 1⟩, ⟨-121564177432576, 1⟩]
def cap_guard11_H_denominator : List Fraction := [⟨7832464697327616, 1⟩, ⟨1528731902410752, 1⟩, ⟨37220186587136, 1⟩]
def cap_guard11_H_controls : List Fraction := [⟨8245370547127981, 4⟩, ⟨26980355003782993, 18⟩, ⟨33521499729130415, 36⟩, ⟨9016520053206125, 27⟩]

theorem cap_guard11_H_coefficient_0 : (Fraction.lt ⟨100000000000000, 1⟩ ⟨8245370547127981, 4⟩) = true := by
  decide +kernel

theorem cap_guard11_H_coefficient_1 : (Fraction.lt ⟨100000000000000, 1⟩ ⟨26980355003782993, 18⟩) = true := by
  decide +kernel

theorem cap_guard11_H_coefficient_2 : (Fraction.lt ⟨100000000000000, 1⟩ ⟨33521499729130415, 36⟩) = true := by
  decide +kernel

theorem cap_guard11_H_coefficient_3 : (Fraction.lt ⟨100000000000000, 1⟩ ⟨9016520053206125, 27⟩) = true := by
  decide +kernel

theorem cap_guard11_H_reconstruct : (Fraction.allEq (bernstein cap_guard11_H_numerator ⟨7, 4⟩ ⟨7, 3⟩ 3) cap_guard11_H_controls) = true := by
  decide +kernel

end F4Heavy.Finite
