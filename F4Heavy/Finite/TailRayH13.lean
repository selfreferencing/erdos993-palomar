module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite

def tail_ray_H_13_numerator_power : List Fraction := [⟨-70856169534722063474246246400000000, 1⟩, ⟨-405202629234290804127998392320000000, 1⟩, ⟨-813257733719541555574885328917800960, 1⟩, ⟨-399530287996146175254159750447207168, 1⟩, ⟨913405909097566921121880625615711200, 1⟩, ⟨1522894148949179843737961912678950776, 1⟩, ⟨723849237347776587704406034965541485, 1⟩, ⟨-98134461264104992091446466417846482, 1⟩, ⟨-145627739524588272291575362184660480, 1⟩, ⟨-11012274144102210329012785245976576, 1⟩, ⟨1325450841286924845513523200000000, 1⟩, ⟨124171465757944489810329600000000, 1⟩]
def tail_ray_H_13_numerator_controls : List Fraction := [Fraction.mul ⟨1, 161243136⟩ (Fraction.mul ⟨4824246981648869123579638875558614644873102305, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨1, 161243136⟩ (Fraction.mul ⟨59722029473093955768134162470379197018024294974, 1⟩ ⟨1, 11⟩), Fraction.mul ⟨1, 161243136⟩ (Fraction.mul ⟨333683664230187371071582324462789597245945806190, 1⟩ ⟨1, 55⟩), Fraction.mul ⟨1, 161243136⟩ (Fraction.mul ⟨1109978344357254268545535476538607878010466491136, 1⟩ ⟨1, 165⟩), Fraction.mul ⟨1, 161243136⟩ (Fraction.mul ⟨2440377362688180049360702956468711542173850045385, 1⟩ ⟨1, 330⟩), Fraction.mul ⟨1, 161243136⟩ (Fraction.mul ⟨3719342149845027807991277324842019455315025693754, 1⟩ ⟨1, 462⟩), Fraction.mul ⟨1, 161243136⟩ (Fraction.mul ⟨4003831893642495560528434414382223587971140395328, 1⟩ ⟨1, 462⟩), Fraction.mul ⟨1, 161243136⟩ (Fraction.mul ⟨3038259981811605724711243536827972149174949344224, 1⟩ ⟨1, 330⟩), Fraction.mul ⟨1, 161243136⟩ (Fraction.mul ⟨1588358509595221595500103041472904696504429600000, 1⟩ ⟨1, 165⟩), Fraction.mul ⟨1, 161243136⟩ (Fraction.mul ⟨542687512840987012129892336549266423180843136512, 1⟩ ⟨1, 55⟩), Fraction.mul ⟨1, 161243136⟩ (Fraction.mul ⟨108418673635664408889757722047874565170555215872, 1⟩ ⟨1, 11⟩), Fraction.mul ⟨1, 161243136⟩ (Fraction.mul ⟨9504332498711975944546966300275772653085204480, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_H_13_numerator_coefficient_0 : (Fraction.positive ⟨4824246981648869123579638875558614644873102305, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_13_numerator_coefficient_1 : (Fraction.positive ⟨59722029473093955768134162470379197018024294974, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_13_numerator_coefficient_2 : (Fraction.positive ⟨333683664230187371071582324462789597245945806190, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_13_numerator_coefficient_3 : (Fraction.positive ⟨1109978344357254268545535476538607878010466491136, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_13_numerator_coefficient_4 : (Fraction.positive ⟨2440377362688180049360702956468711542173850045385, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_13_numerator_coefficient_5 : (Fraction.positive ⟨3719342149845027807991277324842019455315025693754, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_13_numerator_coefficient_6 : (Fraction.positive ⟨4003831893642495560528434414382223587971140395328, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_13_numerator_coefficient_7 : (Fraction.positive ⟨3038259981811605724711243536827972149174949344224, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_13_numerator_coefficient_8 : (Fraction.positive ⟨1588358509595221595500103041472904696504429600000, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_13_numerator_coefficient_9 : (Fraction.positive ⟨542687512840987012129892336549266423180843136512, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_13_numerator_coefficient_10 : (Fraction.positive ⟨108418673635664408889757722047874565170555215872, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_13_numerator_coefficient_11 : (Fraction.positive ⟨9504332498711975944546966300275772653085204480, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_13_numerator_scale_positive : (Fraction.positive ⟨1, 161243136⟩) = true := by
  decide +kernel

theorem tail_ray_H_13_numerator_reconstruct : (Fraction.allEq (bernstein tail_ray_H_13_numerator_power ⟨7, 4⟩ ⟨7, 3⟩ 11) tail_ray_H_13_numerator_controls) = true := by
  decide +kernel

def tail_ray_H_13_denominator_power : List Fraction := [⟨0, 1⟩, ⟨-36363092086058797130946969600000000, 1⟩, ⟨-179560803862043400758970286080000000, 1⟩, ⟨-304692319318986136846514257920000000, 1⟩, ⟨-93519304820224871296275578880000000, 1⟩, ⟨352395201824050328082296340480000000, 1⟩, ⟨492179573699683224601912934400000000, 1⟩, ⟨250508319976691103726305280000000000, 1⟩, ⟨42425516589014330093076480000000000, 1⟩]
def tail_ray_H_13_denominator_controls : List Fraction := [Fraction.mul ⟨4067352002560000000, 27⟩ (Fraction.mul ⟨219863612121748297785, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨4067352002560000000, 27⟩ (Fraction.mul ⟨2250508651596708609213, 1⟩ ⟨1, 8⟩), Fraction.mul ⟨4067352002560000000, 27⟩ (Fraction.mul ⟨10060655018976281084400, 1⟩ ⟨1, 28⟩), Fraction.mul ⟨4067352002560000000, 27⟩ (Fraction.mul ⟨25657816166982240442236, 1⟩ ⟨1, 56⟩), Fraction.mul ⟨4067352002560000000, 27⟩ (Fraction.mul ⟨40833809081871266243664, 1⟩ ⟨1, 70⟩), Fraction.mul ⟨4067352002560000000, 27⟩ (Fraction.mul ⟨41530142301265742447232, 1⟩ ⟨1, 56⟩), Fraction.mul ⟨4067352002560000000, 27⟩ (Fraction.mul ⟨26362292204257776990720, 1⟩ ⟨1, 28⟩), Fraction.mul ⟨4067352002560000000, 27⟩ (Fraction.mul ⟨9549720287179716086784, 1⟩ ⟨1, 8⟩), Fraction.mul ⟨4067352002560000000, 27⟩ (Fraction.mul ⟨1511571265636576464896, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_H_13_denominator_coefficient_0 : (Fraction.positive ⟨219863612121748297785, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_13_denominator_coefficient_1 : (Fraction.positive ⟨2250508651596708609213, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_13_denominator_coefficient_2 : (Fraction.positive ⟨10060655018976281084400, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_13_denominator_coefficient_3 : (Fraction.positive ⟨25657816166982240442236, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_13_denominator_coefficient_4 : (Fraction.positive ⟨40833809081871266243664, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_13_denominator_coefficient_5 : (Fraction.positive ⟨41530142301265742447232, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_13_denominator_coefficient_6 : (Fraction.positive ⟨26362292204257776990720, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_13_denominator_coefficient_7 : (Fraction.positive ⟨9549720287179716086784, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_13_denominator_coefficient_8 : (Fraction.positive ⟨1511571265636576464896, 1⟩) = true := by
  decide +kernel

theorem tail_ray_H_13_denominator_scale_positive : (Fraction.positive ⟨4067352002560000000, 27⟩) = true := by
  decide +kernel

theorem tail_ray_H_13_denominator_reconstruct : (Fraction.allEq (bernstein tail_ray_H_13_denominator_power ⟨7, 4⟩ ⟨7, 3⟩ 8) tail_ray_H_13_denominator_controls) = true := by
  decide +kernel

end F4Heavy.Finite
