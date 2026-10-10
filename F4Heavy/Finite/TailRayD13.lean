module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite

def tail_ray_D_13_numerator_power : List Fraction := [⟨-66744310772531238587596800000000, 1⟩, ⟨2061096123493470130038374400000000, 1⟩, ⟨24605053059039516744500358335692800, 1⟩, ⟨76997825850112379321071496129445888, 1⟩, ⟨106097682002752907946360052175766528, 1⟩, ⟨66533362927942755627487679610280320, 1⟩, ⟨4599020432447228602818611967036360, 1⟩, ⟨-13199232737829159383424086022854205, 1⟩, ⟨3163378269952555037864198813068128, 1⟩, ⟨5804895878638200204810362407738688, 1⟩, ⟨2037598260605572715215552000000000, 1⟩, ⟨2384711628898108761251840000000000, 1⟩]
def tail_ray_D_13_numerator_controls : List Fraction := [Fraction.mul ⟨1, 250000000⟩ (Fraction.mul ⟨30545629882545185163975878499079841787150336, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨1, 250000000⟩ (Fraction.mul ⟨404409245907078887309101594881958873102811136, 1⟩ ⟨1, 11⟩), Fraction.mul ⟨1, 250000000⟩ (Fraction.mul ⟨2426265724598565320063244683274427891793428480, 1⟩ ⟨1, 55⟩), Fraction.mul ⟨1, 250000000⟩ (Fraction.mul ⟨8709359345694902066807977998773876678770544640, 1⟩ ⟨1, 165⟩), Fraction.mul ⟨1, 250000000⟩ (Fraction.mul ⟨20790663909008632247563748117895886360525217280, 1⟩ ⟨1, 330⟩), Fraction.mul ⟨1, 250000000⟩ (Fraction.mul ⟨34670972233909385679273000308958450969470980032, 1⟩ ⟨1, 462⟩), Fraction.mul ⟨1, 250000000⟩ (Fraction.mul ⟨41238603083396687134855617567072082175810654712, 1⟩ ⟨1, 462⟩), Fraction.mul ⟨1, 250000000⟩ (Fraction.mul ⟨35011261103626983393334407855856698451015173255, 1⟩ ⟨1, 330⟩), Fraction.mul ⟨1, 250000000⟩ (Fraction.mul ⟨20812402465362388977573301726608343594444930140, 1⟩ ⟨1, 165⟩), Fraction.mul ⟨1, 250000000⟩ (Fraction.mul ⟨8260179953666301755847312318624379375626353130, 1⟩ ⟨1, 55⟩), Fraction.mul ⟨1, 250000000⟩ (Fraction.mul ⟨1972946944565146364845874127692360061467652996, 1⟩ ⟨1, 11⟩), Fraction.mul ⟨1, 250000000⟩ (Fraction.mul ⟨215246165111807209470129168946815577843171751, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_D_13_numerator_coefficient_0 : (Fraction.positive ⟨30545629882545185163975878499079841787150336, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_13_numerator_coefficient_1 : (Fraction.positive ⟨404409245907078887309101594881958873102811136, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_13_numerator_coefficient_2 : (Fraction.positive ⟨2426265724598565320063244683274427891793428480, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_13_numerator_coefficient_3 : (Fraction.positive ⟨8709359345694902066807977998773876678770544640, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_13_numerator_coefficient_4 : (Fraction.positive ⟨20790663909008632247563748117895886360525217280, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_13_numerator_coefficient_5 : (Fraction.positive ⟨34670972233909385679273000308958450969470980032, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_13_numerator_coefficient_6 : (Fraction.positive ⟨41238603083396687134855617567072082175810654712, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_13_numerator_coefficient_7 : (Fraction.positive ⟨35011261103626983393334407855856698451015173255, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_13_numerator_coefficient_8 : (Fraction.positive ⟨20812402465362388977573301726608343594444930140, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_13_numerator_coefficient_9 : (Fraction.positive ⟨8260179953666301755847312318624379375626353130, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_13_numerator_coefficient_10 : (Fraction.positive ⟨1972946944565146364845874127692360061467652996, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_13_numerator_coefficient_11 : (Fraction.positive ⟨215246165111807209470129168946815577843171751, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_13_numerator_scale_positive : (Fraction.positive ⟨1, 250000000⟩) = true := by
  decide +kernel

theorem tail_ray_D_13_numerator_reconstruct : (Fraction.allEq (bernstein tail_ray_D_13_numerator_power ⟨4, 5⟩ ⟨13, 10⟩ 11) tail_ray_D_13_numerator_controls) = true := by
  decide +kernel

def tail_ray_D_13_denominator_power : List Fraction := [⟨0, 1⟩, ⟨-3201577420522310888985722880000000, 1⟩, ⟨112350224883851146980092805120000000, 1⟩, ⟨684952895397624135187798425600000000, 1⟩, ⟨1681325850284962202564060774400000000, 1⟩, ⟨2277256924165525095905545420800000000, 1⟩, ⟨1813818676876392004615636254720000000, 1⟩, ⟨775284692135964514266403307520000000, 1⟩, ⟨124414805048219634013883596800000000, 1⟩]
def tail_ray_D_13_denominator_controls : List Fraction := [Fraction.mul ⟨740146412519424, 1⟩ (Fraction.mul ⟨3396443389006325219328, 1⟩ ⟨1, 1⟩), Fraction.mul ⟨740146412519424, 1⟩ (Fraction.mul ⟨37167100191633166434304, 1⟩ ⟨1, 8⟩), Fraction.mul ⟨740146412519424, 1⟩ (Fraction.mul ⟨177656102012939076358144, 1⟩ ⟨1, 28⟩), Fraction.mul ⟨740146412519424, 1⟩ (Fraction.mul ⟨484513513335499991502848, 1⟩ ⟨1, 56⟩), Fraction.mul ⟨740146412519424, 1⟩ (Fraction.mul ⟨824679443704846426989760, 1⟩ ⟨1, 70⟩), Fraction.mul ⟨740146412519424, 1⟩ (Fraction.mul ⟨897111299333486560475168, 1⟩ ⟨1, 56⟩), Fraction.mul ⟨740146412519424, 1⟩ (Fraction.mul ⟨609136539626701832606839, 1⟩ ⟨1, 28⟩), Fraction.mul ⟨740146412519424, 1⟩ (Fraction.mul ⟨236044435382539970580709, 1⟩ ⟨1, 8⟩), Fraction.mul ⟨740146412519424, 1⟩ (Fraction.mul ⟨39968476130199477818958, 1⟩ ⟨1, 1⟩)]

theorem tail_ray_D_13_denominator_coefficient_0 : (Fraction.positive ⟨3396443389006325219328, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_13_denominator_coefficient_1 : (Fraction.positive ⟨37167100191633166434304, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_13_denominator_coefficient_2 : (Fraction.positive ⟨177656102012939076358144, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_13_denominator_coefficient_3 : (Fraction.positive ⟨484513513335499991502848, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_13_denominator_coefficient_4 : (Fraction.positive ⟨824679443704846426989760, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_13_denominator_coefficient_5 : (Fraction.positive ⟨897111299333486560475168, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_13_denominator_coefficient_6 : (Fraction.positive ⟨609136539626701832606839, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_13_denominator_coefficient_7 : (Fraction.positive ⟨236044435382539970580709, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_13_denominator_coefficient_8 : (Fraction.positive ⟨39968476130199477818958, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_13_denominator_scale_positive : (Fraction.positive ⟨740146412519424, 1⟩) = true := by
  decide +kernel

theorem tail_ray_D_13_denominator_reconstruct : (Fraction.allEq (bernstein tail_ray_D_13_denominator_power ⟨4, 5⟩ ⟨13, 10⟩ 8) tail_ray_D_13_denominator_controls) = true := by
  decide +kernel

end F4Heavy.Finite
