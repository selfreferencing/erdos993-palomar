module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite

def cap_slope_D_4_numerator : List Fraction := [⟨-1148733714428832, 1⟩, ⟨-23016156617902370, 1⟩, ⟨29910233109573627, 1⟩, ⟨-10096689007453308, 1⟩, ⟨4784370585316364, 1⟩, ⟨14582858692134912, 1⟩, ⟨3664838570803200, 1⟩]
def cap_slope_D_4_denominator : List Fraction := [⟨-381846080716800, 1⟩, ⟨13913315868672000, 1⟩, ⟨79989733903564800, 1⟩, ⟨146749323529420800, 1⟩, ⟨102894281529753600, 1⟩, ⟨23877011688652800, 1⟩]
def cap_slope_D_4_controls : List Fraction := [⟨6594656812029013448, 3125⟩, ⟨121324229685627284663, 18750⟩, ⟨481930516511939812151, 37500⟩, ⟨552582546818266227859, 25000⟩, ⟨443576413340457804017, 12500⟩, ⟨342731791431463779771, 6250⟩, ⟨258735565742853649923, 3125⟩]

theorem cap_slope_D_4_coefficient_0 : (Fraction.lt ⟨1000000000000000, 1⟩ ⟨6594656812029013448, 3125⟩) = true := by
  decide +kernel

theorem cap_slope_D_4_coefficient_1 : (Fraction.lt ⟨1000000000000000, 1⟩ ⟨121324229685627284663, 18750⟩) = true := by
  decide +kernel

theorem cap_slope_D_4_coefficient_2 : (Fraction.lt ⟨1000000000000000, 1⟩ ⟨481930516511939812151, 37500⟩) = true := by
  decide +kernel

theorem cap_slope_D_4_coefficient_3 : (Fraction.lt ⟨1000000000000000, 1⟩ ⟨552582546818266227859, 25000⟩) = true := by
  decide +kernel

theorem cap_slope_D_4_coefficient_4 : (Fraction.lt ⟨1000000000000000, 1⟩ ⟨443576413340457804017, 12500⟩) = true := by
  decide +kernel

theorem cap_slope_D_4_coefficient_5 : (Fraction.lt ⟨1000000000000000, 1⟩ ⟨342731791431463779771, 6250⟩) = true := by
  decide +kernel

theorem cap_slope_D_4_coefficient_6 : (Fraction.lt ⟨1000000000000000, 1⟩ ⟨258735565742853649923, 3125⟩) = true := by
  decide +kernel

theorem cap_slope_D_4_reconstruct : (Fraction.allEq (bernstein cap_slope_D_4_numerator ⟨4, 5⟩ ⟨13, 10⟩ 6) cap_slope_D_4_controls) = true := by
  decide +kernel

def cap_slope_D_5_numerator : List Fraction := [⟨-574366857214416, 1⟩, ⟨-11467677658699006, 1⟩, ⟨13276996826532813, 1⟩, ⟨-5477529286754532, 1⟩, ⟨9691781899280404, 1⟩, ⟨9730699775391744, 1⟩, ⟨2221831913472000, 1⟩]
def cap_slope_D_5_denominator : List Fraction := [⟨-190923040358400, 1⟩, ⟨7004388694425600, 1⟩, ⟨38219904398131200, 1⟩, ⟨64707166942003200, 1⟩, ⟨39604096440729600, 1⟩, ⟨7959003896217600, 1⟩]
def cap_slope_D_5_controls : List Fraction := [⟨11515698323312135176, 3125⟩, ⟨136913256801360908281, 18750⟩, ⟨472476826799408251537, 37500⟩, ⟨506701870815401701733, 25000⟩, ⟨391132238259564249479, 12500⟩, ⟨294043847706903078477, 6250⟩, ⟨217050339551036012901, 3125⟩]

theorem cap_slope_D_5_coefficient_0 : (Fraction.lt ⟨1000000000000000, 1⟩ ⟨11515698323312135176, 3125⟩) = true := by
  decide +kernel

theorem cap_slope_D_5_coefficient_1 : (Fraction.lt ⟨1000000000000000, 1⟩ ⟨136913256801360908281, 18750⟩) = true := by
  decide +kernel

theorem cap_slope_D_5_coefficient_2 : (Fraction.lt ⟨1000000000000000, 1⟩ ⟨472476826799408251537, 37500⟩) = true := by
  decide +kernel

theorem cap_slope_D_5_coefficient_3 : (Fraction.lt ⟨1000000000000000, 1⟩ ⟨506701870815401701733, 25000⟩) = true := by
  decide +kernel

theorem cap_slope_D_5_coefficient_4 : (Fraction.lt ⟨1000000000000000, 1⟩ ⟨391132238259564249479, 12500⟩) = true := by
  decide +kernel

theorem cap_slope_D_5_coefficient_5 : (Fraction.lt ⟨1000000000000000, 1⟩ ⟨294043847706903078477, 6250⟩) = true := by
  decide +kernel

theorem cap_slope_D_5_coefficient_6 : (Fraction.lt ⟨1000000000000000, 1⟩ ⟨217050339551036012901, 3125⟩) = true := by
  decide +kernel

theorem cap_slope_D_5_reconstruct : (Fraction.allEq (bernstein cap_slope_D_5_numerator ⟨4, 5⟩ ⟨13, 10⟩ 6) cap_slope_D_5_controls) = true := by
  decide +kernel

def cap_slope_E1_4_numerator : List Fraction := [⟨-29538998904420, 1⟩, ⟨-70960785568724, 1⟩, ⟨11960627278009, 1⟩, ⟨45810335197060, 1⟩, ⟨45561486650724, 1⟩, ⟨-10678983829056, 1⟩, ⟨-12916291449600, 1⟩]
def cap_slope_E1_4_denominator : List Fraction := [⟨-8174174208000, 1⟩, ⟨-32468081049600, 1⟩, ⟨-21789632102400, 1⟩, ⟨44802244608000, 1⟩, ⟨55639906713600, 1⟩, ⟨15669500313600, 1⟩]
def cap_slope_E1_4_controls : List Fraction := [⟨85012866134932581, 3125⟩, ⟨387721666054462179, 12500⟩, ⟨1731415757850962559, 50000⟩, ⟨7591469133239185761, 200000⟩, ⟨327315616003290351, 8000⟩, ⟨8679199083129524151, 200000⟩, ⟨9056702774935450341, 200000⟩]

theorem cap_slope_E1_4_coefficient_0 : (Fraction.lt ⟨10000000000000, 1⟩ ⟨85012866134932581, 3125⟩) = true := by
  decide +kernel

theorem cap_slope_E1_4_coefficient_1 : (Fraction.lt ⟨10000000000000, 1⟩ ⟨387721666054462179, 12500⟩) = true := by
  decide +kernel

theorem cap_slope_E1_4_coefficient_2 : (Fraction.lt ⟨10000000000000, 1⟩ ⟨1731415757850962559, 50000⟩) = true := by
  decide +kernel

theorem cap_slope_E1_4_coefficient_3 : (Fraction.lt ⟨10000000000000, 1⟩ ⟨7591469133239185761, 200000⟩) = true := by
  decide +kernel

theorem cap_slope_E1_4_coefficient_4 : (Fraction.lt ⟨10000000000000, 1⟩ ⟨327315616003290351, 8000⟩) = true := by
  decide +kernel

theorem cap_slope_E1_4_coefficient_5 : (Fraction.lt ⟨10000000000000, 1⟩ ⟨8679199083129524151, 200000⟩) = true := by
  decide +kernel

theorem cap_slope_E1_4_coefficient_6 : (Fraction.lt ⟨10000000000000, 1⟩ ⟨9056702774935450341, 200000⟩) = true := by
  decide +kernel

theorem cap_slope_E1_4_reconstruct : (Fraction.allEq (bernstein cap_slope_E1_4_numerator ⟨13, 10⟩ ⟨29, 20⟩ 6) cap_slope_E1_4_controls) = true := by
  decide +kernel

def cap_slope_E1_5_numerator : List Fraction := [⟨-14769499452210, 1⟩, ⟨-33044762632747, 1⟩, ⟨9180877910075, 1⟩, ⟨16313034178496, 1⟩, ⟨16718601964860, 1⟩, ⟨-2722788833472, 1⟩, ⟨-2982104966400, 1⟩]
def cap_slope_E1_5_denominator : List Fraction := [⟨-4087087104000, 1⟩, ⟨-15212268748800, 1⟩, ⟨-7602634752000, 1⟩, ⟨22655690342400, 1⟩, ⟨22028746752000, 1⟩, ⟨5223166771200, 1⟩]
def cap_slope_E1_5_controls : List Fraction := [⟨52731726628158117, 3125⟩, ⟨246907784447583153, 12500⟩, ⟨1135660960620671679, 50000⟩, ⟨514869765992110683, 20000⟩, ⟨5765678397998640429, 200000⟩, ⟨6389995794010303167, 200000⟩, ⟨7017404364422035047, 200000⟩]

theorem cap_slope_E1_5_coefficient_0 : (Fraction.lt ⟨10000000000000, 1⟩ ⟨52731726628158117, 3125⟩) = true := by
  decide +kernel

theorem cap_slope_E1_5_coefficient_1 : (Fraction.lt ⟨10000000000000, 1⟩ ⟨246907784447583153, 12500⟩) = true := by
  decide +kernel

theorem cap_slope_E1_5_coefficient_2 : (Fraction.lt ⟨10000000000000, 1⟩ ⟨1135660960620671679, 50000⟩) = true := by
  decide +kernel

theorem cap_slope_E1_5_coefficient_3 : (Fraction.lt ⟨10000000000000, 1⟩ ⟨514869765992110683, 20000⟩) = true := by
  decide +kernel

theorem cap_slope_E1_5_coefficient_4 : (Fraction.lt ⟨10000000000000, 1⟩ ⟨5765678397998640429, 200000⟩) = true := by
  decide +kernel

theorem cap_slope_E1_5_coefficient_5 : (Fraction.lt ⟨10000000000000, 1⟩ ⟨6389995794010303167, 200000⟩) = true := by
  decide +kernel

theorem cap_slope_E1_5_coefficient_6 : (Fraction.lt ⟨10000000000000, 1⟩ ⟨7017404364422035047, 200000⟩) = true := by
  decide +kernel

theorem cap_slope_E1_5_reconstruct : (Fraction.allEq (bernstein cap_slope_E1_5_numerator ⟨13, 10⟩ ⟨29, 20⟩ 6) cap_slope_E1_5_controls) = true := by
  decide +kernel

def cap_slope_E2_4_numerator : List Fraction := [⟨2479038484166496, 1⟩, ⟨2947083442913358, 1⟩, ⟨19522741485176851, 1⟩, ⟨10358631708164004, 1⟩, ⟨1008767131130220, 1⟩, ⟨-3755026683864064, 1⟩, ⟨-1398749955686400, 1⟩]
def cap_slope_E2_4_denominator : List Fraction := [⟨666506782310400, 1⟩, ⟨6603777717043200, 1⟩, ⟨22547740911206400, 1⟩, ⟨33438079490457600, 1⟩, ⟨21179771387904000, 1⟩, ⟨4656925664870400, 1⟩]
def cap_slope_E2_4_controls : List Fraction := [⟨9353770783008285333159, 200000⟩, ⟨9355831922957024841759, 200000⟩, ⟨9318918251120103208053, 200000⟩, ⟨9238033915761169787517, 200000⟩, ⟨455385417471787855653, 10000⟩, ⟨557622247561456686417, 12500⟩, ⟨135534885015499277328, 3125⟩]

theorem cap_slope_E2_4_coefficient_0 : (Fraction.lt ⟨10000000000000000, 1⟩ ⟨9353770783008285333159, 200000⟩) = true := by
  decide +kernel

theorem cap_slope_E2_4_coefficient_1 : (Fraction.lt ⟨10000000000000000, 1⟩ ⟨9355831922957024841759, 200000⟩) = true := by
  decide +kernel

theorem cap_slope_E2_4_coefficient_2 : (Fraction.lt ⟨10000000000000000, 1⟩ ⟨9318918251120103208053, 200000⟩) = true := by
  decide +kernel

theorem cap_slope_E2_4_coefficient_3 : (Fraction.lt ⟨10000000000000000, 1⟩ ⟨9238033915761169787517, 200000⟩) = true := by
  decide +kernel

theorem cap_slope_E2_4_coefficient_4 : (Fraction.lt ⟨10000000000000000, 1⟩ ⟨455385417471787855653, 10000⟩) = true := by
  decide +kernel

theorem cap_slope_E2_4_coefficient_5 : (Fraction.lt ⟨10000000000000000, 1⟩ ⟨557622247561456686417, 12500⟩) = true := by
  decide +kernel

theorem cap_slope_E2_4_coefficient_6 : (Fraction.lt ⟨10000000000000000, 1⟩ ⟨135534885015499277328, 3125⟩) = true := by
  decide +kernel

theorem cap_slope_E2_4_reconstruct : (Fraction.allEq (bernstein cap_slope_E2_4_numerator ⟨29, 20⟩ ⟨8, 5⟩ 6) cap_slope_E2_4_controls) = true := by
  decide +kernel

def cap_slope_E2_5_numerator : List Fraction := [⟨1239519242083248, 1⟩, ⟨1345629417105042, 1⟩, ⟨8927262494854901, 1⟩, ⟨4171962352718844, 1⟩, ⟨1158701554468788, 1⟩, ⟨-973073631362048, 1⟩, ⟨-314057298739200, 1⟩]
def cap_slope_E2_5_denominator : List Fraction := [⟨333253391155200, 1⟩, ⟨3218575510732800, 1⟩, ⟨10510883251814400, 1⟩, ⟨14472812534169600, 1⟩, ⟨8094796165939200, 1⟩, ⟨1552308554956800, 1⟩]
def cap_slope_E2_5_controls : List Fraction := [⟨6129003964666953220353, 200000⟩, ⟨6299471946468778327593, 200000⟩, ⟨6467300698990305375747, 200000⟩, ⟨6631521080843772642123, 200000⟩, ⟨1697764324039294530591, 50000⟩, ⟨434044844709442154559, 12500⟩, ⟨110799746569587191616, 3125⟩]

theorem cap_slope_E2_5_coefficient_0 : (Fraction.lt ⟨10000000000000000, 1⟩ ⟨6129003964666953220353, 200000⟩) = true := by
  decide +kernel

theorem cap_slope_E2_5_coefficient_1 : (Fraction.lt ⟨10000000000000000, 1⟩ ⟨6299471946468778327593, 200000⟩) = true := by
  decide +kernel

theorem cap_slope_E2_5_coefficient_2 : (Fraction.lt ⟨10000000000000000, 1⟩ ⟨6467300698990305375747, 200000⟩) = true := by
  decide +kernel

theorem cap_slope_E2_5_coefficient_3 : (Fraction.lt ⟨10000000000000000, 1⟩ ⟨6631521080843772642123, 200000⟩) = true := by
  decide +kernel

theorem cap_slope_E2_5_coefficient_4 : (Fraction.lt ⟨10000000000000000, 1⟩ ⟨1697764324039294530591, 50000⟩) = true := by
  decide +kernel

theorem cap_slope_E2_5_coefficient_5 : (Fraction.lt ⟨10000000000000000, 1⟩ ⟨434044844709442154559, 12500⟩) = true := by
  decide +kernel

theorem cap_slope_E2_5_coefficient_6 : (Fraction.lt ⟨10000000000000000, 1⟩ ⟨110799746569587191616, 3125⟩) = true := by
  decide +kernel

theorem cap_slope_E2_5_reconstruct : (Fraction.allEq (bernstein cap_slope_E2_5_numerator ⟨29, 20⟩ ⟨8, 5⟩ 6) cap_slope_E2_5_controls) = true := by
  decide +kernel

def cap_slope_H_4_numerator : List Fraction := [⟨-79375864812767140, 1⟩, ⟨-285683715861754252, 1⟩, ⟨-107091597381743923, 1⟩, ⟨201755969045265220, 1⟩, ⟨112326345493290292, 1⟩, ⟨-22752255854655488, 1⟩, ⟨-13148243381452800, 1⟩]
def cap_slope_H_4_denominator : List Fraction := [⟨-14208976551936000, 1⟩, ⟨-54607490108620800, 1⟩, ⟨-28263562031923200, 1⟩, ⟨95044497309696000, 1⟩, ⟨108619174300876800, 1⟩, ⟨29984455183564800, 1⟩]
def cap_slope_H_4_controls : List Fraction := [⟨30489815056934967165, 64⟩, ⟨38201318862859065429, 64⟩, ⟨45835878870284776103, 64⟩, ⟨2370748974279002823731, 2880⟩, ⟨649036962542613032467, 720⟩, ⟨2704312944592315173053, 2916⟩, ⟨23436788700855312463, 27⟩]

theorem cap_slope_H_4_coefficient_0 : (Fraction.lt ⟨100000000000000000, 1⟩ ⟨30489815056934967165, 64⟩) = true := by
  decide +kernel

theorem cap_slope_H_4_coefficient_1 : (Fraction.lt ⟨100000000000000000, 1⟩ ⟨38201318862859065429, 64⟩) = true := by
  decide +kernel

theorem cap_slope_H_4_coefficient_2 : (Fraction.lt ⟨100000000000000000, 1⟩ ⟨45835878870284776103, 64⟩) = true := by
  decide +kernel

theorem cap_slope_H_4_coefficient_3 : (Fraction.lt ⟨100000000000000000, 1⟩ ⟨2370748974279002823731, 2880⟩) = true := by
  decide +kernel

theorem cap_slope_H_4_coefficient_4 : (Fraction.lt ⟨100000000000000000, 1⟩ ⟨649036962542613032467, 720⟩) = true := by
  decide +kernel

theorem cap_slope_H_4_coefficient_5 : (Fraction.lt ⟨100000000000000000, 1⟩ ⟨2704312944592315173053, 2916⟩) = true := by
  decide +kernel

theorem cap_slope_H_4_coefficient_6 : (Fraction.lt ⟨100000000000000000, 1⟩ ⟨23436788700855312463, 27⟩) = true := by
  decide +kernel

theorem cap_slope_H_4_reconstruct : (Fraction.allEq (bernstein cap_slope_H_4_numerator ⟨7, 4⟩ ⟨7, 3⟩ 6) cap_slope_H_4_controls) = true := by
  decide +kernel

def cap_slope_H_5_numerator : List Fraction := [⟨-39687932406383570, 1⟩, ⟨-137397526765319171, 1⟩, ⟨-45480989962953185, 1⟩, ⟨86308175661120608, 1⟩, ⟨39961317904693580, 1⟩, ⟨-6207070068852736, 1⟩, ⟨-2805399846912000, 1⟩]
def cap_slope_H_5_denominator : List Fraction := [⟨-7104488275968000, 1⟩, ⟨-25527622985318400, 1⟩, ⟨-8637936304128000, 1⟩, ⟨46934810374963200, 1⟩, ⟨42869603696640000, 1⟩, ⟨9994818394521600, 1⟩]
def cap_slope_H_5_controls : List Fraction := [⟨15070451351184482175, 64⟩, ⟨19959231880976980185, 64⟩, ⟨381749084156811547483, 960⟩, ⟨44245305224530772027, 90⟩, ⟨3832251544943964572257, 6480⟩, ⟨4042459472898301024667, 5832⟩, ⟨192215073984721702462, 243⟩]

theorem cap_slope_H_5_coefficient_0 : (Fraction.lt ⟨100000000000000000, 1⟩ ⟨15070451351184482175, 64⟩) = true := by
  decide +kernel

theorem cap_slope_H_5_coefficient_1 : (Fraction.lt ⟨100000000000000000, 1⟩ ⟨19959231880976980185, 64⟩) = true := by
  decide +kernel

theorem cap_slope_H_5_coefficient_2 : (Fraction.lt ⟨100000000000000000, 1⟩ ⟨381749084156811547483, 960⟩) = true := by
  decide +kernel

theorem cap_slope_H_5_coefficient_3 : (Fraction.lt ⟨100000000000000000, 1⟩ ⟨44245305224530772027, 90⟩) = true := by
  decide +kernel

theorem cap_slope_H_5_coefficient_4 : (Fraction.lt ⟨100000000000000000, 1⟩ ⟨3832251544943964572257, 6480⟩) = true := by
  decide +kernel

theorem cap_slope_H_5_coefficient_5 : (Fraction.lt ⟨100000000000000000, 1⟩ ⟨4042459472898301024667, 5832⟩) = true := by
  decide +kernel

theorem cap_slope_H_5_coefficient_6 : (Fraction.lt ⟨100000000000000000, 1⟩ ⟨192215073984721702462, 243⟩) = true := by
  decide +kernel

theorem cap_slope_H_5_reconstruct : (Fraction.allEq (bernstein cap_slope_H_5_numerator ⟨7, 4⟩ ⟨7, 3⟩ 6) cap_slope_H_5_controls) = true := by
  decide +kernel

def cap_slope_H_6_numerator : List Fraction := [⟨-1693842000, 1⟩, ⟨6831556822, 1⟩, ⟨8577618079, 1⟩, ⟨-3596077800, 1⟩, ⟨-399329280, 1⟩]
def cap_slope_H_6_denominator : List Fraction := [⟨0, 1⟩, ⟨5033164800, 1⟩, ⟨10066329600, 1⟩]
def cap_slope_H_6_controls : List Fraction := [⟨216197383457, 16⟩, ⟨51280632289, 4⟩, ⟨9614240613511, 864⟩, ⟨292229178671, 36⟩, ⟨10279220471, 3⟩]

theorem cap_slope_H_6_coefficient_0 : (Fraction.lt ⟨1000000000, 1⟩ ⟨216197383457, 16⟩) = true := by
  decide +kernel

theorem cap_slope_H_6_coefficient_1 : (Fraction.lt ⟨1000000000, 1⟩ ⟨51280632289, 4⟩) = true := by
  decide +kernel

theorem cap_slope_H_6_coefficient_2 : (Fraction.lt ⟨1000000000, 1⟩ ⟨9614240613511, 864⟩) = true := by
  decide +kernel

theorem cap_slope_H_6_coefficient_3 : (Fraction.lt ⟨1000000000, 1⟩ ⟨292229178671, 36⟩) = true := by
  decide +kernel

theorem cap_slope_H_6_coefficient_4 : (Fraction.lt ⟨1000000000, 1⟩ ⟨10279220471, 3⟩) = true := by
  decide +kernel

theorem cap_slope_H_6_reconstruct : (Fraction.allEq (bernstein cap_slope_H_6_numerator ⟨7, 4⟩ ⟨7, 3⟩ 4) cap_slope_H_6_controls) = true := by
  decide +kernel

def cap_slope_H_7_numerator : List Fraction := [⟨5646140, 1⟩, ⟨53249366, 1⟩, ⟨39285227, 1⟩, ⟨-12558592, 1⟩]
def cap_slope_H_7_denominator : List Fraction := [⟨0, 1⟩, ⟨33554432, 1⟩, ⟨67108864, 1⟩]
def cap_slope_H_7_controls : List Fraction := [⟨2429397347, 16⟩, ⟨7991604275, 48⟩, ⟨4809339182, 27⟩, ⟨4974487151, 27⟩]

theorem cap_slope_H_7_coefficient_0 : (Fraction.lt ⟨100000000, 1⟩ ⟨2429397347, 16⟩) = true := by
  decide +kernel

theorem cap_slope_H_7_coefficient_1 : (Fraction.lt ⟨100000000, 1⟩ ⟨7991604275, 48⟩) = true := by
  decide +kernel

theorem cap_slope_H_7_coefficient_2 : (Fraction.lt ⟨100000000, 1⟩ ⟨4809339182, 27⟩) = true := by
  decide +kernel

theorem cap_slope_H_7_coefficient_3 : (Fraction.lt ⟨100000000, 1⟩ ⟨4974487151, 27⟩) = true := by
  decide +kernel

theorem cap_slope_H_7_reconstruct : (Fraction.allEq (bernstein cap_slope_H_7_numerator ⟨7, 4⟩ ⟨7, 3⟩ 3) cap_slope_H_7_controls) = true := by
  decide +kernel

end F4Heavy.Finite
