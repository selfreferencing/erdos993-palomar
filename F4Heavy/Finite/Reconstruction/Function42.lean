module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite
open Fraction

def numerator_H_r6_endpoint_C : List (List Fraction) :=
  [[⟨5095368579730, 1⟩, ⟨3538087071904, 1⟩, ⟨1947317700636, 1⟩, ⟨2579612841421, 1⟩, ⟨806619551500, 1⟩],
    [⟨-14281511328040, 1⟩, ⟨-171279350704, 1⟩, ⟨21356597432016, 1⟩, ⟨16212656008612, 1⟩, ⟨3016426221592, 1⟩],
    [⟨-25159703532150, 1⟩, ⟨-15879508783600, 1⟩, ⟨40975642192044, 1⟩, ⟨32647089681297, 1⟩, ⟨3402941804276, 1⟩],
    [⟨-14757095628000, 1⟩, ⟨-19754393199968, 1⟩, ⟨24171065145024, 1⟩, ⟨25743542206816, 1⟩, ⟨-420103968816, 1⟩],
    [⟨-4165610758650, 1⟩, ⟨-9404319460032, 1⟩, ⟨734161746612, 1⟩, ⟨4780455997471, 1⟩, ⟨-3612993788684, 1⟩],
    [⟨-579569965560, 1⟩, ⟨-1973350424304, 1⟩, ⟨-2241384129936, 1⟩, ⟨-2666958894852, 1⟩, ⟨-2596322252776, 1⟩],
    [⟨-32032257570, 1⟩, ⟨-153281803248, 1⟩, ⟨-370843192188, 1⟩, ⟨-717919199613, 1⟩, ⟨-596567567092, 1⟩]]

-- certificates.json[336], H_r6_endpoint_C, source coefficient reconstruction
theorem reconstruct_336_H_r6_endpoint_C :
    (allEq (ordinaryControl numerator_H_r6_endpoint_C ⟨1, 4⟩ 4 0 ⟨0, 1⟩ ⟨1, 7⟩ false false)
    [⟨1228008886625557803985, 240945152⟩, ⟨-35984515932630333993, 2151296⟩, ⟨-36949461594794576351, 1229312⟩, ⟨-216020901545756161, 10976⟩, ⟨-43089491520643357, 6272⟩, ⟨-36699540345451, 28⟩, ⟨-3426503598293, 32⟩]) = true := by
  decide +kernel

-- certificates.json[337], H_r6_endpoint_C, source coefficient reconstruction
theorem reconstruct_337_H_r6_endpoint_C :
    (allEq (ordinaryControl numerator_H_r6_endpoint_C ⟨1, 4⟩ 4 1 ⟨0, 1⟩ ⟨1, 7⟩ false false)
    [⟨12022031738223453169595, 1927561216⟩, ⟨-954763977461043209583, 68841472⟩, ⟨-277049619713614973791, 9834496⟩, ⟨-3635925909411764509, 175616⟩, ⟨-436419014378059187, 50176⟩, ⟨-3684436252186855, 1792⟩, ⟨-51920767452553, 256⟩]) = true := by
  decide +kernel

-- certificates.json[338], H_r6_endpoint_C, source coefficient reconstruction
theorem reconstruct_338_H_r6_endpoint_C :
    (allEq (ordinaryControl numerator_H_r6_endpoint_C ⟨1, 4⟩ 4 2 ⟨0, 1⟩ ⟨1, 7⟩ false false)
    [⟨1935973116703859133895, 240945152⟩, ⟨-58572575776440812475, 8605184⟩, ⟨-23543552569456406171, 1229312⟩, ⟨-386606070429954209, 21952⟩, ⟨-65418240867345631, 6272⟩, ⟨-747229406212307, 224⟩, ⟨-12952674553517, 32⟩]) = true := by
  decide +kernel

-- certificates.json[339], H_r6_endpoint_C, source coefficient reconstruction
theorem reconstruct_339_H_r6_endpoint_C :
    (allEq (ordinaryControl numerator_H_r6_endpoint_C ⟨1, 4⟩ 4 3 ⟨0, 1⟩ ⟨1, 7⟩ false false)
    [⟨1326765374908616918825, 120472576⟩, ⟨30429656661561661803, 4302592⟩, ⟨846580083755256491, 614656⟩, ⟨-84814669385036431, 10976⟩, ⟨-38112401771743505, 3136⟩, ⟨-645637571228029, 112⟩, ⟨-13625316150883, 16⟩]) = true := by
  decide +kernel

-- certificates.json[340], H_r6_endpoint_C, source coefficient reconstruction
theorem reconstruct_340_H_r6_endpoint_C :
    (allEq (ordinaryControl numerator_H_r6_endpoint_C ⟨1, 4⟩ 4 4 ⟨0, 1⟩ ⟨1, 7⟩ false false)
    [⟨120641107082017046765, 7529536⟩, ⟨8466641826424965231, 268912⟩, ⟨1490638025675347271, 38416⟩, ⟨7629991238706413, 686⟩, ⟨-3019078684619093, 196⟩, ⟨-76015031731129, 7⟩, ⟨-1870644019711, 1⟩]) = true := by
  decide +kernel

end F4Heavy.Finite
