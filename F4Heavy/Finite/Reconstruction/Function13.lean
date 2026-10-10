module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite
open Fraction

def numerator_D_r6_endpoint_C : List (List Fraction) :=
  [[⟨1699424315100, 1⟩, ⟨-1375273681425, 1⟩, ⟨3302591080428, 1⟩, ⟨4178818385856, 1⟩, ⟨997863448320, 1⟩],
    [⟨-212808659400, 1⟩, ⟨12716908769700, 1⟩, ⟨8487209709288, 1⟩, ⟨6063097783296, 1⟩, ⟨1940312276480, 1⟩],
    [⟨-196481173500, 1⟩, ⟨-8148240321525, 1⟩, ⟨-3061860055980, 1⟩, ⟨-4585212183360, 1⟩, ⟨-1164107308800, 1⟩],
    [⟨66974202000, 1⟩, ⟨-15851948673600, 1⟩, ⟨-16212031692240, 1⟩, ⟨-8527231969280, 1⟩, ⟨-4102283033600, 1⟩],
    [⟨-8736673500, 1⟩, ⟨5716257256725, 1⟩, ⟨-5920969654380, 1⟩, ⟨-121720762560, 1⟩, ⟨-887034208000, 1⟩],
    [⟨528540600, 1⟩, ⟨-648012588900, 1⟩, ⟨1926213480168, 1⟩, ⟨1754827047936, 1⟩, ⟨2161970757120, 1⟩],
    [⟨-12384900, 1⟩, ⟨24204253425, 1⟩, ⟨-118369872852, 1⟩, ⟨-181192577984, 1⟩, ⟨1053278068480, 1⟩]]

-- certificates.json[144], D_r6_endpoint_C, source coefficient reconstruction
theorem reconstruct_144_D_r6_endpoint_C :
    (allEq (ordinaryControl numerator_D_r6_endpoint_C ⟨5, 16⟩ 4 0 ⟨0, 1⟩ ⟨5, 21⟩ false false)
    [⟨350275034936182864870175, 156132458496⟩, ⟨6976982458264580325575, 1858719744⟩, ⟨-54173222535940619375, 9834496⟩, ⟨-3264045761146220375, 526848⟩, ⟨61375394662030625, 50176⟩, ⟨108711478426725, 1792⟩, ⟨129835562175, 256⟩]) = true := by
  decide +kernel

-- certificates.json[145], D_r6_endpoint_C, source coefficient reconstruction
theorem reconstruct_145_D_r6_endpoint_C :
    (allEq (ordinaryControl numerator_D_r6_endpoint_C ⟨5, 16⟩ 4 1 ⟨0, 1⟩ ⟨5, 21⟩ false false)
    [⟨4168742098000416953230555, 1405192126464⟩, ⟨36329491679697721282415, 5576159232⟩, ⟨-2453793728050016483725, 265531392⟩, ⟨-52115849390548228625, 4741632⟩, ⟨253234444676066975, 150528⟩, ⟨525207377841815, 1792⟩, ⟨1261220884495, 256⟩]) = true := by
  decide +kernel

-- certificates.json[146], D_r6_endpoint_C, source coefficient reconstruction
theorem reconstruct_146_D_r6_endpoint_C :
    (allEq (ordinaryControl numerator_D_r6_endpoint_C ⟨5, 16⟩ 4 2 ⟨0, 1⟩ ⟨5, 21⟩ false false)
    [⟨346277276263301536521709, 78066229248⟩, ⟨28548527097606107698843, 2788079616⟩, ⟨-1910931668107884444055, 132765696⟩, ⟨-14283413399993463955, 790272⟩, ⟨139796956492302505, 75264⟩, ⟨828926848528283, 896⟩, ⟨4512884905749, 128⟩]) = true := by
  decide +kernel

-- certificates.json[147], D_r6_endpoint_C, source coefficient reconstruction
theorem reconstruct_147_D_r6_endpoint_C :
    (allEq (ordinaryControl numerator_D_r6_endpoint_C ⟨5, 16⟩ 4 3 ⟨0, 1⟩ ⟨5, 21⟩ false false)
    [⟨838965127808712364636891, 117099343872⟩, ⟨7180227692880905931103, 464679936⟩, ⟨-483578589313304971805, 22127616⟩, ⟨-11279821808440072865, 395136⟩, ⟨23629415544457855, 12544⟩, ⟨1068399702226389, 448⟩, ⟨11759089590237, 64⟩]) = true := by
  decide +kernel

-- certificates.json[148], D_r6_endpoint_C, source coefficient reconstruction
theorem reconstruct_148_D_r6_endpoint_C :
    (allEq (ordinaryControl numerator_D_r6_endpoint_C ⟨5, 16⟩ 4 4 ⟨0, 1⟩ ⟨5, 21⟩ false false)
    [⟨65520511283988434262941, 5489031744⟩, ⟨501193827206711986633, 21781872⟩, ⟨-34340543760742690955, 1037232⟩, ⟨-823227813522133015, 18522⟩, ⟨1197016992166105, 588⟩, ⟨40258228089313, 7⟩, ⟨777907486169, 1⟩]) = true := by
  decide +kernel

end F4Heavy.Finite
