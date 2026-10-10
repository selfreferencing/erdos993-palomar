module

public import F4Heavy.Finite.TransformArithmetic

@[expose] public section
set_option autoImplicit false
namespace F4Heavy.Finite

def leaf_D_polynomial : List Fraction := [⟨-274877906944, 25⟩, ⟨1413504016384, 25⟩, ⟨-6938482904655181, 81920⟩, ⟨430776334709479, 122880⟩, ⟨19824204338678297, 245760⟩, ⟨-2231796310016, 45⟩, ⟨34932625408, 9⟩, ⟨39487799296, 225⟩, ⟨39761690624, 225⟩, ⟨4503713792, 15⟩]

def leaf_D_controls : List Fraction := [⟨35030548232390215813, 1190155742208⟩, ⟨10131715641610197203429, 164241492424704⟩, ⟨124746583152868583143159, 1492367141044224⟩, ⟨1102056066123506203720879, 11441481414672384⟩, ⟨2215678276401283373791181, 21929506044788736⟩, ⟨38780281975603762426130759, 392294497023442944⟩, ⟨17349363014937607318526557, 190958167863263232⟩, ⟨4232758133165883240890071, 54222689640185856⟩, ⟨3592457510036158662317881, 58458837268325376⟩, ⟨309389608914205817304433, 7377521301352448⟩]

theorem leaf_D_degree : ((leaf_D_polynomial.length == 10)) = true := by decide +kernel

theorem leaf_D_coefficient_00 : (Fraction.positive ⟨35030548232390215813, 1190155742208⟩) = true := by decide +kernel

theorem leaf_D_coefficient_01 : (Fraction.positive ⟨10131715641610197203429, 164241492424704⟩) = true := by decide +kernel

theorem leaf_D_coefficient_02 : (Fraction.positive ⟨124746583152868583143159, 1492367141044224⟩) = true := by decide +kernel

theorem leaf_D_coefficient_03 : (Fraction.positive ⟨1102056066123506203720879, 11441481414672384⟩) = true := by decide +kernel

theorem leaf_D_coefficient_04 : (Fraction.positive ⟨2215678276401283373791181, 21929506044788736⟩) = true := by decide +kernel

theorem leaf_D_coefficient_05 : (Fraction.positive ⟨38780281975603762426130759, 392294497023442944⟩) = true := by decide +kernel

theorem leaf_D_coefficient_06 : (Fraction.positive ⟨17349363014937607318526557, 190958167863263232⟩) = true := by decide +kernel

theorem leaf_D_coefficient_07 : (Fraction.positive ⟨4232758133165883240890071, 54222689640185856⟩) = true := by decide +kernel

theorem leaf_D_coefficient_08 : (Fraction.positive ⟨3592457510036158662317881, 58458837268325376⟩) = true := by decide +kernel

theorem leaf_D_coefficient_09 : (Fraction.positive ⟨309389608914205817304433, 7377521301352448⟩) = true := by decide +kernel

theorem leaf_D_reconstruction : (Fraction.allEq (bernstein leaf_D_polynomial ⟨4, 9⟩ ⟨13, 23⟩ 9) leaf_D_controls) = true := by decide +kernel

theorem leaf_D_closed_endpoint_0 : (Fraction.eq (evalPoly leaf_D_polynomial ⟨4, 9⟩) ⟨35030548232390215813, 1190155742208⟩) = true := by decide +kernel

theorem leaf_D_closed_endpoint_1 : (Fraction.eq (evalPoly leaf_D_polynomial ⟨13, 23⟩) ⟨309389608914205817304433, 7377521301352448⟩) = true := by decide +kernel

theorem leaf_D_gamma_endpoint_0 : (Fraction.positive ⟨7094913, 41943040⟩) = true := by decide +kernel

theorem leaf_D_gamma_endpoint_1 : (Fraction.positive ⟨11476993, 41943040⟩) = true := by decide +kernel

theorem leaf_D_interval : ((Fraction.positive ⟨4, 9⟩ && Fraction.lt ⟨4, 9⟩ ⟨13, 23⟩ && Fraction.lt ⟨13, 23⟩ Fraction.one)) = true := by decide +kernel

theorem leaf_D_price : (Fraction.positive ⟨8, 5⟩) = true := by decide +kernel

def leaf_E1_polynomial : List Fraction := [⟨-310311387136, 25⟩, ⟨1403689762816, 25⟩, ⟨-349194429993, 4⟩, ⟨1605212151983, 30⟩, ⟨141550672201, 60⟩, ⟨-6204130359296, 225⟩, ⟨2362673917952, 225⟩, ⟨62755979264, 225⟩, ⟨39709179904, 225⟩, ⟨18125871104, 25⟩]

def leaf_E1_controls : List Fraction := [⟨178932694085205298761, 1801152661463⟩, ⟨1477759989984856865821, 14800776218109⟩, ⟨88162367360623683158203, 882898477010676⟩, ⟨436181200919841770494063, 4388901124850172⟩, ⟨60021155640022382691071, 609800061770298⟩, ⟨2898160826953702862610229, 29880203026744602⟩, ⟨4035081057520507929313681, 42438549226390884⟩, ⟨3591719488109851405030429, 38748240598009068⟩, ⟨1853976160839325696540144, 20637649883722221⟩, ⟨422601028340525431578484, 4885240793731347⟩]

theorem leaf_E1_degree : ((leaf_E1_polynomial.length == 10)) = true := by decide +kernel

theorem leaf_E1_coefficient_00 : (Fraction.positive ⟨178932694085205298761, 1801152661463⟩) = true := by decide +kernel

theorem leaf_E1_coefficient_01 : (Fraction.positive ⟨1477759989984856865821, 14800776218109⟩) = true := by decide +kernel

theorem leaf_E1_coefficient_02 : (Fraction.positive ⟨88162367360623683158203, 882898477010676⟩) = true := by decide +kernel

theorem leaf_E1_coefficient_03 : (Fraction.positive ⟨436181200919841770494063, 4388901124850172⟩) = true := by decide +kernel

theorem leaf_E1_coefficient_04 : (Fraction.positive ⟨60021155640022382691071, 609800061770298⟩) = true := by decide +kernel

theorem leaf_E1_coefficient_05 : (Fraction.positive ⟨2898160826953702862610229, 29880203026744602⟩) = true := by decide +kernel

theorem leaf_E1_coefficient_06 : (Fraction.positive ⟨4035081057520507929313681, 42438549226390884⟩) = true := by decide +kernel

theorem leaf_E1_coefficient_07 : (Fraction.positive ⟨3591719488109851405030429, 38748240598009068⟩) = true := by decide +kernel

theorem leaf_E1_coefficient_08 : (Fraction.positive ⟨1853976160839325696540144, 20637649883722221⟩) = true := by decide +kernel

theorem leaf_E1_coefficient_09 : (Fraction.positive ⟨422601028340525431578484, 4885240793731347⟩) = true := by decide +kernel

theorem leaf_E1_reconstruction : (Fraction.allEq (bernstein leaf_E1_polynomial ⟨13, 23⟩ ⟨29, 49⟩ 9) leaf_E1_controls) = true := by decide +kernel

theorem leaf_E1_closed_endpoint_0 : (Fraction.eq (evalPoly leaf_E1_polynomial ⟨13, 23⟩) ⟨178932694085205298761, 1801152661463⟩) = true := by decide +kernel

theorem leaf_E1_closed_endpoint_1 : (Fraction.eq (evalPoly leaf_E1_polynomial ⟨29, 49⟩) ⟨422601028340525431578484, 4885240793731347⟩) = true := by decide +kernel

theorem leaf_E1_gamma_endpoint_0 : (Fraction.positive ⟨651391, 2621440⟩) = true := by decide +kernel

theorem leaf_E1_gamma_endpoint_1 : (Fraction.positive ⟨774289, 2621440⟩) = true := by decide +kernel

theorem leaf_E1_interval : ((Fraction.positive ⟨13, 23⟩ && Fraction.lt ⟨13, 23⟩ ⟨29, 49⟩ && Fraction.lt ⟨29, 49⟩ Fraction.one)) = true := by decide +kernel

theorem leaf_E1_price : (Fraction.positive ⟨17, 10⟩) = true := by decide +kernel

def leaf_E2_polynomial : List Fraction := [⟨-310311387136, 25⟩, ⟨1295052875776, 25⟩, ⟨-71442461163049, 1024⟩, ⟨44383887511291, 1536⟩, ⟨29850802560133, 3072⟩, ⟨-721368622336, 45⟩, ⟨76343961088, 15⟩, ⟨42825908224, 225⟩, ⟨4416374784, 25⟩, ⟨16256708864, 45⟩]

def leaf_E2_controls : List Fraction := [⟨5840561598992513520101127, 104218470266268736⟩, ⟨3123206271179656190566029, 55299596467816064⟩, ⟨239110912285955970787493087, 4225340595418435584⟩, ⟨147472507716011401955194871, 2615687035259031552⟩, ⟨9689705425486054864910401, 173489446216160256⟩, ⟨1085103490662774875444741, 19726205254898688⟩, ⟨2630455669932525576657931, 48845841583558656⟩, ⟨96983636807722497824633, 1851300118327296⟩, ⟨1165317746954930289347, 23023183869504⟩, ⟨8235842174371275683, 169671989968⟩]

theorem leaf_E2_degree : ((leaf_E2_polynomial.length == 10)) = true := by decide +kernel

theorem leaf_E2_coefficient_00 : (Fraction.positive ⟨5840561598992513520101127, 104218470266268736⟩) = true := by decide +kernel

theorem leaf_E2_coefficient_01 : (Fraction.positive ⟨3123206271179656190566029, 55299596467816064⟩) = true := by decide +kernel

theorem leaf_E2_coefficient_02 : (Fraction.positive ⟨239110912285955970787493087, 4225340595418435584⟩) = true := by decide +kernel

theorem leaf_E2_coefficient_03 : (Fraction.positive ⟨147472507716011401955194871, 2615687035259031552⟩) = true := by decide +kernel

theorem leaf_E2_coefficient_04 : (Fraction.positive ⟨9689705425486054864910401, 173489446216160256⟩) = true := by decide +kernel

theorem leaf_E2_coefficient_05 : (Fraction.positive ⟨1085103490662774875444741, 19726205254898688⟩) = true := by decide +kernel

theorem leaf_E2_coefficient_06 : (Fraction.positive ⟨2630455669932525576657931, 48845841583558656⟩) = true := by decide +kernel

theorem leaf_E2_coefficient_07 : (Fraction.positive ⟨96983636807722497824633, 1851300118327296⟩) = true := by decide +kernel

theorem leaf_E2_coefficient_08 : (Fraction.positive ⟨1165317746954930289347, 23023183869504⟩) = true := by decide +kernel

theorem leaf_E2_coefficient_09 : (Fraction.positive ⟨8235842174371275683, 169671989968⟩) = true := by decide +kernel

theorem leaf_E2_reconstruction : (Fraction.allEq (bernstein leaf_E2_polynomial ⟨29, 49⟩ ⟨8, 13⟩ 9) leaf_E2_controls) = true := by decide +kernel

theorem leaf_E2_closed_endpoint_0 : (Fraction.eq (evalPoly leaf_E2_polynomial ⟨29, 49⟩) ⟨5840561598992513520101127, 104218470266268736⟩) = true := by decide +kernel

theorem leaf_E2_closed_endpoint_1 : (Fraction.eq (evalPoly leaf_E2_polynomial ⟨8, 13⟩) ⟨8235842174371275683, 169671989968⟩) = true := by decide +kernel

theorem leaf_E2_gamma_endpoint_0 : (Fraction.positive ⟨6043677, 20971520⟩) = true := by decide +kernel

theorem leaf_E2_gamma_endpoint_1 : (Fraction.positive ⟨6714621, 20971520⟩) = true := by decide +kernel

theorem leaf_E2_interval : ((Fraction.positive ⟨29, 49⟩ && Fraction.lt ⟨29, 49⟩ ⟨8, 13⟩ && Fraction.lt ⟨8, 13⟩ Fraction.one)) = true := by decide +kernel

theorem leaf_E2_price : (Fraction.positive ⟨17, 10⟩) = true := by decide +kernel

def leaf_H_polynomial : List Fraction := [⟨-17179869184, 1⟩, ⟨65226055680, 1⟩, ⟨-294583781351833, 4096⟩, ⟨47743041299915, 6144⟩, ⟨187529695516981, 12288⟩, ⟨327994787584, 45⟩, ⟨-298670880256, 45⟩, ⟨3123642368, 45⟩, ⟨14080116736, 45⟩, ⟨-2291804928, 5⟩]

def leaf_H_controls : List Fraction := [⟨19100502552309709005, 603634608896⟩, ⟨16300009300257389078027, 444494575641600⟩, ⟨46702970336157592861763, 1175522844672000⟩, ⟨2005541826767655034141, 48980118528000⟩, ⟨72040925880632014408801, 1781095219200000⟩, ⟨153997881972659683921, 4014489600000⟩, ⟨12810107521382082607981, 367994880000000⟩, ⟨15015307485982402016603, 501811200000000⟩, ⟨181098879682494103247, 7603200000000⟩, ⟨10638045279047314407, 640000000000⟩]

theorem leaf_H_degree : ((leaf_H_polynomial.length == 10)) = true := by decide +kernel

theorem leaf_H_coefficient_00 : (Fraction.positive ⟨19100502552309709005, 603634608896⟩) = true := by decide +kernel

theorem leaf_H_coefficient_01 : (Fraction.positive ⟨16300009300257389078027, 444494575641600⟩) = true := by decide +kernel

theorem leaf_H_coefficient_02 : (Fraction.positive ⟨46702970336157592861763, 1175522844672000⟩) = true := by decide +kernel

theorem leaf_H_coefficient_03 : (Fraction.positive ⟨2005541826767655034141, 48980118528000⟩) = true := by decide +kernel

theorem leaf_H_coefficient_04 : (Fraction.positive ⟨72040925880632014408801, 1781095219200000⟩) = true := by decide +kernel

theorem leaf_H_coefficient_05 : (Fraction.positive ⟨153997881972659683921, 4014489600000⟩) = true := by decide +kernel

theorem leaf_H_coefficient_06 : (Fraction.positive ⟨12810107521382082607981, 367994880000000⟩) = true := by decide +kernel

theorem leaf_H_coefficient_07 : (Fraction.positive ⟨15015307485982402016603, 501811200000000⟩) = true := by decide +kernel

theorem leaf_H_coefficient_08 : (Fraction.positive ⟨181098879682494103247, 7603200000000⟩) = true := by decide +kernel

theorem leaf_H_coefficient_09 : (Fraction.positive ⟨10638045279047314407, 640000000000⟩) = true := by decide +kernel

theorem leaf_H_reconstruction : (Fraction.allEq (bernstein leaf_H_polynomial ⟨7, 11⟩ ⟨7, 10⟩ 9) leaf_H_controls) = true := by decide +kernel

theorem leaf_H_closed_endpoint_0 : (Fraction.eq (evalPoly leaf_H_polynomial ⟨7, 11⟩) ⟨19100502552309709005, 603634608896⟩) = true := by decide +kernel

theorem leaf_H_closed_endpoint_1 : (Fraction.eq (evalPoly leaf_H_polynomial ⟨7, 10⟩) ⟨10638045279047314407, 640000000000⟩) = true := by decide +kernel

theorem leaf_H_gamma_endpoint_0 : (Fraction.positive ⟨7291025, 16777216⟩) = true := by decide +kernel

theorem leaf_H_gamma_endpoint_1 : (Fraction.positive ⟨23814259, 50331648⟩) = true := by decide +kernel

theorem leaf_H_interval : ((Fraction.positive ⟨7, 11⟩ && Fraction.lt ⟨7, 11⟩ ⟨7, 10⟩ && Fraction.lt ⟨7, 10⟩ Fraction.one)) = true := by decide +kernel

theorem leaf_H_price : (Fraction.positive ⟨2, 1⟩) = true := by decide +kernel

end F4Heavy.Finite
