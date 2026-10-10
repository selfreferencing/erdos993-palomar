module
public import Erdos993Lean.F4U.Light.Construction.ContactSemantics
public import Erdos993Lean.F4U.Light.Construction.ContactLogData
@[expose] public section
set_option maxRecDepth 8192
namespace F4Unified.LightConstruction.ContactChecks
noncomputable section
open F4U.Light.Linking
def D_lo_first_rows : Polynomial2.Rows := [[65868824677577001970708938850034034630765975433213249044267663059368140844720402441234976977819297843613625, -207234096979937726940042122469233922205097155969058673630000942953801738707188259311814963638107750, -98703641079021946051943311423305231618322772201841574985532703925612374550671375], [-1777056855988825105350381909563187108472766031079216269998197849317075631921568403139837654210274075, 4565266365745919370907794022489774988125468355360150951790220059805602076776720850, -612699176937254897858816530522969576156201199034247147650475075], [-23527366860816559977836203484443836994345142311893154191071954441751254988604171765, 11373695222800959947249252932549357202113380287579624590185424270, -1159745744553952115525744995262183433703717965], [-38088241146661975727248099160582555121464445775251576904655181481, 8199340786354039805832081123857742389659537158, -607389400443476149816196961]]
theorem D_lo_first_checked : Polynomial2.rectangleNormOK D_lo_first_rows = true := by decide
theorem D_lo_first_identity (x y : ℝ) : Polynomial2.eval D_lo_first_rows x y =
    (80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*contactCleared ((4404409 : ℝ)/10000000) ((11 : ℝ)/5) (1 : ℝ) ((-3326942783 : ℝ)/2000000000) (((232242450712722371 : ℝ)/400000000000000000)+((1 : ℝ)/2000000000000000000)*y) (((32458660463368861 : ℝ)/2000000000000000000)+((1 : ℝ)/2000000000000000000)*x) := by
  norm_num [D_lo_first_rows, Polynomial2.eval, F4U.Light.eval, contactCleared]
  ring
theorem D_lo_first : literalContactValue ((4 : ℝ)/5) ((4404409 : ℝ)/10000000) ((11 : ℝ)/5) (1 : ℝ) < ((-3326942783 : ℝ)/2000000000) := by
  have hu0 : 0 < ((4404409 : ℝ)/10000000) := by norm_num
  have hu1 : ((4404409 : ℝ)/10000000) < 1 := by norm_num
  have hp := checkLogCertificate_sound ContactLogData.L00_checked
  have ht := checkLogCertificate_sound ContactLogData.L01_checked
  have hpa : ContactLogData.L00.argument = 1/(1-((4404409 : ℝ)/10000000)) := by
    norm_num [LogCertificate.argument, ContactLogData.L00]
  have hta : ContactLogData.L01.argument = ((4 : ℝ)/5)*(1-((4404409 : ℝ)/10000000))/((4404409 : ℝ)/10000000) := by
    norm_num [LogCertificate.argument, ContactLogData.L01]
  rw [hpa, ← phi_eq_log_inv hu0 hu1] at hp
  rw [hta] at ht
  norm_num [ContactLogData.L00] at hp
  norm_num [ContactLogData.L01] at ht
  have hpN := normalized_interval (value := phi ((4404409 : ℝ)/10000000)) (midpoint := ((232242450712722371 : ℝ)/400000000000000000)) (radius := ((1 : ℝ)/2000000000000000000))
    (by norm_num) (by convert hp.1 using 1 <;> norm_num) (by convert hp.2 using 1 <;> norm_num)
  have htN := normalized_interval (value := Real.log (((4 : ℝ)/5)*(1-((4404409 : ℝ)/10000000))/((4404409 : ℝ)/10000000))) (midpoint := ((32458660463368861 : ℝ)/2000000000000000000)) (radius := ((1 : ℝ)/2000000000000000000))
    (by norm_num) (by convert ht.1 using 1 <;> norm_num) (by convert ht.2 using 1 <;> norm_num)
  have hpos := Polynomial2.rectangleNormOK_sound D_lo_first_checked htN.1 hpN.1
  rw [D_lo_first_identity, hpN.2, htN.2] at hpos
  have hm : 0 < (80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by norm_num
  have hclear := (mul_pos_iff_of_pos_left hm).mp hpos
  have hphi : 0 < phi ((4404409 : ℝ)/10000000) := lt_of_lt_of_le (by norm_num) hp.1
  have hw : 0 < ((4404409 : ℝ)/10000000)-(1-((4404409 : ℝ)/10000000))*phi ((4404409 : ℝ)/10000000) := by nlinarith [hp.2]
  exact literalContactValue_lt_of_cleared ((4 : ℝ)/5) ((4404409 : ℝ)/10000000) ((11 : ℝ)/5) (1 : ℝ) ((-3326942783 : ℝ)/2000000000) hu0.ne' hphi (by norm_num) hw.ne' hclear
#print axioms D_lo_first_checked
#print axioms D_lo_first_identity
#print axioms D_lo_first
def D_lo_second_rows : Polynomial2.Rows := [[1054793271168006779668449175699756941970481919584145644924048549512415129245624642115537910705933301554932371, -12269901649695714697211722818326940457074459681573354651161710120418214734434739437386429495382344306, -38383721634278373227939705068983122286913440017351182833366915674486031636975908821], [-19633614291509158744542679675231224535195460441837893052945383418548178196349232998998096424860095347, 645102315650910541472842825311535921333477201491685909760933289618302567641377822642, -491508223816260809917788292236200093094306611533663413282252757003], [627400271358638850871843397279248046284198555378333915796404414500969989002738945393, -3719388106841174989855988218799386318259002781622570000757919256998, -1988385552475541657480542142393190815219779060743], [-8191231918785124622693932509720479481465359667736973470776370674889, 1884879988606875755891706547062851642360955504054, -2446068837277002303776849964561]]
theorem D_lo_second_checked : Polynomial2.rectangleNormOK D_lo_second_rows = true := by decide
theorem D_lo_second_identity (x y : ℝ) : Polynomial2.eval D_lo_second_rows x y =
    (800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*contactCleared ((19405741 : ℝ)/100000000) ((3 : ℝ)/10) (1 : ℝ) ((-60258643 : ℝ)/1000000000) (((431485534600409821 : ℝ)/2000000000000000000)+((1 : ℝ)/2000000000000000000)*y) (((2401429834494695893 : ℝ)/2000000000000000000)+((1 : ℝ)/2000000000000000000)*x) := by
  norm_num [D_lo_second_rows, Polynomial2.eval, F4U.Light.eval, contactCleared]
  ring
theorem D_lo_second : literalContactValue ((4 : ℝ)/5) ((19405741 : ℝ)/100000000) ((3 : ℝ)/10) (1 : ℝ) < ((-60258643 : ℝ)/1000000000) := by
  have hu0 : 0 < ((19405741 : ℝ)/100000000) := by norm_num
  have hu1 : ((19405741 : ℝ)/100000000) < 1 := by norm_num
  have hp := checkLogCertificate_sound ContactLogData.L02_checked
  have ht := checkLogCertificate_sound ContactLogData.L03_checked
  have hpa : ContactLogData.L02.argument = 1/(1-((19405741 : ℝ)/100000000)) := by
    norm_num [LogCertificate.argument, ContactLogData.L02]
  have hta : ContactLogData.L03.argument = ((4 : ℝ)/5)*(1-((19405741 : ℝ)/100000000))/((19405741 : ℝ)/100000000) := by
    norm_num [LogCertificate.argument, ContactLogData.L03]
  rw [hpa, ← phi_eq_log_inv hu0 hu1] at hp
  rw [hta] at ht
  norm_num [ContactLogData.L02] at hp
  norm_num [ContactLogData.L03] at ht
  have hpN := normalized_interval (value := phi ((19405741 : ℝ)/100000000)) (midpoint := ((431485534600409821 : ℝ)/2000000000000000000)) (radius := ((1 : ℝ)/2000000000000000000))
    (by norm_num) (by convert hp.1 using 1 <;> norm_num) (by convert hp.2 using 1 <;> norm_num)
  have htN := normalized_interval (value := Real.log (((4 : ℝ)/5)*(1-((19405741 : ℝ)/100000000))/((19405741 : ℝ)/100000000))) (midpoint := ((2401429834494695893 : ℝ)/2000000000000000000)) (radius := ((1 : ℝ)/2000000000000000000))
    (by norm_num) (by convert ht.1 using 1 <;> norm_num) (by convert ht.2 using 1 <;> norm_num)
  have hpos := Polynomial2.rectangleNormOK_sound D_lo_second_checked htN.1 hpN.1
  rw [D_lo_second_identity, hpN.2, htN.2] at hpos
  have hm : 0 < (800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by norm_num
  have hclear := (mul_pos_iff_of_pos_left hm).mp hpos
  have hphi : 0 < phi ((19405741 : ℝ)/100000000) := lt_of_lt_of_le (by norm_num) hp.1
  have hw : 0 < ((19405741 : ℝ)/100000000)-(1-((19405741 : ℝ)/100000000))*phi ((19405741 : ℝ)/100000000) := by nlinarith [hp.2]
  exact literalContactValue_lt_of_cleared ((4 : ℝ)/5) ((19405741 : ℝ)/100000000) ((3 : ℝ)/10) (1 : ℝ) ((-60258643 : ℝ)/1000000000) hu0.ne' hphi (by norm_num) hw.ne' hclear
#print axioms D_lo_second_checked
#print axioms D_lo_second_identity
#print axioms D_lo_second
def D_hi_first_rows : Polynomial2.Rows := [[1500818132794175540061244994381897037334126620352422686478212333812845655925058737426342307074359210604992707225, -6713281544950266519088335396749223257883158817835650805578381679575310982239266988894011189811869173970, -1367172668812097835597610985490600468936331476857058272942395776558354832979619922119], [-35931366640057383430223649691162633642837697735012320772885643795327743905499512311736578895586448870675, 60993921315259742632930338901060212888322248975462210017275394206363938614746287112710, -8051225397428821553222896478466888996319877055387929923522397802483], [-236114265504122987973630331556292303599417687456072434926273443334890993478105312260325, 127628005046527033266454093133358640504401635398920925306597210592490, -14080160068419225300104346173350315142772873609477], [-288918042861595126782529084043063774832208492401255291021724186776225, 74338662154506645630577773396524445540610919308770, -6211217457788098446553016697921]]
theorem D_hi_first_checked : Polynomial2.rectangleNormOK D_hi_first_rows = true := by decide
theorem D_hi_first_identity (x y : ℝ) : Polynomial2.eval D_hi_first_rows x y =
    (800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*contactCleared ((52787217 : ℝ)/100000000) ((11 : ℝ)/5) (1 : ℝ) ((-23862523 : ℝ)/16000000) (((1501011007584419479 : ℝ)/2000000000000000000)+((1 : ℝ)/2000000000000000000)*y) (((60303955014148163 : ℝ)/400000000000000000)+((1 : ℝ)/2000000000000000000)*x) := by
  norm_num [D_hi_first_rows, Polynomial2.eval, F4U.Light.eval, contactCleared]
  ring
theorem D_hi_first : literalContactValue ((13 : ℝ)/10) ((52787217 : ℝ)/100000000) ((11 : ℝ)/5) (1 : ℝ) < ((-23862523 : ℝ)/16000000) := by
  have hu0 : 0 < ((52787217 : ℝ)/100000000) := by norm_num
  have hu1 : ((52787217 : ℝ)/100000000) < 1 := by norm_num
  have hp := checkLogCertificate_sound ContactLogData.L04_checked
  have ht := checkLogCertificate_sound ContactLogData.L05_checked
  have hpa : ContactLogData.L04.argument = 1/(1-((52787217 : ℝ)/100000000)) := by
    norm_num [LogCertificate.argument, ContactLogData.L04]
  have hta : ContactLogData.L05.argument = ((13 : ℝ)/10)*(1-((52787217 : ℝ)/100000000))/((52787217 : ℝ)/100000000) := by
    norm_num [LogCertificate.argument, ContactLogData.L05]
  rw [hpa, ← phi_eq_log_inv hu0 hu1] at hp
  rw [hta] at ht
  norm_num [ContactLogData.L04] at hp
  norm_num [ContactLogData.L05] at ht
  have hpN := normalized_interval (value := phi ((52787217 : ℝ)/100000000)) (midpoint := ((1501011007584419479 : ℝ)/2000000000000000000)) (radius := ((1 : ℝ)/2000000000000000000))
    (by norm_num) (by convert hp.1 using 1 <;> norm_num) (by convert hp.2 using 1 <;> norm_num)
  have htN := normalized_interval (value := Real.log (((13 : ℝ)/10)*(1-((52787217 : ℝ)/100000000))/((52787217 : ℝ)/100000000))) (midpoint := ((60303955014148163 : ℝ)/400000000000000000)) (radius := ((1 : ℝ)/2000000000000000000))
    (by norm_num) (by convert ht.1 using 1 <;> norm_num) (by convert ht.2 using 1 <;> norm_num)
  have hpos := Polynomial2.rectangleNormOK_sound D_hi_first_checked htN.1 hpN.1
  rw [D_hi_first_identity, hpN.2, htN.2] at hpos
  have hm : 0 < (800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by norm_num
  have hclear := (mul_pos_iff_of_pos_left hm).mp hpos
  have hphi : 0 < phi ((52787217 : ℝ)/100000000) := lt_of_lt_of_le (by norm_num) hp.1
  have hw : 0 < ((52787217 : ℝ)/100000000)-(1-((52787217 : ℝ)/100000000))*phi ((52787217 : ℝ)/100000000) := by nlinarith [hp.2]
  exact literalContactValue_lt_of_cleared ((13 : ℝ)/10) ((52787217 : ℝ)/100000000) ((11 : ℝ)/5) (1 : ℝ) ((-23862523 : ℝ)/16000000) hu0.ne' hphi (by norm_num) hw.ne' hclear
#print axioms D_hi_first_checked
#print axioms D_hi_first_identity
#print axioms D_hi_first
def D_hi_second_rows : Polynomial2.Rows := [[32153428592922759807623289840825939105519806173255093466319798015258750388840558503053291019549678770242051829, -59041281053928726752096460898810510591535166894795699475874360430124769296627609918617342854238225506, -119094111699351939361320429398861705411630392168446620393084543405248953816462288579], [32960251911181535491425789427718264653989051779822600969018105967383386416145983197148530732782484973, 1106404350103352103899771318947905723868612033515419496458524498853071259052584084078, -1189772932573468513953327404559877039432530639487371497171907219723], [-790412372097948941103488324447481243699764474434577019136815631596665305282802018633, -8116456920506446496569765644531762029315199213277534111480368066838, -3734958557357160325221693091430610073917475901617], [3809077201402333143277859464664963601771164472204621876329268529831, -1312513445382441289373055153453763806856061263734, -3521123109740086719421811638081]]
theorem D_hi_second_checked : Polynomial2.rectangleNormOK D_hi_second_rows = true := by decide
theorem D_hi_second_identity (x y : ℝ) : Polynomial2.eval D_hi_second_rows x y =
    (800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*contactCleared ((25029329 : ℝ)/100000000) ((3 : ℝ)/10) (1 : ℝ) ((174865111 : ℝ)/5000000000) (((576146404532817019 : ℝ)/2000000000000000000)+((1 : ℝ)/2000000000000000000)*y) (((2718825901870861307 : ℝ)/2000000000000000000)+((1 : ℝ)/2000000000000000000)*x) := by
  norm_num [D_hi_second_rows, Polynomial2.eval, F4U.Light.eval, contactCleared]
  ring
theorem D_hi_second : literalContactValue ((13 : ℝ)/10) ((25029329 : ℝ)/100000000) ((3 : ℝ)/10) (1 : ℝ) < ((174865111 : ℝ)/5000000000) := by
  have hu0 : 0 < ((25029329 : ℝ)/100000000) := by norm_num
  have hu1 : ((25029329 : ℝ)/100000000) < 1 := by norm_num
  have hp := checkLogCertificate_sound ContactLogData.L06_checked
  have ht := checkLogCertificate_sound ContactLogData.L07_checked
  have hpa : ContactLogData.L06.argument = 1/(1-((25029329 : ℝ)/100000000)) := by
    norm_num [LogCertificate.argument, ContactLogData.L06]
  have hta : ContactLogData.L07.argument = ((13 : ℝ)/10)*(1-((25029329 : ℝ)/100000000))/((25029329 : ℝ)/100000000) := by
    norm_num [LogCertificate.argument, ContactLogData.L07]
  rw [hpa, ← phi_eq_log_inv hu0 hu1] at hp
  rw [hta] at ht
  norm_num [ContactLogData.L06] at hp
  norm_num [ContactLogData.L07] at ht
  have hpN := normalized_interval (value := phi ((25029329 : ℝ)/100000000)) (midpoint := ((576146404532817019 : ℝ)/2000000000000000000)) (radius := ((1 : ℝ)/2000000000000000000))
    (by norm_num) (by convert hp.1 using 1 <;> norm_num) (by convert hp.2 using 1 <;> norm_num)
  have htN := normalized_interval (value := Real.log (((13 : ℝ)/10)*(1-((25029329 : ℝ)/100000000))/((25029329 : ℝ)/100000000))) (midpoint := ((2718825901870861307 : ℝ)/2000000000000000000)) (radius := ((1 : ℝ)/2000000000000000000))
    (by norm_num) (by convert ht.1 using 1 <;> norm_num) (by convert ht.2 using 1 <;> norm_num)
  have hpos := Polynomial2.rectangleNormOK_sound D_hi_second_checked htN.1 hpN.1
  rw [D_hi_second_identity, hpN.2, htN.2] at hpos
  have hm : 0 < (800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by norm_num
  have hclear := (mul_pos_iff_of_pos_left hm).mp hpos
  have hphi : 0 < phi ((25029329 : ℝ)/100000000) := lt_of_lt_of_le (by norm_num) hp.1
  have hw : 0 < ((25029329 : ℝ)/100000000)-(1-((25029329 : ℝ)/100000000))*phi ((25029329 : ℝ)/100000000) := by nlinarith [hp.2]
  exact literalContactValue_lt_of_cleared ((13 : ℝ)/10) ((25029329 : ℝ)/100000000) ((3 : ℝ)/10) (1 : ℝ) ((174865111 : ℝ)/5000000000) hu0.ne' hphi (by norm_num) hw.ne' hclear
#print axioms D_hi_second_checked
#print axioms D_hi_second_identity
#print axioms D_hi_second
def E_13_10_first_rows : Polynomial2.Rows := [[316994482827474697515383122344368245630732274576440198407], [-41135262147981708839955873552481907937647456983], [-134678077554406449863216440691], [-185794138069]]
theorem E_13_10_first_checked : Polynomial2.rectangleNormOK E_13_10_first_rows = true := by decide
theorem E_13_10_first_identity (x y : ℝ) : Polynomial2.eval E_13_10_first_rows x y =
    (438012000000000000000000000000000000000000000000000000000000000000 : ℝ)*contactCleared ((13 : ℝ)/23) ((7 : ℝ)/3) ((3 : ℝ)/2) ((-79166889 : ℝ)/50000000) (((1665818245870208013 : ℝ)/2000000000000000000)+((1 : ℝ)/2000000000000000000)*y) ((0 : ℝ)+(0 : ℝ)*x) := by
  norm_num [E_13_10_first_rows, Polynomial2.eval, F4U.Light.eval, contactCleared]
  ring
theorem E_13_10_first : literalContactValue ((13 : ℝ)/10) ((13 : ℝ)/23) ((7 : ℝ)/3) ((3 : ℝ)/2) < ((-79166889 : ℝ)/50000000) := by
  have hu0 : 0 < ((13 : ℝ)/23) := by norm_num
  have hu1 : ((13 : ℝ)/23) < 1 := by norm_num
  have hp := checkLogCertificate_sound ContactLogData.L08_checked
  have ht := checkLogCertificate_sound ContactLogData.L09_checked
  have hpa : ContactLogData.L08.argument = 1/(1-((13 : ℝ)/23)) := by
    norm_num [LogCertificate.argument, ContactLogData.L08]
  have hta : ContactLogData.L09.argument = ((13 : ℝ)/10)*(1-((13 : ℝ)/23))/((13 : ℝ)/23) := by
    norm_num [LogCertificate.argument, ContactLogData.L09]
  rw [hpa, ← phi_eq_log_inv hu0 hu1] at hp
  rw [hta] at ht
  norm_num [ContactLogData.L08] at hp
  norm_num [ContactLogData.L09] at ht
  have hpN := normalized_interval (value := phi ((13 : ℝ)/23)) (midpoint := ((1665818245870208013 : ℝ)/2000000000000000000)) (radius := ((1 : ℝ)/2000000000000000000))
    (by norm_num) (by convert hp.1 using 1 <;> norm_num) (by convert hp.2 using 1 <;> norm_num)
  have htN : |(Real.log (((13 : ℝ)/10)*(1-((13 : ℝ)/23))/((13 : ℝ)/23))-(0 : ℝ))/(0 : ℝ)| ≤ 1 ∧
      (0 : ℝ)+(0 : ℝ)*((Real.log (((13 : ℝ)/10)*(1-((13 : ℝ)/23))/((13 : ℝ)/23))-(0 : ℝ))/(0 : ℝ)) = Real.log (((13 : ℝ)/10)*(1-((13 : ℝ)/23))/((13 : ℝ)/23)) := by norm_num

  have hpos := Polynomial2.rectangleNormOK_sound E_13_10_first_checked htN.1 hpN.1
  rw [E_13_10_first_identity, hpN.2, htN.2] at hpos
  have hm : 0 < (438012000000000000000000000000000000000000000000000000000000000000 : ℝ) := by norm_num
  have hclear := (mul_pos_iff_of_pos_left hm).mp hpos
  have hphi : 0 < phi ((13 : ℝ)/23) := lt_of_lt_of_le (by norm_num) hp.1
  have hw : 0 < ((13 : ℝ)/23)-(1-((13 : ℝ)/23))*phi ((13 : ℝ)/23) := by nlinarith [hp.2]
  exact literalContactValue_lt_of_cleared ((13 : ℝ)/10) ((13 : ℝ)/23) ((7 : ℝ)/3) ((3 : ℝ)/2) ((-79166889 : ℝ)/50000000) hu0.ne' hphi (by norm_num) hw.ne' hclear
#print axioms E_13_10_first_checked
#print axioms E_13_10_first_identity
#print axioms E_13_10_first
def E_13_10_second_rows : Polynomial2.Rows := [[226746191308360961419618848516365485822027398112791654297939116209967271367254437666925, -3985314225902014277864373536021319311212202770894908400260765042744938993490, -5553431075928364513857885874658391539494678518999555318987], [2402605424583231943066051970296098682658859042865148174796046350599138458325, 82834274137766627900454088694023379824655551244206991349790, -55286054145981181284401270490656330636323], [-52581740041138338379197398233308773711728289776525856017025, -533874482531334538491288447227109977029030, -172932180090184409302889], [265048002590029474617215927111431766030975, -58264776202190573419430, -162409]]
theorem E_13_10_second_checked : Polynomial2.rectangleNormOK E_13_10_second_rows = true := by decide
theorem E_13_10_second_identity (x y : ℝ) : Polynomial2.eval E_13_10_second_rows x y =
    (36720736020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*contactCleared ((52 : ℝ)/207) ((3 : ℝ)/10) ((3 : ℝ)/2) ((3500567 : ℝ)/100000000) (((578587352692244907 : ℝ)/2000000000000000000)+((1 : ℝ)/2000000000000000000)*y) (((541818265122124127 : ℝ)/400000000000000000)+((1 : ℝ)/2000000000000000000)*x) := by
  norm_num [E_13_10_second_rows, Polynomial2.eval, F4U.Light.eval, contactCleared]
  ring
theorem E_13_10_second : literalContactValue ((13 : ℝ)/10) ((52 : ℝ)/207) ((3 : ℝ)/10) ((3 : ℝ)/2) < ((3500567 : ℝ)/100000000) := by
  have hu0 : 0 < ((52 : ℝ)/207) := by norm_num
  have hu1 : ((52 : ℝ)/207) < 1 := by norm_num
  have hp := checkLogCertificate_sound ContactLogData.L10_checked
  have ht := checkLogCertificate_sound ContactLogData.L11_checked
  have hpa : ContactLogData.L10.argument = 1/(1-((52 : ℝ)/207)) := by
    norm_num [LogCertificate.argument, ContactLogData.L10]
  have hta : ContactLogData.L11.argument = ((13 : ℝ)/10)*(1-((52 : ℝ)/207))/((52 : ℝ)/207) := by
    norm_num [LogCertificate.argument, ContactLogData.L11]
  rw [hpa, ← phi_eq_log_inv hu0 hu1] at hp
  rw [hta] at ht
  norm_num [ContactLogData.L10] at hp
  norm_num [ContactLogData.L11] at ht
  have hpN := normalized_interval (value := phi ((52 : ℝ)/207)) (midpoint := ((578587352692244907 : ℝ)/2000000000000000000)) (radius := ((1 : ℝ)/2000000000000000000))
    (by norm_num) (by convert hp.1 using 1 <;> norm_num) (by convert hp.2 using 1 <;> norm_num)
  have htN := normalized_interval (value := Real.log (((13 : ℝ)/10)*(1-((52 : ℝ)/207))/((52 : ℝ)/207))) (midpoint := ((541818265122124127 : ℝ)/400000000000000000)) (radius := ((1 : ℝ)/2000000000000000000))
    (by norm_num) (by convert ht.1 using 1 <;> norm_num) (by convert ht.2 using 1 <;> norm_num)
  have hpos := Polynomial2.rectangleNormOK_sound E_13_10_second_checked htN.1 hpN.1
  rw [E_13_10_second_identity, hpN.2, htN.2] at hpos
  have hm : 0 < (36720736020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by norm_num
  have hclear := (mul_pos_iff_of_pos_left hm).mp hpos
  have hphi : 0 < phi ((52 : ℝ)/207) := lt_of_lt_of_le (by norm_num) hp.1
  have hw : 0 < ((52 : ℝ)/207)-(1-((52 : ℝ)/207))*phi ((52 : ℝ)/207) := by nlinarith [hp.2]
  exact literalContactValue_lt_of_cleared ((13 : ℝ)/10) ((52 : ℝ)/207) ((3 : ℝ)/10) ((3 : ℝ)/2) ((3500567 : ℝ)/100000000) hu0.ne' hphi (by norm_num) hw.ne' hclear
#print axioms E_13_10_second_checked
#print axioms E_13_10_second_identity
#print axioms E_13_10_second
def E_29_20_first_rows : Polynomial2.Rows := [[250728424624338382434279227940358894046608703343642717309], [-36923391879734036365936055299444617854661345481], [-97731571620303291332359624457], [-119301384643]]
theorem E_29_20_first_checked : Polynomial2.rectangleNormOK E_29_20_first_rows = true := by decide
theorem E_29_20_first_identity (x y : ℝ) : Polynomial2.eval E_29_20_first_rows x y =
    (302526000000000000000000000000000000000000000000000000000000000000 : ℝ)*contactCleared ((29 : ℝ)/49) ((7 : ℝ)/3) ((3 : ℝ)/2) ((-154103887 : ℝ)/100000000) (((1792176049113271233 : ℝ)/2000000000000000000)+((1 : ℝ)/2000000000000000000)*y) ((0 : ℝ)+(0 : ℝ)*x) := by
  norm_num [E_29_20_first_rows, Polynomial2.eval, F4U.Light.eval, contactCleared]
  ring
theorem E_29_20_first : literalContactValue ((29 : ℝ)/20) ((29 : ℝ)/49) ((7 : ℝ)/3) ((3 : ℝ)/2) < ((-154103887 : ℝ)/100000000) := by
  have hu0 : 0 < ((29 : ℝ)/49) := by norm_num
  have hu1 : ((29 : ℝ)/49) < 1 := by norm_num
  have hp := checkLogCertificate_sound ContactLogData.L12_checked
  have ht := checkLogCertificate_sound ContactLogData.L09_checked
  have hpa : ContactLogData.L12.argument = 1/(1-((29 : ℝ)/49)) := by
    norm_num [LogCertificate.argument, ContactLogData.L12]
  have hta : ContactLogData.L09.argument = ((29 : ℝ)/20)*(1-((29 : ℝ)/49))/((29 : ℝ)/49) := by
    norm_num [LogCertificate.argument, ContactLogData.L09]
  rw [hpa, ← phi_eq_log_inv hu0 hu1] at hp
  rw [hta] at ht
  norm_num [ContactLogData.L12] at hp
  norm_num [ContactLogData.L09] at ht
  have hpN := normalized_interval (value := phi ((29 : ℝ)/49)) (midpoint := ((1792176049113271233 : ℝ)/2000000000000000000)) (radius := ((1 : ℝ)/2000000000000000000))
    (by norm_num) (by convert hp.1 using 1 <;> norm_num) (by convert hp.2 using 1 <;> norm_num)
  have htN : |(Real.log (((29 : ℝ)/20)*(1-((29 : ℝ)/49))/((29 : ℝ)/49))-(0 : ℝ))/(0 : ℝ)| ≤ 1 ∧
      (0 : ℝ)+(0 : ℝ)*((Real.log (((29 : ℝ)/20)*(1-((29 : ℝ)/49))/((29 : ℝ)/49))-(0 : ℝ))/(0 : ℝ)) = Real.log (((29 : ℝ)/20)*(1-((29 : ℝ)/49))/((29 : ℝ)/49)) := by norm_num

  have hpos := Polynomial2.rectangleNormOK_sound E_29_20_first_checked htN.1 hpN.1
  rw [E_29_20_first_identity, hpN.2, htN.2] at hpos
  have hm : 0 < (302526000000000000000000000000000000000000000000000000000000000000 : ℝ) := by norm_num
  have hclear := (mul_pos_iff_of_pos_left hm).mp hpos
  have hphi : 0 < phi ((29 : ℝ)/49) := lt_of_lt_of_le (by norm_num) hp.1
  have hw : 0 < ((29 : ℝ)/49)-(1-((29 : ℝ)/49))*phi ((29 : ℝ)/49) := by nlinarith [hp.2]
  exact literalContactValue_lt_of_cleared ((29 : ℝ)/20) ((29 : ℝ)/49) ((7 : ℝ)/3) ((3 : ℝ)/2) ((-154103887 : ℝ)/100000000) hu0.ne' hphi (by norm_num) hw.ne' hclear
#print axioms E_29_20_first_checked
#print axioms E_29_20_first_identity
#print axioms E_29_20_first
def E_29_20_second_rows : Polynomial2.Rows := [[17660888699252280958557464518195671893069444840160400090322819667094021337623196615625, -4575857455739378690433106886817394385564066326084960068776998634886644208750, -5576183473898575342881006790771264310220221321063019960375], [3882806724406228459125511326513220371660007860385444724241239743410606448125, 74622325873990170598795944940307252804196859516569811808250, -53125432375842400796940319943782058307075], [-83652349813271343129383960416647666769897322361797300095125, -501681654362894291104344254393736341169450, -158825178578249090374805], [351685625983601660852214637376831554541775, -87027513119116557210210, -142129]]
theorem E_29_20_second_checked : Polynomial2.rectangleNormOK E_29_20_second_rows = true := by decide
theorem E_29_20_second_identity (x y : ℝ) : Polynomial2.eval E_29_20_second_rows x y =
    (30258287488800000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*contactCleared ((116 : ℝ)/441) ((3 : ℝ)/10) ((3 : ℝ)/2) ((5922933 : ℝ)/100000000) (((122087877246843403 : ℝ)/400000000000000000)+((1 : ℝ)/2000000000000000000)*y) (((560719419062342349 : ℝ)/400000000000000000)+((1 : ℝ)/2000000000000000000)*x) := by
  norm_num [E_29_20_second_rows, Polynomial2.eval, F4U.Light.eval, contactCleared]
  ring
theorem E_29_20_second : literalContactValue ((29 : ℝ)/20) ((116 : ℝ)/441) ((3 : ℝ)/10) ((3 : ℝ)/2) < ((5922933 : ℝ)/100000000) := by
  have hu0 : 0 < ((116 : ℝ)/441) := by norm_num
  have hu1 : ((116 : ℝ)/441) < 1 := by norm_num
  have hp := checkLogCertificate_sound ContactLogData.L13_checked
  have ht := checkLogCertificate_sound ContactLogData.L14_checked
  have hpa : ContactLogData.L13.argument = 1/(1-((116 : ℝ)/441)) := by
    norm_num [LogCertificate.argument, ContactLogData.L13]
  have hta : ContactLogData.L14.argument = ((29 : ℝ)/20)*(1-((116 : ℝ)/441))/((116 : ℝ)/441) := by
    norm_num [LogCertificate.argument, ContactLogData.L14]
  rw [hpa, ← phi_eq_log_inv hu0 hu1] at hp
  rw [hta] at ht
  norm_num [ContactLogData.L13] at hp
  norm_num [ContactLogData.L14] at ht
  have hpN := normalized_interval (value := phi ((116 : ℝ)/441)) (midpoint := ((122087877246843403 : ℝ)/400000000000000000)) (radius := ((1 : ℝ)/2000000000000000000))
    (by norm_num) (by convert hp.1 using 1 <;> norm_num) (by convert hp.2 using 1 <;> norm_num)
  have htN := normalized_interval (value := Real.log (((29 : ℝ)/20)*(1-((116 : ℝ)/441))/((116 : ℝ)/441))) (midpoint := ((560719419062342349 : ℝ)/400000000000000000)) (radius := ((1 : ℝ)/2000000000000000000))
    (by norm_num) (by convert ht.1 using 1 <;> norm_num) (by convert ht.2 using 1 <;> norm_num)
  have hpos := Polynomial2.rectangleNormOK_sound E_29_20_second_checked htN.1 hpN.1
  rw [E_29_20_second_identity, hpN.2, htN.2] at hpos
  have hm : 0 < (30258287488800000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by norm_num
  have hclear := (mul_pos_iff_of_pos_left hm).mp hpos
  have hphi : 0 < phi ((116 : ℝ)/441) := lt_of_lt_of_le (by norm_num) hp.1
  have hw : 0 < ((116 : ℝ)/441)-(1-((116 : ℝ)/441))*phi ((116 : ℝ)/441) := by nlinarith [hp.2]
  exact literalContactValue_lt_of_cleared ((29 : ℝ)/20) ((116 : ℝ)/441) ((3 : ℝ)/10) ((3 : ℝ)/2) ((5922933 : ℝ)/100000000) hu0.ne' hphi (by norm_num) hw.ne' hclear
#print axioms E_29_20_second_checked
#print axioms E_29_20_second_identity
#print axioms E_29_20_second
def E_8_5_first_rows : Polynomial2.Rows := [[921962425067710754368285213585124684351619893875361709327], [-96521956744707847740187595020202902699501429953], [-214555604553821384041662210011], [-233740999219]]
theorem E_8_5_first_checked : Polynomial2.rectangleNormOK E_8_5_first_rows = true := by decide
theorem E_8_5_first_identity (x y : ℝ) : Polynomial2.eval E_8_5_first_rows x y =
    (632736000000000000000000000000000000000000000000000000000000000000 : ℝ)*contactCleared ((8 : ℝ)/13) ((7 : ℝ)/3) ((3 : ℝ)/2) ((-150225069 : ℝ)/100000000) (((1911022890054872723 : ℝ)/2000000000000000000)+((1 : ℝ)/2000000000000000000)*y) ((0 : ℝ)+(0 : ℝ)*x) := by
  norm_num [E_8_5_first_rows, Polynomial2.eval, F4U.Light.eval, contactCleared]
  ring
theorem E_8_5_first : literalContactValue ((8 : ℝ)/5) ((8 : ℝ)/13) ((7 : ℝ)/3) ((3 : ℝ)/2) < ((-150225069 : ℝ)/100000000) := by
  have hu0 : 0 < ((8 : ℝ)/13) := by norm_num
  have hu1 : ((8 : ℝ)/13) < 1 := by norm_num
  have hp := checkLogCertificate_sound ContactLogData.L15_checked
  have ht := checkLogCertificate_sound ContactLogData.L09_checked
  have hpa : ContactLogData.L15.argument = 1/(1-((8 : ℝ)/13)) := by
    norm_num [LogCertificate.argument, ContactLogData.L15]
  have hta : ContactLogData.L09.argument = ((8 : ℝ)/5)*(1-((8 : ℝ)/13))/((8 : ℝ)/13) := by
    norm_num [LogCertificate.argument, ContactLogData.L09]
  rw [hpa, ← phi_eq_log_inv hu0 hu1] at hp
  rw [hta] at ht
  norm_num [ContactLogData.L15] at hp
  norm_num [ContactLogData.L09] at ht
  have hpN := normalized_interval (value := phi ((8 : ℝ)/13)) (midpoint := ((1911022890054872723 : ℝ)/2000000000000000000)) (radius := ((1 : ℝ)/2000000000000000000))
    (by norm_num) (by convert hp.1 using 1 <;> norm_num) (by convert hp.2 using 1 <;> norm_num)
  have htN : |(Real.log (((8 : ℝ)/5)*(1-((8 : ℝ)/13))/((8 : ℝ)/13))-(0 : ℝ))/(0 : ℝ)| ≤ 1 ∧
      (0 : ℝ)+(0 : ℝ)*((Real.log (((8 : ℝ)/5)*(1-((8 : ℝ)/13))/((8 : ℝ)/13))-(0 : ℝ))/(0 : ℝ)) = Real.log (((8 : ℝ)/5)*(1-((8 : ℝ)/13))/((8 : ℝ)/13)) := by norm_num

  have hpos := Polynomial2.rectangleNormOK_sound E_8_5_first_checked htN.1 hpN.1
  rw [E_8_5_first_identity, hpN.2, htN.2] at hpos
  have hm : 0 < (632736000000000000000000000000000000000000000000000000000000000000 : ℝ) := by norm_num
  have hclear := (mul_pos_iff_of_pos_left hm).mp hpos
  have hphi : 0 < phi ((8 : ℝ)/13) := lt_of_lt_of_le (by norm_num) hp.1
  have hw : 0 < ((8 : ℝ)/13)-(1-((8 : ℝ)/13))*phi ((8 : ℝ)/13) := by nlinarith [hp.2]
  exact literalContactValue_lt_of_cleared ((8 : ℝ)/5) ((8 : ℝ)/13) ((7 : ℝ)/3) ((3 : ℝ)/2) ((-150225069 : ℝ)/100000000) hu0.ne' hphi (by norm_num) hw.ne' hclear
#print axioms E_8_5_first_checked
#print axioms E_8_5_first_identity
#print axioms E_8_5_first
def E_8_5_second_rows : Polynomial2.Rows := [[725134280577492193506747112780265935079935152327132332849262239169161724896038264377, -11746543155294258660863585454696158619132387281498494252137534390667397802, -12733139832602877933232220166734159373615875834218508287], [11435146984113456121302733498377853879866962527094142423106216572680454453, 154028688549851752014288884319880336383318261824354748222, -116912025893374717109248285139300529443], [-250023939863828433760514678466688699369723570169716035861, -1089111275516415247596104111186452735614, -336452324185100376509], [899309225908356343546370276233714692519, -243044594274392233494, -289]]
theorem E_8_5_second_checked : Polynomial2.rectangleNormOK E_8_5_second_rows = true := by decide
theorem E_8_5_second_identity (x y : ℝ) : Polynomial2.eval E_8_5_second_rows x y =
    (58558975312500000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*contactCleared ((32 : ℝ)/117) ((3 : ℝ)/10) ((3 : ℝ)/2) ((1640021 : ℝ)/20000000) (((639045356614879327 : ℝ)/2000000000000000000)+((1 : ℝ)/2000000000000000000)*y) (((2893837965872650923 : ℝ)/2000000000000000000)+((1 : ℝ)/2000000000000000000)*x) := by
  norm_num [E_8_5_second_rows, Polynomial2.eval, F4U.Light.eval, contactCleared]
  ring
theorem E_8_5_second : literalContactValue ((8 : ℝ)/5) ((32 : ℝ)/117) ((3 : ℝ)/10) ((3 : ℝ)/2) < ((1640021 : ℝ)/20000000) := by
  have hu0 : 0 < ((32 : ℝ)/117) := by norm_num
  have hu1 : ((32 : ℝ)/117) < 1 := by norm_num
  have hp := checkLogCertificate_sound ContactLogData.L16_checked
  have ht := checkLogCertificate_sound ContactLogData.L17_checked
  have hpa : ContactLogData.L16.argument = 1/(1-((32 : ℝ)/117)) := by
    norm_num [LogCertificate.argument, ContactLogData.L16]
  have hta : ContactLogData.L17.argument = ((8 : ℝ)/5)*(1-((32 : ℝ)/117))/((32 : ℝ)/117) := by
    norm_num [LogCertificate.argument, ContactLogData.L17]
  rw [hpa, ← phi_eq_log_inv hu0 hu1] at hp
  rw [hta] at ht
  norm_num [ContactLogData.L16] at hp
  norm_num [ContactLogData.L17] at ht
  have hpN := normalized_interval (value := phi ((32 : ℝ)/117)) (midpoint := ((639045356614879327 : ℝ)/2000000000000000000)) (radius := ((1 : ℝ)/2000000000000000000))
    (by norm_num) (by convert hp.1 using 1 <;> norm_num) (by convert hp.2 using 1 <;> norm_num)
  have htN := normalized_interval (value := Real.log (((8 : ℝ)/5)*(1-((32 : ℝ)/117))/((32 : ℝ)/117))) (midpoint := ((2893837965872650923 : ℝ)/2000000000000000000)) (radius := ((1 : ℝ)/2000000000000000000))
    (by norm_num) (by convert ht.1 using 1 <;> norm_num) (by convert ht.2 using 1 <;> norm_num)
  have hpos := Polynomial2.rectangleNormOK_sound E_8_5_second_checked htN.1 hpN.1
  rw [E_8_5_second_identity, hpN.2, htN.2] at hpos
  have hm : 0 < (58558975312500000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by norm_num
  have hclear := (mul_pos_iff_of_pos_left hm).mp hpos
  have hphi : 0 < phi ((32 : ℝ)/117) := lt_of_lt_of_le (by norm_num) hp.1
  have hw : 0 < ((32 : ℝ)/117)-(1-((32 : ℝ)/117))*phi ((32 : ℝ)/117) := by nlinarith [hp.2]
  exact literalContactValue_lt_of_cleared ((8 : ℝ)/5) ((32 : ℝ)/117) ((3 : ℝ)/10) ((3 : ℝ)/2) ((1640021 : ℝ)/20000000) hu0.ne' hphi (by norm_num) hw.ne' hclear
#print axioms E_8_5_second_checked
#print axioms E_8_5_second_identity
#print axioms E_8_5_second
def H_lo_first_rows : Polynomial2.Rows := [[170765437915895215100325751705910536291100618335578198121288781639004182986325177913405677339176643142801, -352204490043911382129025428404120725384014195818669058386608786405189736914366623706805547705534, -47404575143750398326327462744843648542496240021898202056086831280754117752911], [-1308499679013392222711322923255488225773091311910367842750044685038844671488093112889764089296107, 2759996863040554199829259834446069966982234737429377659510275435297140955969738, -373350849230828761626792004621483504718432105110105942818123], [-25811406324697608367032937146788639772039227621978244248615622404798719550533917, 9408087658290284521726101974582065102879979135606268487498278, -818468231519354386272577446611990496801213], [-14177413454710604844646585682094156220951956988009121033808009, 4159274160759840104951703405126809161965006, -318332377099768401593001]]
theorem H_lo_first_checked : Polynomial2.rectangleNormOK H_lo_first_rows = true := by decide
theorem H_lo_first_identity (x y : ℝ) : Polynomial2.eval H_lo_first_rows x y =
    (47683715820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*contactCleared ((996057 : ℝ)/1562500) ((12 : ℝ)/5) ((1 : ℝ)/4) ((-15097571481 : ℝ)/10000000000) (((2029331848067164071 : ℝ)/2000000000000000000)+((1 : ℝ)/2000000000000000000)*y) (((-9624478700703503 : ℝ)/2000000000000000000)+((1 : ℝ)/2000000000000000000)*x) := by
  norm_num [H_lo_first_rows, Polynomial2.eval, F4U.Light.eval, contactCleared]
  ring
theorem H_lo_first : literalContactValue ((7 : ℝ)/4) ((996057 : ℝ)/1562500) ((12 : ℝ)/5) ((1 : ℝ)/4) < ((-15097571481 : ℝ)/10000000000) := by
  have hu0 : 0 < ((996057 : ℝ)/1562500) := by norm_num
  have hu1 : ((996057 : ℝ)/1562500) < 1 := by norm_num
  have hp := checkLogCertificate_sound ContactLogData.L18_checked
  have ht := checkLogCertificate_sound ContactLogData.L19_checked
  have hpa : ContactLogData.L18.argument = 1/(1-((996057 : ℝ)/1562500)) := by
    norm_num [LogCertificate.argument, ContactLogData.L18]
  have hta : ContactLogData.L19.argument = ((7 : ℝ)/4)*(1-((996057 : ℝ)/1562500))/((996057 : ℝ)/1562500) := by
    norm_num [LogCertificate.argument, ContactLogData.L19]
  rw [hpa, ← phi_eq_log_inv hu0 hu1] at hp
  rw [hta] at ht
  norm_num [ContactLogData.L18] at hp
  norm_num [ContactLogData.L19] at ht
  have hpN := normalized_interval (value := phi ((996057 : ℝ)/1562500)) (midpoint := ((2029331848067164071 : ℝ)/2000000000000000000)) (radius := ((1 : ℝ)/2000000000000000000))
    (by norm_num) (by convert hp.1 using 1 <;> norm_num) (by convert hp.2 using 1 <;> norm_num)
  have htN := normalized_interval (value := Real.log (((7 : ℝ)/4)*(1-((996057 : ℝ)/1562500))/((996057 : ℝ)/1562500))) (midpoint := ((-9624478700703503 : ℝ)/2000000000000000000)) (radius := ((1 : ℝ)/2000000000000000000))
    (by norm_num) (by convert ht.1 using 1 <;> norm_num) (by convert ht.2 using 1 <;> norm_num)
  have hpos := Polynomial2.rectangleNormOK_sound H_lo_first_checked htN.1 hpN.1
  rw [H_lo_first_identity, hpN.2, htN.2] at hpos
  have hm : 0 < (47683715820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by norm_num
  have hclear := (mul_pos_iff_of_pos_left hm).mp hpos
  have hphi : 0 < phi ((996057 : ℝ)/1562500) := lt_of_lt_of_le (by norm_num) hp.1
  have hw : 0 < ((996057 : ℝ)/1562500)-(1-((996057 : ℝ)/1562500))*phi ((996057 : ℝ)/1562500) := by nlinarith [hp.2]
  exact literalContactValue_lt_of_cleared ((7 : ℝ)/4) ((996057 : ℝ)/1562500) ((12 : ℝ)/5) ((1 : ℝ)/4) ((-15097571481 : ℝ)/10000000000) hu0.ne' hphi (by norm_num) hw.ne' hclear
#print axioms H_lo_first_checked
#print axioms H_lo_first_identity
#print axioms H_lo_first
def H_lo_second_rows : Polynomial2.Rows := [[1473590734351842582662403855548060487250071274310296710069140912972164839972612350766132191074910852502832375, -2071760198748989456454333854855483418341520593752785992356171804118671307002416549973077462634422750, -12928670066363934940420259270988610210941403305879165620928124769693072603758817625], [2634313942688329595574209692838488731273458390823787088888601261389708070668829531066392643407522925, -15329522394888219902726369958316607737663856837396622372641036336413370620995556650, -114186471290496296321439991239917257186238888266768333206747267075], [-86491387235466750325464773326375956791294076965010171311941676511527791612215296715, -378186369271001253807037321009299105951393279468079761927746223930, -315666260722380745680252816669144083500869014715], [98313728441248960943277417446362140092890629573499699226008894399, -263244974785786699081776390957156413481847633902, -259604303121975430658719350801]]
theorem H_lo_second_checked : Polynomial2.rectangleNormOK H_lo_second_rows = true := by decide
theorem H_lo_second_identity (x y : ℝ) : Polynomial2.eval H_lo_second_rows x y =
    (50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*contactCleared ((14253549 : ℝ)/50000000) ((3 : ℝ)/10) ((1 : ℝ)/4) ((516659173 : ℝ)/5000000000) (((134228805577306181 : ℝ)/400000000000000000)+((1 : ℝ)/2000000000000000000)*y) (((2958121702165046151 : ℝ)/2000000000000000000)+((1 : ℝ)/2000000000000000000)*x) := by
  norm_num [H_lo_second_rows, Polynomial2.eval, F4U.Light.eval, contactCleared]
  ring
theorem H_lo_second : literalContactValue ((7 : ℝ)/4) ((14253549 : ℝ)/50000000) ((3 : ℝ)/10) ((1 : ℝ)/4) < ((516659173 : ℝ)/5000000000) := by
  have hu0 : 0 < ((14253549 : ℝ)/50000000) := by norm_num
  have hu1 : ((14253549 : ℝ)/50000000) < 1 := by norm_num
  have hp := checkLogCertificate_sound ContactLogData.L20_checked
  have ht := checkLogCertificate_sound ContactLogData.L21_checked
  have hpa : ContactLogData.L20.argument = 1/(1-((14253549 : ℝ)/50000000)) := by
    norm_num [LogCertificate.argument, ContactLogData.L20]
  have hta : ContactLogData.L21.argument = ((7 : ℝ)/4)*(1-((14253549 : ℝ)/50000000))/((14253549 : ℝ)/50000000) := by
    norm_num [LogCertificate.argument, ContactLogData.L21]
  rw [hpa, ← phi_eq_log_inv hu0 hu1] at hp
  rw [hta] at ht
  norm_num [ContactLogData.L20] at hp
  norm_num [ContactLogData.L21] at ht
  have hpN := normalized_interval (value := phi ((14253549 : ℝ)/50000000)) (midpoint := ((134228805577306181 : ℝ)/400000000000000000)) (radius := ((1 : ℝ)/2000000000000000000))
    (by norm_num) (by convert hp.1 using 1 <;> norm_num) (by convert hp.2 using 1 <;> norm_num)
  have htN := normalized_interval (value := Real.log (((7 : ℝ)/4)*(1-((14253549 : ℝ)/50000000))/((14253549 : ℝ)/50000000))) (midpoint := ((2958121702165046151 : ℝ)/2000000000000000000)) (radius := ((1 : ℝ)/2000000000000000000))
    (by norm_num) (by convert ht.1 using 1 <;> norm_num) (by convert ht.2 using 1 <;> norm_num)
  have hpos := Polynomial2.rectangleNormOK_sound H_lo_second_checked htN.1 hpN.1
  rw [H_lo_second_identity, hpN.2, htN.2] at hpos
  have hm : 0 < (50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by norm_num
  have hclear := (mul_pos_iff_of_pos_left hm).mp hpos
  have hphi : 0 < phi ((14253549 : ℝ)/50000000) := lt_of_lt_of_le (by norm_num) hp.1
  have hw : 0 < ((14253549 : ℝ)/50000000)-(1-((14253549 : ℝ)/50000000))*phi ((14253549 : ℝ)/50000000) := by nlinarith [hp.2]
  exact literalContactValue_lt_of_cleared ((7 : ℝ)/4) ((14253549 : ℝ)/50000000) ((3 : ℝ)/10) ((1 : ℝ)/4) ((516659173 : ℝ)/5000000000) hu0.ne' hphi (by norm_num) hw.ne' hclear
#print axioms H_lo_second_checked
#print axioms H_lo_second_identity
#print axioms H_lo_second
def H_hi_first_rows : Polynomial2.Rows := [[216343565171066136410158356131108793983776895938248792069288065623347447519693612104073669359881005427017, -450107297715042062835831843399927320478978245767951726420115577415768631128891289396464637785278, -29719689461825971686348369761236543565213755958996437521025229650862274015687], [-1436958167197543249591756044943131263866171992249412443301702470668832855856578611429030586821643, 2244682667502698151503723362567110541881721724694991528138190685745437617235162, -291191105434389567743513045084106651842669378942799881150427], [-23386895822886333346682836974728442218559404370384042879982023416637713042274501, 8702280380287665735130578389362932654349513309606455281728134, -775833330390598965688941835605412236799989], [-12060395921561782904661303150248328347935623016019530680194169, 3724768548169674907998080541274254967223646, -299461250095498468609641]]
theorem H_hi_first_checked : Polynomial2.rectangleNormOK H_hi_first_rows = true := by decide
theorem H_hi_first_identity (x y : ℝ) : Polynomial2.eval H_hi_first_rows x y =
    (47683715820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*contactCleared ((1032489 : ℝ)/1562500) ((12 : ℝ)/5) ((1 : ℝ)/4) ((-3484969137 : ℝ)/2500000000) (((2162289241125568143 : ℝ)/2000000000000000000)+((1 : ℝ)/2000000000000000000)*y) (((360935900819133097 : ℝ)/2000000000000000000)+((1 : ℝ)/2000000000000000000)*x) := by
  norm_num [H_hi_first_rows, Polynomial2.eval, F4U.Light.eval, contactCleared]
  ring
theorem H_hi_first : literalContactValue ((7 : ℝ)/3) ((1032489 : ℝ)/1562500) ((12 : ℝ)/5) ((1 : ℝ)/4) < ((-3484969137 : ℝ)/2500000000) := by
  have hu0 : 0 < ((1032489 : ℝ)/1562500) := by norm_num
  have hu1 : ((1032489 : ℝ)/1562500) < 1 := by norm_num
  have hp := checkLogCertificate_sound ContactLogData.L22_checked
  have ht := checkLogCertificate_sound ContactLogData.L23_checked
  have hpa : ContactLogData.L22.argument = 1/(1-((1032489 : ℝ)/1562500)) := by
    norm_num [LogCertificate.argument, ContactLogData.L22]
  have hta : ContactLogData.L23.argument = ((7 : ℝ)/3)*(1-((1032489 : ℝ)/1562500))/((1032489 : ℝ)/1562500) := by
    norm_num [LogCertificate.argument, ContactLogData.L23]
  rw [hpa, ← phi_eq_log_inv hu0 hu1] at hp
  rw [hta] at ht
  norm_num [ContactLogData.L22] at hp
  norm_num [ContactLogData.L23] at ht
  have hpN := normalized_interval (value := phi ((1032489 : ℝ)/1562500)) (midpoint := ((2162289241125568143 : ℝ)/2000000000000000000)) (radius := ((1 : ℝ)/2000000000000000000))
    (by norm_num) (by convert hp.1 using 1 <;> norm_num) (by convert hp.2 using 1 <;> norm_num)
  have htN := normalized_interval (value := Real.log (((7 : ℝ)/3)*(1-((1032489 : ℝ)/1562500))/((1032489 : ℝ)/1562500))) (midpoint := ((360935900819133097 : ℝ)/2000000000000000000)) (radius := ((1 : ℝ)/2000000000000000000))
    (by norm_num) (by convert ht.1 using 1 <;> norm_num) (by convert ht.2 using 1 <;> norm_num)
  have hpos := Polynomial2.rectangleNormOK_sound H_hi_first_checked htN.1 hpN.1
  rw [H_hi_first_identity, hpN.2, htN.2] at hpos
  have hm : 0 < (47683715820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by norm_num
  have hclear := (mul_pos_iff_of_pos_left hm).mp hpos
  have hphi : 0 < phi ((1032489 : ℝ)/1562500) := lt_of_lt_of_le (by norm_num) hp.1
  have hw : 0 < ((1032489 : ℝ)/1562500)-(1-((1032489 : ℝ)/1562500))*phi ((1032489 : ℝ)/1562500) := by nlinarith [hp.2]
  exact literalContactValue_lt_of_cleared ((7 : ℝ)/3) ((1032489 : ℝ)/1562500) ((12 : ℝ)/5) ((1 : ℝ)/4) ((-3484969137 : ℝ)/2500000000) hu0.ne' hphi (by norm_num) hw.ne' hclear
#print axioms H_hi_first_checked
#print axioms H_hi_first_identity
#print axioms H_hi_first
def H_hi_second_rows : Polynomial2.Rows := [[6658606557758442546813787518264097066362657009996446000829382994129165366525971213327765645189805020684777457, -65376375015837854420479444101210501214706686892157404443978134402063909390351765289625169419577135294, -321351268386353594719512377744431315027459288344888545150016851775608596219681234863], [114076210357716296748096059123154887413571085194747554723751538964127010368857217305740638019186149853, -963132515233314522438263199622123964304176564532441792296266291878836807863203354726, -2569690336314429310829550729210104284531512762200667508401952943427], [-3742382383216698701370895129371117428859660756203385626797608473758712942614471956621, -10477335285597355851344795410728501008220440931442098784399529850618, -6405080169737304350976927995097541748961093239661], [995756641146156172055032992359389840561832878036712538138109060799, -7639980606134569723524265441317754607680682508258, -4699970251010731130720644161441]]
theorem H_hi_second_checked : Polynomial2.rectangleNormOK H_hi_second_rows = true := by decide
theorem H_hi_second_identity (x y : ℝ) : Polynomial2.eval H_hi_second_rows x y =
    (800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*contactCleared ((31777527 : ℝ)/100000000) ((3 : ℝ)/10) ((1 : ℝ)/4) ((1762035691 : ℝ)/10000000000) (((764792318576317807 : ℝ)/2000000000000000000)+((1 : ℝ)/2000000000000000000)*y) (((3222625090486066769 : ℝ)/2000000000000000000)+((1 : ℝ)/2000000000000000000)*x) := by
  norm_num [H_hi_second_rows, Polynomial2.eval, F4U.Light.eval, contactCleared]
  ring
theorem H_hi_second : literalContactValue ((7 : ℝ)/3) ((31777527 : ℝ)/100000000) ((3 : ℝ)/10) ((1 : ℝ)/4) < ((1762035691 : ℝ)/10000000000) := by
  have hu0 : 0 < ((31777527 : ℝ)/100000000) := by norm_num
  have hu1 : ((31777527 : ℝ)/100000000) < 1 := by norm_num
  have hp := checkLogCertificate_sound ContactLogData.L24_checked
  have ht := checkLogCertificate_sound ContactLogData.L25_checked
  have hpa : ContactLogData.L24.argument = 1/(1-((31777527 : ℝ)/100000000)) := by
    norm_num [LogCertificate.argument, ContactLogData.L24]
  have hta : ContactLogData.L25.argument = ((7 : ℝ)/3)*(1-((31777527 : ℝ)/100000000))/((31777527 : ℝ)/100000000) := by
    norm_num [LogCertificate.argument, ContactLogData.L25]
  rw [hpa, ← phi_eq_log_inv hu0 hu1] at hp
  rw [hta] at ht
  norm_num [ContactLogData.L24] at hp
  norm_num [ContactLogData.L25] at ht
  have hpN := normalized_interval (value := phi ((31777527 : ℝ)/100000000)) (midpoint := ((764792318576317807 : ℝ)/2000000000000000000)) (radius := ((1 : ℝ)/2000000000000000000))
    (by norm_num) (by convert hp.1 using 1 <;> norm_num) (by convert hp.2 using 1 <;> norm_num)
  have htN := normalized_interval (value := Real.log (((7 : ℝ)/3)*(1-((31777527 : ℝ)/100000000))/((31777527 : ℝ)/100000000))) (midpoint := ((3222625090486066769 : ℝ)/2000000000000000000)) (radius := ((1 : ℝ)/2000000000000000000))
    (by norm_num) (by convert ht.1 using 1 <;> norm_num) (by convert ht.2 using 1 <;> norm_num)
  have hpos := Polynomial2.rectangleNormOK_sound H_hi_second_checked htN.1 hpN.1
  rw [H_hi_second_identity, hpN.2, htN.2] at hpos
  have hm : 0 < (800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by norm_num
  have hclear := (mul_pos_iff_of_pos_left hm).mp hpos
  have hphi : 0 < phi ((31777527 : ℝ)/100000000) := lt_of_lt_of_le (by norm_num) hp.1
  have hw : 0 < ((31777527 : ℝ)/100000000)-(1-((31777527 : ℝ)/100000000))*phi ((31777527 : ℝ)/100000000) := by nlinarith [hp.2]
  exact literalContactValue_lt_of_cleared ((7 : ℝ)/3) ((31777527 : ℝ)/100000000) ((3 : ℝ)/10) ((1 : ℝ)/4) ((1762035691 : ℝ)/10000000000) hu0.ne' hphi (by norm_num) hw.ne' hclear
#print axioms H_hi_second_checked
#print axioms H_hi_second_identity
#print axioms H_hi_second
theorem endpointContactLo (r : Row) (s : Support) :
    supportContactValue r s (rowData r).lo (contactLo r s) < endpointInterceptLo r s := by
  cases r <;> cases s
  · have h := D_lo_first
    norm_num [supportContactValue, literalContactValue, slope, curvature, rowData, contactLo, endpointInterceptLo] at h ⊢
    exact h
  · have h := D_lo_second
    norm_num [supportContactValue, literalContactValue, slope, curvature, rowData, contactLo, endpointInterceptLo] at h ⊢
    exact h
  · have h := E_13_10_first
    norm_num [supportContactValue, literalContactValue, slope, curvature, rowData, contactLo, endpointInterceptLo] at h ⊢
    exact h
  · have h := E_13_10_second
    norm_num [supportContactValue, literalContactValue, slope, curvature, rowData, contactLo, endpointInterceptLo] at h ⊢
    exact h
  · have h := E_29_20_first
    norm_num [supportContactValue, literalContactValue, slope, curvature, rowData, contactLo, endpointInterceptLo] at h ⊢
    exact h
  · have h := E_29_20_second
    norm_num [supportContactValue, literalContactValue, slope, curvature, rowData, contactLo, endpointInterceptLo] at h ⊢
    exact h
  · have h := H_lo_first
    norm_num [supportContactValue, literalContactValue, slope, curvature, rowData, contactLo, endpointInterceptLo] at h ⊢
    exact h
  · have h := H_lo_second
    norm_num [supportContactValue, literalContactValue, slope, curvature, rowData, contactLo, endpointInterceptLo] at h ⊢
    exact h
#print axioms endpointContactLo
theorem endpointContactHi (r : Row) (s : Support) :
    supportContactValue r s (rowData r).hi (contactHi r s) < endpointInterceptHi r s := by
  cases r <;> cases s
  · have h := D_hi_first
    norm_num [supportContactValue, literalContactValue, slope, curvature, rowData, contactHi, endpointInterceptHi] at h ⊢
    exact h
  · have h := D_hi_second
    norm_num [supportContactValue, literalContactValue, slope, curvature, rowData, contactHi, endpointInterceptHi] at h ⊢
    exact h
  · have h := E_29_20_first
    norm_num [supportContactValue, literalContactValue, slope, curvature, rowData, contactHi, endpointInterceptHi] at h ⊢
    exact h
  · have h := E_29_20_second
    norm_num [supportContactValue, literalContactValue, slope, curvature, rowData, contactHi, endpointInterceptHi] at h ⊢
    exact h
  · have h := E_8_5_first
    norm_num [supportContactValue, literalContactValue, slope, curvature, rowData, contactHi, endpointInterceptHi] at h ⊢
    exact h
  · have h := E_8_5_second
    norm_num [supportContactValue, literalContactValue, slope, curvature, rowData, contactHi, endpointInterceptHi] at h ⊢
    exact h
  · have h := H_hi_first
    norm_num [supportContactValue, literalContactValue, slope, curvature, rowData, contactHi, endpointInterceptHi] at h ⊢
    exact h
  · have h := H_hi_second
    norm_num [supportContactValue, literalContactValue, slope, curvature, rowData, contactHi, endpointInterceptHi] at h ⊢
    exact h
#print axioms endpointContactHi
end
end F4Unified.LightConstruction.ContactChecks
