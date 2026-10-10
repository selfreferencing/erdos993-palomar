module

public import F4Heavy.Analysis.BernsteinSquareSemantics
public import F4Heavy.Finite.Reconstruction.Function38
public import Mathlib.Tactic.IntervalCases
public import F4Heavy.Finite.Certificates.Part022
public import F4Heavy.Finite.Certificates.Part023
public import F4Heavy.Finite.Certificates.Part024
public import F4Heavy.Finite.Certificates.Part025
public import F4Heavy.Finite.Certificates.Part026

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Heavy.Finite

def dh_special_H_r6_1_1_V4_00_coefficients : List Fraction :=
  [⟨2015482051749933969073151803414077789617446114168481758264322072088403266051, 262144⟩, ⟨-2443809541218413096885718205104054815858017090190829804989102051495508380157, 131072⟩, ⟨-141017709620997435469097329343157447314154350057184322379990880001260118370877, 262144⟩, ⟨-952692493383169980313630643082693949135019812599578475075030601293343935411, 1024⟩, ⟨42337512522879888229105715939919095200928414055155628097769090166883987359183, 4096⟩, ⟨127376775640297322288468278788885025112181591854817178582613807407665330314943, 2048⟩, ⟨167378915509829436598147641755806292653583849128251133752496968531584229405357, 1024⟩, ⟨31967600371357953515954194694084466027162206811834861630935976466187978422845, 128⟩, ⟨1889122721698700371159752042921717835520047258884753213493905691457134255071, 8⟩, ⟨136573944159040783794632583025936729811411880113612721571149919626920434188, 1⟩, ⟨44380963487281213403939204365509983594409293489009324810458402841138755101, 1⟩, ⟨6215748396112285280068034102192317111758563780458355481489927296876273976, 1⟩]

def dh_special_H_r6_1_1_V4_00_quotient : List Fraction :=
  [⟨7583293699038033175634298756297663359464320155950513363028468430586732218405711, 16777216⟩, ⟨12998275334737882877115478740000342145475525890620919181089006863389413180720539, 2097152⟩, ⟨9388123554693896708574429645740944303380853221631528366830128976111446567299239, 262144⟩, ⟨3826857548201178420351064994448189253457659976438200835617588417384711574156211, 32768⟩, ⟨975192343172772978790466163310256296393885230774833502662269629338551772000895, 4096⟩, ⟨161555548389124693845359792794483741125015954788541027028771759815037254884667, 512⟩, ⟨17434415644794155292843989301936356470482075315253086405261764417859655389867, 64⟩, ⟨1183684385895430804144964585726835924597023089304592305495674885433969586447, 8⟩, ⟨45934900586309284723956212891058062872348934434123913680830884665357823595, 1⟩, ⟨6215748396112285280068034102192317111758563780458355481489927296876273976, 1⟩]

theorem dh_special_H_r6_1_1_V4_00 (x : ℝ) (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < realHorner ((activityControlPolynomial numerator_H_r6_1_1_V4 ⟨0, 1⟩ ⟨1, 7⟩ 12 11 0).map fractionValue) x := by
  have hp : ∀ c ∈ (activityControlPolynomial numerator_H_r6_1_1_V4 ⟨0, 1⟩ ⟨1, 7⟩ 12 11 0), 0 < c.den :=
    activityControlPolynomial_den_pos numerator_H_r6_1_1_V4 ⟨0, 1⟩ ⟨1, 7⟩ 12 11 0
      (by norm_num [numerator_H_r6_1_1_V4]) (by norm_num) (by norm_num)
  have hboth := cert_0906_H_r6_1_1_V4_square_discriminant_and_closed_endpoint_0
  rw [Bool.and_eq_true] at hboth
  apply weightedBernstein_positive_closed (activityControlPolynomial numerator_H_r6_1_1_V4 ⟨0, 1⟩ ⟨1, 7⟩ 12 11 0) dh_special_H_r6_1_1_V4_00_coefficients ⟨1, 4⟩ Fraction.one 11 x hp
  · norm_num [Fraction.one, Fraction.ofInt]
  · norm_num [Fraction.one, Fraction.ofInt]
  · simp [activityControlPolynomial]
  · norm_num [fractionValue, Fraction.one, Fraction.ofInt]
  · simpa only [fractionValue, Int.cast_ofNat, Int.cast_one, Nat.cast_ofNat, Nat.cast_one] using hx.1
  · simpa only [fractionValue_one] using hx.2
  · exact reconstruct_292_H_r6_1_1_V4
  · intro z hz
    apply squareReconstruction_positive dh_special_H_r6_1_1_V4_00_coefficients dh_special_H_r6_1_1_V4_00_quotient ⟨1, 8⟩ ⟨84492969515056206157868590263707927205811012152071435870321068435004558537325, 268435456⟩ ⟨-334148906869471537057856669431567557985495079075302175340910502947349325189885, 134217728⟩ z
    · norm_num [dh_special_H_r6_1_1_V4_00_quotient]
    · norm_num
    · norm_num
    · norm_num
    · simp [dh_special_H_r6_1_1_V4_00_quotient]
    · exact hz
    · intro c hc
      simp only [dh_special_H_r6_1_1_V4_00_quotient, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_0896_H_r6_1_1_V4_square_quotient_coefficient_0_0
      · exact cert_0897_H_r6_1_1_V4_square_quotient_coefficient_0_1
      · exact cert_0898_H_r6_1_1_V4_square_quotient_coefficient_0_2
      · exact cert_0899_H_r6_1_1_V4_square_quotient_coefficient_0_3
      · exact cert_0900_H_r6_1_1_V4_square_quotient_coefficient_0_4
      · exact cert_0901_H_r6_1_1_V4_square_quotient_coefficient_0_5
      · exact cert_0902_H_r6_1_1_V4_square_quotient_coefficient_0_6
      · exact cert_0903_H_r6_1_1_V4_square_quotient_coefficient_0_7
      · exact cert_0904_H_r6_1_1_V4_square_quotient_coefficient_0_8
      · exact cert_0905_H_r6_1_1_V4_square_quotient_coefficient_0_9
    · exact hboth.1
    · exact reconstruct_292_H_r6_1_1_V4_square_identity
  · exact fraction_positive_sound _ hboth.2

def dh_special_H_r6_1_1_V4_01_coefficients : List Fraction :=
  [⟨100666749045955282178890332599587146624244129421481161128334137502206942739997, 7340032⟩, ⟨316858987834258772066089147023586751428201302513463599166373914864392026505741, 40370176⟩, ⟨1689981621360659689300988857877993393436434737538629686105187173632265893481501, 403701760⟩, ⟨167625290340992235262911060657278539723274901653570155534415062325277201835293, 12615680⟩, ⟨693441988626011724106983007940985187910153208538471017184689514893407887148307, 12615680⟩, ⟨203742289727442989619713601651836924580641226723170830373104563004500884402661, 1261568⟩, ⟨240133125043322523468522752135126553214866031261802046120778071366518745952359, 630784⟩, ⟨61370184991976267144087395191573465138467675968066915883599771722546221604513, 78848⟩, ⟨17734900448090444635539009161690166277682618704324326087074094980950786384119, 12320⟩, ⟨950239287009962590599974915272093206400782149154775393953263042755500219444, 385⟩, ⟨111551969903738467139503302290019711992465031555230996658707435609680323897, 28⟩, ⟨42812879153966206949259396081651145054703181487700881390502617861308096618, 7⟩]

theorem dh_special_H_r6_1_1_V4_01 (x : ℝ) (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < realHorner ((activityControlPolynomial numerator_H_r6_1_1_V4 ⟨0, 1⟩ ⟨1, 7⟩ 12 11 1).map fractionValue) x := by
  have hp : ∀ c ∈ (activityControlPolynomial numerator_H_r6_1_1_V4 ⟨0, 1⟩ ⟨1, 7⟩ 12 11 1), 0 < c.den :=
    activityControlPolynomial_den_pos numerator_H_r6_1_1_V4 ⟨0, 1⟩ ⟨1, 7⟩ 12 11 1
      (by norm_num [numerator_H_r6_1_1_V4]) (by norm_num) (by norm_num)
  apply bernstein_positive_of_allEq (activityControlPolynomial numerator_H_r6_1_1_V4 ⟨0, 1⟩ ⟨1, 7⟩ 12 11 1) dh_special_H_r6_1_1_V4_01_coefficients ⟨1, 4⟩ Fraction.one 11 x hp
  · norm_num [Fraction.one, Fraction.ofInt]
  · norm_num [Fraction.one, Fraction.ofInt]
  · simp [activityControlPolynomial]
  · norm_num [fractionValue, Fraction.one, Fraction.ofInt]
  · simpa only [fractionValue, Int.cast_ofNat, Int.cast_one, Nat.cast_ofNat, Nat.cast_one] using hx.1
  · simpa only [fractionValue_one] using hx.2
  · exact reconstruct_293_H_r6_1_1_V4
  · intro c hc
    simp only [dh_special_H_r6_1_1_V4_01_coefficients, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cert_0907_H_r6_1_1_V4_positive_parent_control_1_0
    · exact cert_0908_H_r6_1_1_V4_positive_parent_control_1_1
    · exact cert_0909_H_r6_1_1_V4_positive_parent_control_1_2
    · exact cert_0910_H_r6_1_1_V4_positive_parent_control_1_3
    · exact cert_0911_H_r6_1_1_V4_positive_parent_control_1_4
    · exact cert_0912_H_r6_1_1_V4_positive_parent_control_1_5
    · exact cert_0913_H_r6_1_1_V4_positive_parent_control_1_6
    · exact cert_0914_H_r6_1_1_V4_positive_parent_control_1_7
    · exact cert_0915_H_r6_1_1_V4_positive_parent_control_1_8
    · exact cert_0916_H_r6_1_1_V4_positive_parent_control_1_9
    · exact cert_0917_H_r6_1_1_V4_positive_parent_control_1_10
    · exact cert_0918_H_r6_1_1_V4_positive_parent_control_1_11

def dh_special_H_r6_1_1_V4_02_coefficients : List Fraction :=
  [⟨2678140652243154251433788206584879014599216724460696285815111723421728733510793, 141295616⟩, ⟨12622865696162470522390250627754360710538712860353655494839658621491406967806689, 777125888⟩, ⟨2334710044808154706398569081916515194948436966294366090246553155334878057377951, 141295616⟩, ⟨14551995203450198288915683165679813422703649295451031866510958014053046056422313, 485703680⟩, ⟨18349703009056392436560096255130405788586488904425688068188369294518025257278731, 242851840⟩, ⟨4475638481766643811485779906636739308671744766432453213541157361197085459238493, 24285184⟩, ⟨4883317236119167809115144379465355216782754933880288928454178283462860228624651, 12142592⟩, ⟨6015888583071238824173672510827302852176664286270778590903764847588947309410599, 7589120⟩, ⟨341134893448412644838636413403401220016297913223386214111744912715350548990493, 237160⟩, ⟨14470425352207662847537130190270456620786160215544872956597403680838484742322, 5929⟩, ⟨23222845060137028024700006402291085328407871771279655252073303320079227375183, 5929⟩, ⟨3231180312802354929592313970960943389568227542919715742802032704890522307672, 539⟩]

theorem dh_special_H_r6_1_1_V4_02 (x : ℝ) (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < realHorner ((activityControlPolynomial numerator_H_r6_1_1_V4 ⟨0, 1⟩ ⟨1, 7⟩ 12 11 2).map fractionValue) x := by
  have hp : ∀ c ∈ (activityControlPolynomial numerator_H_r6_1_1_V4 ⟨0, 1⟩ ⟨1, 7⟩ 12 11 2), 0 < c.den :=
    activityControlPolynomial_den_pos numerator_H_r6_1_1_V4 ⟨0, 1⟩ ⟨1, 7⟩ 12 11 2
      (by norm_num [numerator_H_r6_1_1_V4]) (by norm_num) (by norm_num)
  apply bernstein_positive_of_allEq (activityControlPolynomial numerator_H_r6_1_1_V4 ⟨0, 1⟩ ⟨1, 7⟩ 12 11 2) dh_special_H_r6_1_1_V4_02_coefficients ⟨1, 4⟩ Fraction.one 11 x hp
  · norm_num [Fraction.one, Fraction.ofInt]
  · norm_num [Fraction.one, Fraction.ofInt]
  · simp [activityControlPolynomial]
  · norm_num [fractionValue, Fraction.one, Fraction.ofInt]
  · simpa only [fractionValue, Int.cast_ofNat, Int.cast_one, Nat.cast_ofNat, Nat.cast_one] using hx.1
  · simpa only [fractionValue_one] using hx.2
  · exact reconstruct_294_H_r6_1_1_V4
  · intro c hc
    simp only [dh_special_H_r6_1_1_V4_02_coefficients, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cert_0919_H_r6_1_1_V4_positive_parent_control_2_0
    · exact cert_0920_H_r6_1_1_V4_positive_parent_control_2_1
    · exact cert_0921_H_r6_1_1_V4_positive_parent_control_2_2
    · exact cert_0922_H_r6_1_1_V4_positive_parent_control_2_3
    · exact cert_0923_H_r6_1_1_V4_positive_parent_control_2_4
    · exact cert_0924_H_r6_1_1_V4_positive_parent_control_2_5
    · exact cert_0925_H_r6_1_1_V4_positive_parent_control_2_6
    · exact cert_0926_H_r6_1_1_V4_positive_parent_control_2_7
    · exact cert_0927_H_r6_1_1_V4_positive_parent_control_2_8
    · exact cert_0928_H_r6_1_1_V4_positive_parent_control_2_9
    · exact cert_0929_H_r6_1_1_V4_positive_parent_control_2_10
    · exact cert_0930_H_r6_1_1_V4_positive_parent_control_2_11

def dh_special_H_r6_1_1_V4_03_coefficients : List Fraction :=
  [⟨11576257903591298171361750257140149499778066702439520551720397192758659654195337, 494534656⟩, ⟨319388187605773605386760544388293372172733633889511585226224067799401572619844977, 13599703040⟩, ⟨3701973151415719140401179115837260519679609844094365376869213098974929121815775869, 135997030400⟩, ⟨754092234172405356484808383178041925293351383777305143232207115935208938277168219, 16999628800⟩, ⟨395490475847334994547517712699789596116736385014091349263970915182490237774585337, 4249907200⟩, ⟨86248723144784713426913355267486102503967611067748775973578922494336345416659459, 424990720⟩, ⟨12692637803587676808754277853171929480478329784813125829329806681869481971094737, 30356480⟩, ⟨13276678781696552977449450209900269144265912318266163864992093658239056139013559, 16601200⟩, ⟨1481243871248518129685421185796995716349576556943923689339520676481287634582634, 1037575⟩, ⟨2490378328187995938285915785937434275891501286716282276642896814259160428249202, 1037575⟩, ⟨795309745123564877257707267417796211715608219990243947495756806292657409484462, 207515⟩, ⟨110375153192529122644842344922397309300226446371902239898568993933657432288288, 18865⟩]

theorem dh_special_H_r6_1_1_V4_03 (x : ℝ) (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < realHorner ((activityControlPolynomial numerator_H_r6_1_1_V4 ⟨0, 1⟩ ⟨1, 7⟩ 12 11 3).map fractionValue) x := by
  have hp : ∀ c ∈ (activityControlPolynomial numerator_H_r6_1_1_V4 ⟨0, 1⟩ ⟨1, 7⟩ 12 11 3), 0 < c.den :=
    activityControlPolynomial_den_pos numerator_H_r6_1_1_V4 ⟨0, 1⟩ ⟨1, 7⟩ 12 11 3
      (by norm_num [numerator_H_r6_1_1_V4]) (by norm_num) (by norm_num)
  apply bernstein_positive_of_allEq (activityControlPolynomial numerator_H_r6_1_1_V4 ⟨0, 1⟩ ⟨1, 7⟩ 12 11 3) dh_special_H_r6_1_1_V4_03_coefficients ⟨1, 4⟩ Fraction.one 11 x hp
  · norm_num [Fraction.one, Fraction.ofInt]
  · norm_num [Fraction.one, Fraction.ofInt]
  · simp [activityControlPolynomial]
  · norm_num [fractionValue, Fraction.one, Fraction.ofInt]
  · simpa only [fractionValue, Int.cast_ofNat, Int.cast_one, Nat.cast_ofNat, Nat.cast_one] using hx.1
  · simpa only [fractionValue_one] using hx.2
  · exact reconstruct_295_H_r6_1_1_V4
  · intro c hc
    simp only [dh_special_H_r6_1_1_V4_03_coefficients, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cert_0931_H_r6_1_1_V4_positive_parent_control_3_0
    · exact cert_0932_H_r6_1_1_V4_positive_parent_control_3_1
    · exact cert_0933_H_r6_1_1_V4_positive_parent_control_3_2
    · exact cert_0934_H_r6_1_1_V4_positive_parent_control_3_3
    · exact cert_0935_H_r6_1_1_V4_positive_parent_control_3_4
    · exact cert_0936_H_r6_1_1_V4_positive_parent_control_3_5
    · exact cert_0937_H_r6_1_1_V4_positive_parent_control_3_6
    · exact cert_0938_H_r6_1_1_V4_positive_parent_control_3_7
    · exact cert_0939_H_r6_1_1_V4_positive_parent_control_3_8
    · exact cert_0940_H_r6_1_1_V4_positive_parent_control_3_9
    · exact cert_0941_H_r6_1_1_V4_positive_parent_control_3_10
    · exact cert_0942_H_r6_1_1_V4_positive_parent_control_3_11

def dh_special_H_r6_1_1_V4_04_coefficients : List Fraction :=
  [⟨29297489311188777971258750676773899371796679574156670066882201871967637512815899, 1081794560⟩, ⟨175978317830086773379243773023412680632189329896497287850976663922155875417998431, 5949870080⟩, ⟨39242169453704289812148441239924827879805563056749207170219153483574777219887597, 1081794560⟩, ⟨419988738228896934165216597432686704231972662138355842360611027955926526815848667, 7437337600⟩, ⟨199762068806983566232142016107941722195618019970312285801877029882210554369692973, 1859334400⟩, ⟨8084141804290578170161698790011089615623831664132312427166244679955585785343993, 37186688⟩, ⟨39834038749322631512251746037549233522222900512640737636227336600739488533830281, 92966720⟩, ⟨23222484151430535206630155857543411319675117524839160388696617918297805964559637, 29052100⟩, ⟨2043640880749960408891171803253753413179389115164708123884675075575830611986632, 1452605⟩, ⟨17043132090491991655613411383487286478132607153940948514903500428649621596682848, 7263025⟩, ⟨5419161406029388411461843654525277553690810626451893229124688556324829955537952, 1452605⟩, ⟨750517980549657799708203422177463508609537371830785228349118386839024489278464, 132055⟩]

theorem dh_special_H_r6_1_1_V4_04 (x : ℝ) (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < realHorner ((activityControlPolynomial numerator_H_r6_1_1_V4 ⟨0, 1⟩ ⟨1, 7⟩ 12 11 4).map fractionValue) x := by
  have hp : ∀ c ∈ (activityControlPolynomial numerator_H_r6_1_1_V4 ⟨0, 1⟩ ⟨1, 7⟩ 12 11 4), 0 < c.den :=
    activityControlPolynomial_den_pos numerator_H_r6_1_1_V4 ⟨0, 1⟩ ⟨1, 7⟩ 12 11 4
      (by norm_num [numerator_H_r6_1_1_V4]) (by norm_num) (by norm_num)
  apply bernstein_positive_of_allEq (activityControlPolynomial numerator_H_r6_1_1_V4 ⟨0, 1⟩ ⟨1, 7⟩ 12 11 4) dh_special_H_r6_1_1_V4_04_coefficients ⟨1, 4⟩ Fraction.one 11 x hp
  · norm_num [Fraction.one, Fraction.ofInt]
  · norm_num [Fraction.one, Fraction.ofInt]
  · simp [activityControlPolynomial]
  · norm_num [fractionValue, Fraction.one, Fraction.ofInt]
  · simpa only [fractionValue, Int.cast_ofNat, Int.cast_one, Nat.cast_ofNat, Nat.cast_one] using hx.1
  · simpa only [fractionValue_one] using hx.2
  · exact reconstruct_296_H_r6_1_1_V4
  · intro c hc
    simp only [dh_special_H_r6_1_1_V4_04_coefficients, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cert_0943_H_r6_1_1_V4_positive_parent_control_4_0
    · exact cert_0944_H_r6_1_1_V4_positive_parent_control_4_1
    · exact cert_0945_H_r6_1_1_V4_positive_parent_control_4_2
    · exact cert_0946_H_r6_1_1_V4_positive_parent_control_4_3
    · exact cert_0947_H_r6_1_1_V4_positive_parent_control_4_4
    · exact cert_0948_H_r6_1_1_V4_positive_parent_control_4_5
    · exact cert_0949_H_r6_1_1_V4_positive_parent_control_4_6
    · exact cert_0950_H_r6_1_1_V4_positive_parent_control_4_7
    · exact cert_0951_H_r6_1_1_V4_positive_parent_control_4_8
    · exact cert_0952_H_r6_1_1_V4_positive_parent_control_4_9
    · exact cert_0953_H_r6_1_1_V4_positive_parent_control_4_10
    · exact cert_0954_H_r6_1_1_V4_positive_parent_control_4_11

def dh_special_H_r6_1_1_V4_05_coefficients : List Fraction :=
  [⟨103797046129712221896069707799051412767295223298995064017137478711314613608895845, 3461742592⟩, ⟨179279342060838578895151231761998283182182907321521230884811917151995493256116109, 5192613888⟩, ⟨24955031254121158723294248230396800455251955863485039188005466458497957558443970159, 571187527680⟩, ⟨197211819042420695479695770201491645488671229947993287970979870497780330109288579, 2974935040⟩, ⟨2118442133304929741509265980099095879139288308933705739770978637683374238170944057, 17849610240⟩, ⟨406290851864000308111253637413008000332247645433136327596036538784607044315678367, 1784961024⟩, ⟨902082260289129876884596987146068888111823985957980247119350729931343633612613177, 2082454528⟩, ⟨63063396626750408079404747662732600228105471020862789194215110026896401426915109, 79685760⟩, ⟨23987183217116285070737771744060821240743399996003420798998181446761020807422849, 17431260⟩, ⟨3311178355625004516947987701936703453939144145907163379040403610320748117025112, 1452605⟩, ⟨3146973458852511952837060179210458392882397487860398562653408258299414809217314, 871563⟩, ⟨39557400859698478543048301948697899171553793048672957505423941034960538018064, 7203⟩]

theorem dh_special_H_r6_1_1_V4_05 (x : ℝ) (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < realHorner ((activityControlPolynomial numerator_H_r6_1_1_V4 ⟨0, 1⟩ ⟨1, 7⟩ 12 11 5).map fractionValue) x := by
  have hp : ∀ c ∈ (activityControlPolynomial numerator_H_r6_1_1_V4 ⟨0, 1⟩ ⟨1, 7⟩ 12 11 5), 0 < c.den :=
    activityControlPolynomial_den_pos numerator_H_r6_1_1_V4 ⟨0, 1⟩ ⟨1, 7⟩ 12 11 5
      (by norm_num [numerator_H_r6_1_1_V4]) (by norm_num) (by norm_num)
  apply bernstein_positive_of_allEq (activityControlPolynomial numerator_H_r6_1_1_V4 ⟨0, 1⟩ ⟨1, 7⟩ 12 11 5) dh_special_H_r6_1_1_V4_05_coefficients ⟨1, 4⟩ Fraction.one 11 x hp
  · norm_num [Fraction.one, Fraction.ofInt]
  · norm_num [Fraction.one, Fraction.ofInt]
  · simp [activityControlPolynomial]
  · norm_num [fractionValue, Fraction.one, Fraction.ofInt]
  · simpa only [fractionValue, Int.cast_ofNat, Int.cast_one, Nat.cast_ofNat, Nat.cast_one] using hx.1
  · simpa only [fractionValue_one] using hx.2
  · exact reconstruct_297_H_r6_1_1_V4
  · intro c hc
    simp only [dh_special_H_r6_1_1_V4_05_coefficients, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cert_0955_H_r6_1_1_V4_positive_parent_control_5_0
    · exact cert_0956_H_r6_1_1_V4_positive_parent_control_5_1
    · exact cert_0957_H_r6_1_1_V4_positive_parent_control_5_2
    · exact cert_0958_H_r6_1_1_V4_positive_parent_control_5_3
    · exact cert_0959_H_r6_1_1_V4_positive_parent_control_5_4
    · exact cert_0960_H_r6_1_1_V4_positive_parent_control_5_5
    · exact cert_0961_H_r6_1_1_V4_positive_parent_control_5_6
    · exact cert_0962_H_r6_1_1_V4_positive_parent_control_5_7
    · exact cert_0963_H_r6_1_1_V4_positive_parent_control_5_8
    · exact cert_0964_H_r6_1_1_V4_positive_parent_control_5_9
    · exact cert_0965_H_r6_1_1_V4_positive_parent_control_5_10
    · exact cert_0966_H_r6_1_1_V4_positive_parent_control_5_11

def dh_special_H_r6_1_1_V4_06_coefficients : List Fraction :=
  [⟨4086909697773569119642263328896023275799749152565281237145271573742890123803426789, 127219040256⟩, ⟨26829532207292654013314930075563040518688532704068155602739267590191989130017892093, 699704721408⟩, ⟨346188082135048628185889041907306757628868919009078777721199405924195340755539799941, 6997047214080⟩, ⟨32287048864059881642478761828294269795032130236447541899350550806103885476333591281, 437315450880⟩, ⟨27725184624739148824147053804508453862525943112151887834603315368479311667381014271, 218657725440⟩, ⟨5108092145653360867009516633309456103165376056492717137721997491524359369847385657, 21865772544⟩, ⟨4725339597364730983849437114096537107389495620791484688261748945242432222995346975, 10932886272⟩, ⟨5301606579038855996675938816528331383920790443782190637222792622397726410977680739, 6833053920⟩, ⟨57020451567302183441894927883537394244014787062005767783397965253230608652534173, 42706587⟩, ⟨469505717667808428724330864401054187393756162002618090542976318241541877704092496, 213532935⟩, ⟨148295215878172575295758798795195218414180528614089683533636194121985633175551896, 42706587⟩, ⟨20481433676375180726273018495832279760908590536272256600511149583926174002110912, 3882417⟩]

theorem dh_special_H_r6_1_1_V4_06 (x : ℝ) (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < realHorner ((activityControlPolynomial numerator_H_r6_1_1_V4 ⟨0, 1⟩ ⟨1, 7⟩ 12 11 6).map fractionValue) x := by
  have hp : ∀ c ∈ (activityControlPolynomial numerator_H_r6_1_1_V4 ⟨0, 1⟩ ⟨1, 7⟩ 12 11 6), 0 < c.den :=
    activityControlPolynomial_den_pos numerator_H_r6_1_1_V4 ⟨0, 1⟩ ⟨1, 7⟩ 12 11 6
      (by norm_num [numerator_H_r6_1_1_V4]) (by norm_num) (by norm_num)
  apply bernstein_positive_of_allEq (activityControlPolynomial numerator_H_r6_1_1_V4 ⟨0, 1⟩ ⟨1, 7⟩ 12 11 6) dh_special_H_r6_1_1_V4_06_coefficients ⟨1, 4⟩ Fraction.one 11 x hp
  · norm_num [Fraction.one, Fraction.ofInt]
  · norm_num [Fraction.one, Fraction.ofInt]
  · simp [activityControlPolynomial]
  · norm_num [fractionValue, Fraction.one, Fraction.ofInt]
  · simpa only [fractionValue, Int.cast_ofNat, Int.cast_one, Nat.cast_ofNat, Nat.cast_one] using hx.1
  · simpa only [fractionValue_one] using hx.2
  · exact reconstruct_298_H_r6_1_1_V4
  · intro c hc
    simp only [dh_special_H_r6_1_1_V4_06_coefficients, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cert_0967_H_r6_1_1_V4_positive_parent_control_6_0
    · exact cert_0968_H_r6_1_1_V4_positive_parent_control_6_1
    · exact cert_0969_H_r6_1_1_V4_positive_parent_control_6_2
    · exact cert_0970_H_r6_1_1_V4_positive_parent_control_6_3
    · exact cert_0971_H_r6_1_1_V4_positive_parent_control_6_4
    · exact cert_0972_H_r6_1_1_V4_positive_parent_control_6_5
    · exact cert_0973_H_r6_1_1_V4_positive_parent_control_6_6
    · exact cert_0974_H_r6_1_1_V4_positive_parent_control_6_7
    · exact cert_0975_H_r6_1_1_V4_positive_parent_control_6_8
    · exact cert_0976_H_r6_1_1_V4_positive_parent_control_6_9
    · exact cert_0977_H_r6_1_1_V4_positive_parent_control_6_10
    · exact cert_0978_H_r6_1_1_V4_positive_parent_control_6_11

def dh_special_H_r6_1_1_V4_07_coefficients : List Fraction :=
  [⟨7462614024204120876661110632043989780351616167866561337430444938417952842581737691, 222633320448⟩, ⟨16754487565140759071004847858547568926021963982133345071350918044749651503217722155, 408161087488⟩, ⟨656979969131839586052205145190478333998681360083403045384277644390617526824562141683, 12244832624640⟩, ⟨242161500194992746742442156636597712226524399096015401506275379685761659824794090801, 3061208156160⟩, ⟨8405469702573628034840918465120290547665699176302985763263410247658500641827790991, 63775169920⟩, ⟨204705217254274698635794920143564781335821693022389687588982193094767929888941049, 869661408⟩, ⟨8142356887715346838602641317335933070678207370558323960662826953880398641079762481, 19132550976⟩, ⟨6000892233794406261150387288447055840482976719163371819273469374799641334872120289, 7971896240⟩, ⟨383857267024497024120841126062058906435015332353470626854098899694634559395737946, 298946109⟩, ⟨629064562170851518371559621257013462364876046308877632470177051951303888015686832, 298946109⟩, ⟨330384716865413313192074503761302416379567679884208455640569969900315428590315808, 99648703⟩, ⟨136803051341135229980353470940749968685968256371554511075712776770026479374484608, 27176919⟩]

theorem dh_special_H_r6_1_1_V4_07 (x : ℝ) (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < realHorner ((activityControlPolynomial numerator_H_r6_1_1_V4 ⟨0, 1⟩ ⟨1, 7⟩ 12 11 7).map fractionValue) x := by
  have hp : ∀ c ∈ (activityControlPolynomial numerator_H_r6_1_1_V4 ⟨0, 1⟩ ⟨1, 7⟩ 12 11 7), 0 < c.den :=
    activityControlPolynomial_den_pos numerator_H_r6_1_1_V4 ⟨0, 1⟩ ⟨1, 7⟩ 12 11 7
      (by norm_num [numerator_H_r6_1_1_V4]) (by norm_num) (by norm_num)
  apply bernstein_positive_of_allEq (activityControlPolynomial numerator_H_r6_1_1_V4 ⟨0, 1⟩ ⟨1, 7⟩ 12 11 7) dh_special_H_r6_1_1_V4_07_coefficients ⟨1, 4⟩ Fraction.one 11 x hp
  · norm_num [Fraction.one, Fraction.ofInt]
  · norm_num [Fraction.one, Fraction.ofInt]
  · simp [activityControlPolynomial]
  · norm_num [fractionValue, Fraction.one, Fraction.ofInt]
  · simpa only [fractionValue, Int.cast_ofNat, Int.cast_one, Nat.cast_ofNat, Nat.cast_one] using hx.1
  · simpa only [fractionValue_one] using hx.2
  · exact reconstruct_299_H_r6_1_1_V4
  · intro c hc
    simp only [dh_special_H_r6_1_1_V4_07_coefficients, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cert_0979_H_r6_1_1_V4_positive_parent_control_7_0
    · exact cert_0980_H_r6_1_1_V4_positive_parent_control_7_1
    · exact cert_0981_H_r6_1_1_V4_positive_parent_control_7_2
    · exact cert_0982_H_r6_1_1_V4_positive_parent_control_7_3
    · exact cert_0983_H_r6_1_1_V4_positive_parent_control_7_4
    · exact cert_0984_H_r6_1_1_V4_positive_parent_control_7_5
    · exact cert_0985_H_r6_1_1_V4_positive_parent_control_7_6
    · exact cert_0986_H_r6_1_1_V4_positive_parent_control_7_7
    · exact cert_0987_H_r6_1_1_V4_positive_parent_control_7_8
    · exact cert_0988_H_r6_1_1_V4_positive_parent_control_7_9
    · exact cert_0989_H_r6_1_1_V4_positive_parent_control_7_10
    · exact cert_0990_H_r6_1_1_V4_positive_parent_control_7_11

def dh_special_H_r6_1_1_V4_08_coefficients : List Fraction :=
  [⟨156084786988013255174949780199639778143015441309947564801108048418279227687411359, 4565722392⟩, ⟨4285216711698010969388559035907227418568441474766462163177504051974913639802300445, 100445892624⟩, ⟨35311884472119521055398569868081854032401120411590253360355195667868794624453550033, 627786828900⟩, ⟨206292688445379198580095682157900149185842271815333407116147802009272826652573388383, 2511147315600⟩, ⟨167896156496493367586265460429868339060859893134321267625604622410987836736087275251, 1255573657800⟩, ⟨14625968920499602591058848852995649877914903560409945954375137959772800703631552979, 62778682890⟩, ⟨2594695654095172918551454505875219230567229730703994460389008508299776638404020078, 6277868289⟩, ⟨113326957563642874974617523298310037565062816881124686569451083882349716315580248832, 156946707225⟩, ⟨191901888898037404450444298651473048623120577574722015887656711782313999847577548032, 156946707225⟩, ⟨313268078733057726898447555584516070397630458651409242608544381057247602146969863168, 156946707225⟩, ⟨19711316223103868913340794565992682223739198717811966495353264217520674443286999040, 6277868289⟩, ⟨13601654775832799916913038314390877536633214667209632996088963513884116222985633792, 2853576495⟩]

theorem dh_special_H_r6_1_1_V4_08 (x : ℝ) (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < realHorner ((activityControlPolynomial numerator_H_r6_1_1_V4 ⟨0, 1⟩ ⟨1, 7⟩ 12 11 8).map fractionValue) x := by
  have hp : ∀ c ∈ (activityControlPolynomial numerator_H_r6_1_1_V4 ⟨0, 1⟩ ⟨1, 7⟩ 12 11 8), 0 < c.den :=
    activityControlPolynomial_den_pos numerator_H_r6_1_1_V4 ⟨0, 1⟩ ⟨1, 7⟩ 12 11 8
      (by norm_num [numerator_H_r6_1_1_V4]) (by norm_num) (by norm_num)
  apply bernstein_positive_of_allEq (activityControlPolynomial numerator_H_r6_1_1_V4 ⟨0, 1⟩ ⟨1, 7⟩ 12 11 8) dh_special_H_r6_1_1_V4_08_coefficients ⟨1, 4⟩ Fraction.one 11 x hp
  · norm_num [Fraction.one, Fraction.ofInt]
  · norm_num [Fraction.one, Fraction.ofInt]
  · simp [activityControlPolynomial]
  · norm_num [fractionValue, Fraction.one, Fraction.ofInt]
  · simpa only [fractionValue, Int.cast_ofNat, Int.cast_one, Nat.cast_ofNat, Nat.cast_one] using hx.1
  · simpa only [fractionValue_one] using hx.2
  · exact reconstruct_300_H_r6_1_1_V4
  · intro c hc
    simp only [dh_special_H_r6_1_1_V4_08_coefficients, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cert_0991_H_r6_1_1_V4_positive_parent_control_8_0
    · exact cert_0992_H_r6_1_1_V4_positive_parent_control_8_1
    · exact cert_0993_H_r6_1_1_V4_positive_parent_control_8_2
    · exact cert_0994_H_r6_1_1_V4_positive_parent_control_8_3
    · exact cert_0995_H_r6_1_1_V4_positive_parent_control_8_4
    · exact cert_0996_H_r6_1_1_V4_positive_parent_control_8_5
    · exact cert_0997_H_r6_1_1_V4_positive_parent_control_8_6
    · exact cert_0998_H_r6_1_1_V4_positive_parent_control_8_7
    · exact cert_0999_H_r6_1_1_V4_positive_parent_control_8_8
    · exact cert_1000_H_r6_1_1_V4_positive_parent_control_8_9
    · exact cert_1001_H_r6_1_1_V4_positive_parent_control_8_10
    · exact cert_1002_H_r6_1_1_V4_positive_parent_control_8_11

def dh_special_H_r6_1_1_V4_09_coefficients : List Fraction :=
  [⟨2425089577915722115003061532197044557693231183606966743589929315582503050114264279, 71022348320⟩, ⟨16879193138639918185422975022771689307879565230531731937568393177309654719165796613, 390622915760⟩, ⟨223803718420094751108531038054704161649791417853376689100846331299482412322324176223, 3906229157600⟩, ⟨7368977389182361560591077675148908903364104295624302745515510475108856648187823951, 88777935400⟩, ⟨64752660878039433095956897443904620169529105356715159760169305103604421710854362183, 488278644700⟩, ⟨1105690589975978664954273015737928268723901875960550386039684086728949277620225915, 4882786447⟩, ⟨1931048676491357932988854891910158396976284329088637135858255495885177013208024080, 4882786447⟩, ⟨83484279699203541071460180346497722421292916968067745903490121946074663402541258144, 122069661175⟩, ⟨140539128306045461721372778236669083707026858867367673207484378650419973737743945216, 122069661175⟩, ⟨228762495512257908427694640891948952035460433785784966963884867582972160529660131328, 122069661175⟩, ⟨71907609004884022187545245817055762993310728987516617804829178463895702750249877504, 24413932235⟩, ⟨9928576756071901851204118461403262289637031151940221163078434992061471569959256064, 2219448385⟩]

theorem dh_special_H_r6_1_1_V4_09 (x : ℝ) (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < realHorner ((activityControlPolynomial numerator_H_r6_1_1_V4 ⟨0, 1⟩ ⟨1, 7⟩ 12 11 9).map fractionValue) x := by
  have hp : ∀ c ∈ (activityControlPolynomial numerator_H_r6_1_1_V4 ⟨0, 1⟩ ⟨1, 7⟩ 12 11 9), 0 < c.den :=
    activityControlPolynomial_den_pos numerator_H_r6_1_1_V4 ⟨0, 1⟩ ⟨1, 7⟩ 12 11 9
      (by norm_num [numerator_H_r6_1_1_V4]) (by norm_num) (by norm_num)
  apply bernstein_positive_of_allEq (activityControlPolynomial numerator_H_r6_1_1_V4 ⟨0, 1⟩ ⟨1, 7⟩ 12 11 9) dh_special_H_r6_1_1_V4_09_coefficients ⟨1, 4⟩ Fraction.one 11 x hp
  · norm_num [Fraction.one, Fraction.ofInt]
  · norm_num [Fraction.one, Fraction.ofInt]
  · simp [activityControlPolynomial]
  · norm_num [fractionValue, Fraction.one, Fraction.ofInt]
  · simpa only [fractionValue, Int.cast_ofNat, Int.cast_one, Nat.cast_ofNat, Nat.cast_one] using hx.1
  · simpa only [fractionValue_one] using hx.2
  · exact reconstruct_301_H_r6_1_1_V4
  · intro c hc
    simp only [dh_special_H_r6_1_1_V4_09_coefficients, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cert_1003_H_r6_1_1_V4_positive_parent_control_9_0
    · exact cert_1004_H_r6_1_1_V4_positive_parent_control_9_1
    · exact cert_1005_H_r6_1_1_V4_positive_parent_control_9_2
    · exact cert_1006_H_r6_1_1_V4_positive_parent_control_9_3
    · exact cert_1007_H_r6_1_1_V4_positive_parent_control_9_4
    · exact cert_1008_H_r6_1_1_V4_positive_parent_control_9_5
    · exact cert_1009_H_r6_1_1_V4_positive_parent_control_9_6
    · exact cert_1010_H_r6_1_1_V4_positive_parent_control_9_7
    · exact cert_1011_H_r6_1_1_V4_positive_parent_control_9_8
    · exact cert_1012_H_r6_1_1_V4_positive_parent_control_9_9
    · exact cert_1013_H_r6_1_1_V4_positive_parent_control_9_10
    · exact cert_1014_H_r6_1_1_V4_positive_parent_control_9_11

def dh_special_H_r6_1_1_V4_10_coefficients : List Fraction :=
  [⟨1246182899696165043880498756624451102967902272510729040578755870849835360647512707, 37286732868⟩, ⟨796592618909040983548285155270713180985626322861030523421681031056710196372168465, 18643366434⟩, ⟨10595556124698304612833726111418218141181943331865332314688353765060180081581799081, 186433664340⟩, ⟨41897767201518215218195082834367625744276734152728192390028631515893153303705532932, 512692576935⟩, ⟨5991315382021194343970402959903381977330317507727349502975100110281382954511929756, 46608416085⟩, ⟨22135888750833460974415371202295656596645237101464432760502432637903561171533180032, 102538515387⟩, ⟨5452090866512639844295827804742295112941978742595625522329757123481264282501757472, 14648359341⟩, ⟨327295325694785985600745783049202188525949647375340024818771673455770304701511260672, 512692576935⟩, ⟨109708994093155016352680049537557017277145212554471830965141248434747545347217973248, 102538515387⟩, ⟨178260632843573303629916492410875333608472542787224799061614115327598538386572673024, 102538515387⟩, ⟨280158816217688018374452402851788424712115281746348404918168941344161114869926395904, 102538515387⟩, ⟨38727180270149744522444230790069214175021648760051845911835518599279527858523865088, 9321683217⟩]

theorem dh_special_H_r6_1_1_V4_10 (x : ℝ) (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < realHorner ((activityControlPolynomial numerator_H_r6_1_1_V4 ⟨0, 1⟩ ⟨1, 7⟩ 12 11 10).map fractionValue) x := by
  have hp : ∀ c ∈ (activityControlPolynomial numerator_H_r6_1_1_V4 ⟨0, 1⟩ ⟨1, 7⟩ 12 11 10), 0 < c.den :=
    activityControlPolynomial_den_pos numerator_H_r6_1_1_V4 ⟨0, 1⟩ ⟨1, 7⟩ 12 11 10
      (by norm_num [numerator_H_r6_1_1_V4]) (by norm_num) (by norm_num)
  apply bernstein_positive_of_allEq (activityControlPolynomial numerator_H_r6_1_1_V4 ⟨0, 1⟩ ⟨1, 7⟩ 12 11 10) dh_special_H_r6_1_1_V4_10_coefficients ⟨1, 4⟩ Fraction.one 11 x hp
  · norm_num [Fraction.one, Fraction.ofInt]
  · norm_num [Fraction.one, Fraction.ofInt]
  · simp [activityControlPolynomial]
  · norm_num [fractionValue, Fraction.one, Fraction.ofInt]
  · simpa only [fractionValue, Int.cast_ofNat, Int.cast_one, Nat.cast_ofNat, Nat.cast_one] using hx.1
  · simpa only [fractionValue_one] using hx.2
  · exact reconstruct_302_H_r6_1_1_V4
  · intro c hc
    simp only [dh_special_H_r6_1_1_V4_10_coefficients, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cert_1015_H_r6_1_1_V4_positive_parent_control_10_0
    · exact cert_1016_H_r6_1_1_V4_positive_parent_control_10_1
    · exact cert_1017_H_r6_1_1_V4_positive_parent_control_10_2
    · exact cert_1018_H_r6_1_1_V4_positive_parent_control_10_3
    · exact cert_1019_H_r6_1_1_V4_positive_parent_control_10_4
    · exact cert_1020_H_r6_1_1_V4_positive_parent_control_10_5
    · exact cert_1021_H_r6_1_1_V4_positive_parent_control_10_6
    · exact cert_1022_H_r6_1_1_V4_positive_parent_control_10_7
    · exact cert_1023_H_r6_1_1_V4_positive_parent_control_10_8
    · exact cert_1024_H_r6_1_1_V4_positive_parent_control_10_9
    · exact cert_1025_H_r6_1_1_V4_positive_parent_control_10_10
    · exact cert_1026_H_r6_1_1_V4_positive_parent_control_10_11

def dh_special_H_r6_1_1_V4_11_coefficients : List Fraction :=
  [⟨63357445428567111694013895001711966873280259719600787974414499985887635118658135, 1977326743⟩, ⟨897208923733488886445266945599496639434801702003397239424812200363522313411809690, 21750594173⟩, ⟨1194405814310439697191709533804633808402057731344586348196051822313445260948110403, 21750594173⟩, ⟨1704470704812967344328330149599332259631626148091378371465061156887010740413676692, 21750594173⟩, ⟨2644850225174403736926587083130752912188430645959745251662277337665037103319045488, 21750594173⟩, ⟨4380156558839766092527086186206115310748864869290510727673635695365139365054717120, 21750594173⟩, ⟨679407242046022071432108963696075199767757678416981176462010905351223839720440960, 1977326743⟩, ⟨12738975929264778964296593421369626816305359391724552942519492200982056736004422144, 21750594173⟩, ⟨21289861825735367459506183579578816687840617374827132452587392002629550514536333312, 21750594173⟩, ⟨34574581445931652568056257231463777128962101427118574061730358953396021926157615104, 21750594173⟩, ⟨54391676746271556841162966892614802443650803023369742825272740772670576225331445760, 21750594173⟩, ⟨7533536020866066960989489496246973397624667865733598818416737563951366470814924800, 1977326743⟩]

theorem dh_special_H_r6_1_1_V4_11 (x : ℝ) (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < realHorner ((activityControlPolynomial numerator_H_r6_1_1_V4 ⟨0, 1⟩ ⟨1, 7⟩ 12 11 11).map fractionValue) x := by
  have hp : ∀ c ∈ (activityControlPolynomial numerator_H_r6_1_1_V4 ⟨0, 1⟩ ⟨1, 7⟩ 12 11 11), 0 < c.den :=
    activityControlPolynomial_den_pos numerator_H_r6_1_1_V4 ⟨0, 1⟩ ⟨1, 7⟩ 12 11 11
      (by norm_num [numerator_H_r6_1_1_V4]) (by norm_num) (by norm_num)
  apply bernstein_positive_of_allEq (activityControlPolynomial numerator_H_r6_1_1_V4 ⟨0, 1⟩ ⟨1, 7⟩ 12 11 11) dh_special_H_r6_1_1_V4_11_coefficients ⟨1, 4⟩ Fraction.one 11 x hp
  · norm_num [Fraction.one, Fraction.ofInt]
  · norm_num [Fraction.one, Fraction.ofInt]
  · simp [activityControlPolynomial]
  · norm_num [fractionValue, Fraction.one, Fraction.ofInt]
  · simpa only [fractionValue, Int.cast_ofNat, Int.cast_one, Nat.cast_ofNat, Nat.cast_one] using hx.1
  · simpa only [fractionValue_one] using hx.2
  · exact reconstruct_303_H_r6_1_1_V4
  · intro c hc
    simp only [dh_special_H_r6_1_1_V4_11_coefficients, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cert_1027_H_r6_1_1_V4_positive_parent_control_11_0
    · exact cert_1028_H_r6_1_1_V4_positive_parent_control_11_1
    · exact cert_1029_H_r6_1_1_V4_positive_parent_control_11_2
    · exact cert_1030_H_r6_1_1_V4_positive_parent_control_11_3
    · exact cert_1031_H_r6_1_1_V4_positive_parent_control_11_4
    · exact cert_1032_H_r6_1_1_V4_positive_parent_control_11_5
    · exact cert_1033_H_r6_1_1_V4_positive_parent_control_11_6
    · exact cert_1034_H_r6_1_1_V4_positive_parent_control_11_7
    · exact cert_1035_H_r6_1_1_V4_positive_parent_control_11_8
    · exact cert_1036_H_r6_1_1_V4_positive_parent_control_11_9
    · exact cert_1037_H_r6_1_1_V4_positive_parent_control_11_10
    · exact cert_1038_H_r6_1_1_V4_positive_parent_control_11_11

def dh_special_H_r6_1_1_V4_12_coefficients : List Fraction :=
  [⟨59392294695928485718673195090847098766189793568438716009243824603120242357073600, 1977326743⟩, ⟨844323723512401545242636346201421248517323888045119629577772088820693514682435200, 21750594173⟩, ⟨1122180371911532677385105632681456118208953378642411714451813190109352786617526720, 21750594173⟩, ⟨1588007649521025332620527929631983152575048645761885559713207458353808949636294400, 21750594173⟩, ⟨2433318727763245504043471820499557761663247584585311816378817033429045535325916160, 21750594173⟩, ⟨3982215547684021730876939559111784513078580670752517306168987763477043138100940800, 21750594173⟩, ⟨47177042265028708860474286333418680437081232268250571646952728339620294280878694400, 152254159211⟩, ⟨1040133493141152012455053396223942444668549153215999094682461900301918621802332160, 1977326743⟩, ⟨19102569553339333600435633123113965915382075809417309781525566491017252941054607360, 21750594173⟩, ⟨31054148888399035668186642428062537368887639755468345286706344039058094229783838720, 21750594173⟩, ⟨48963977726106703001943511247318196295075405904041388585400493498415791725556531200, 21750594173⟩, ⟨6802271401689670128482166714972189318949920722865699368254588849014505858714828800, 1977326743⟩]

theorem dh_special_H_r6_1_1_V4_12 (x : ℝ) (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < realHorner ((activityControlPolynomial numerator_H_r6_1_1_V4 ⟨0, 1⟩ ⟨1, 7⟩ 12 11 12).map fractionValue) x := by
  have hp : ∀ c ∈ (activityControlPolynomial numerator_H_r6_1_1_V4 ⟨0, 1⟩ ⟨1, 7⟩ 12 11 12), 0 < c.den :=
    activityControlPolynomial_den_pos numerator_H_r6_1_1_V4 ⟨0, 1⟩ ⟨1, 7⟩ 12 11 12
      (by norm_num [numerator_H_r6_1_1_V4]) (by norm_num) (by norm_num)
  apply bernstein_positive_of_allEq (activityControlPolynomial numerator_H_r6_1_1_V4 ⟨0, 1⟩ ⟨1, 7⟩ 12 11 12) dh_special_H_r6_1_1_V4_12_coefficients ⟨1, 4⟩ Fraction.one 11 x hp
  · norm_num [Fraction.one, Fraction.ofInt]
  · norm_num [Fraction.one, Fraction.ofInt]
  · simp [activityControlPolynomial]
  · norm_num [fractionValue, Fraction.one, Fraction.ofInt]
  · simpa only [fractionValue, Int.cast_ofNat, Int.cast_one, Nat.cast_ofNat, Nat.cast_one] using hx.1
  · simpa only [fractionValue_one] using hx.2
  · exact reconstruct_304_H_r6_1_1_V4
  · intro c hc
    simp only [dh_special_H_r6_1_1_V4_12_coefficients, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cert_1039_H_r6_1_1_V4_positive_parent_control_12_0
    · exact cert_1040_H_r6_1_1_V4_positive_parent_control_12_1
    · exact cert_1041_H_r6_1_1_V4_positive_parent_control_12_2
    · exact cert_1042_H_r6_1_1_V4_positive_parent_control_12_3
    · exact cert_1043_H_r6_1_1_V4_positive_parent_control_12_4
    · exact cert_1044_H_r6_1_1_V4_positive_parent_control_12_5
    · exact cert_1045_H_r6_1_1_V4_positive_parent_control_12_6
    · exact cert_1046_H_r6_1_1_V4_positive_parent_control_12_7
    · exact cert_1047_H_r6_1_1_V4_positive_parent_control_12_8
    · exact cert_1048_H_r6_1_1_V4_positive_parent_control_12_9
    · exact cert_1049_H_r6_1_1_V4_positive_parent_control_12_10
    · exact cert_1050_H_r6_1_1_V4_positive_parent_control_12_11

theorem dh_special_H_r6_1_1_V4_rectangle_positive (v x : ℝ)
    (hv : (0/1 : ℝ) ≤ v ∧ v ≤ (1/7 : ℝ)) (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < matrixValue numerator_H_r6_1_1_V4 v x := by
  apply activityControlPolynomial_rectangle_positive numerator_H_r6_1_1_V4 ⟨0, 1⟩ ⟨1, 7⟩ 12 11 v x
  · norm_num [numerator_H_r6_1_1_V4]
  · norm_num [Fraction.one, Fraction.ofInt]
  · norm_num [Fraction.one, Fraction.ofInt]
  · norm_num [numerator_H_r6_1_1_V4]
  · norm_num [numerator_H_r6_1_1_V4]
  · norm_num [fractionValue, Fraction.one, Fraction.ofInt]
  · simpa only [fractionValue, Int.cast_ofNat, Int.cast_one, Nat.cast_ofNat, Nat.cast_one, Int.cast_zero, zero_div] using hv.1
  · simpa only [fractionValue, Int.cast_ofNat, Int.cast_one, Nat.cast_ofNat, Nat.cast_one] using hv.2
  · intro j hj
    interval_cases j
    · exact dh_special_H_r6_1_1_V4_00 x hx
    · exact dh_special_H_r6_1_1_V4_01 x hx
    · exact dh_special_H_r6_1_1_V4_02 x hx
    · exact dh_special_H_r6_1_1_V4_03 x hx
    · exact dh_special_H_r6_1_1_V4_04 x hx
    · exact dh_special_H_r6_1_1_V4_05 x hx
    · exact dh_special_H_r6_1_1_V4_06 x hx
    · exact dh_special_H_r6_1_1_V4_07 x hx
    · exact dh_special_H_r6_1_1_V4_08 x hx
    · exact dh_special_H_r6_1_1_V4_09 x hx
    · exact dh_special_H_r6_1_1_V4_10 x hx
    · exact dh_special_H_r6_1_1_V4_11 x hx
    · exact dh_special_H_r6_1_1_V4_12 x hx

end F4Heavy.Analysis
