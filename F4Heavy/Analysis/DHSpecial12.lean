module

public import F4Heavy.Analysis.BernsteinSquareSemantics
public import F4Heavy.Finite.Reconstruction.Function12
public import Mathlib.Tactic.IntervalCases
public import F4Heavy.Finite.Certificates.Part005
public import F4Heavy.Finite.Certificates.Part006

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Heavy.Finite

def dh_special_D_r6_endpoint_R_00_coefficients : List Fraction :=
  [⟨475715275739165168977260869496165, 1048576⟩, ⟨110251269170317079700700168827867, 262144⟩, ⟨-142142073543287542592855184516531, 32768⟩, ⟨-9795473390064009089296579644717, 4096⟩, ⟨5321288328754731660318942862899, 256⟩, ⟨64777115570228779686663483897, 2⟩, ⟨13480698648273262711616898750, 1⟩]

def dh_special_D_r6_endpoint_R_00_quotient : List Fraction :=
  [⟨21346366265379139432191348324705, 32768⟩, ⟨61100304472899650847107667154923, 4096⟩, ⟨10114097260366490170423016972307, 256⟩, ⟨78257814218502042398280382647, 2⟩, ⟨13480698648273262711616898750, 1⟩]

theorem dh_special_D_r6_endpoint_R_00 (x : ℝ) (hx : (5/16 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < realHorner ((activityControlPolynomial numerator_D_r6_endpoint_R ⟨0, 1⟩ ⟨5, 21⟩ 7 6 0).map fractionValue) x := by
  have hp : ∀ c ∈ (activityControlPolynomial numerator_D_r6_endpoint_R ⟨0, 1⟩ ⟨5, 21⟩ 7 6 0), 0 < c.den :=
    activityControlPolynomial_den_pos numerator_D_r6_endpoint_R ⟨0, 1⟩ ⟨5, 21⟩ 7 6 0
      (by norm_num [numerator_D_r6_endpoint_R]) (by norm_num) (by norm_num)
  have hboth := cert_0208_D_r6_endpoint_R_square_discriminant_and_closed_endpoint_0
  rw [Bool.and_eq_true] at hboth
  apply weightedBernstein_positive_closed (activityControlPolynomial numerator_D_r6_endpoint_R ⟨0, 1⟩ ⟨5, 21⟩ 7 6 0) dh_special_D_r6_endpoint_R_00_coefficients ⟨5, 16⟩ Fraction.one 6 x hp
  · norm_num [Fraction.one, Fraction.ofInt]
  · norm_num [Fraction.one, Fraction.ofInt]
  · simp [activityControlPolynomial]
  · norm_num [fractionValue, Fraction.one, Fraction.ofInt]
  · simpa only [fractionValue, Int.cast_ofNat, Nat.cast_ofNat] using hx.1
  · simpa only [fractionValue_one] using hx.2
  · exact reconstruct_136_D_r6_endpoint_R
  · intro z hz
    apply squareReconstruction_positive dh_special_D_r6_endpoint_R_00_coefficients dh_special_D_r6_endpoint_R_00_quotient ⟨1, 4⟩ ⟨192129029774320962076956533176875, 524288⟩ ⟨-48764483659764965958965106493005, 262144⟩ z
    · norm_num [dh_special_D_r6_endpoint_R_00_quotient]
    · norm_num
    · norm_num
    · norm_num
    · simp [dh_special_D_r6_endpoint_R_00_quotient]
    · exact hz
    · intro c hc
      simp only [dh_special_D_r6_endpoint_R_00_quotient, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact cert_0203_D_r6_endpoint_R_square_quotient_coefficient_0_0
      · exact cert_0204_D_r6_endpoint_R_square_quotient_coefficient_0_1
      · exact cert_0205_D_r6_endpoint_R_square_quotient_coefficient_0_2
      · exact cert_0206_D_r6_endpoint_R_square_quotient_coefficient_0_3
      · exact cert_0207_D_r6_endpoint_R_square_quotient_coefficient_0_4
    · exact hboth.1
    · exact reconstruct_136_D_r6_endpoint_R_square_identity
  · exact fraction_positive_sound _ hboth.2

def dh_special_D_r6_endpoint_R_01_coefficients : List Fraction :=
  [⟨2480956704607556443386510946215, 4096⟩, ⟨3803788899119425448934000803874493, 12845056⟩, ⟨4401623013202485197718663083369, 1003520⟩, ⟨406274204695361085544507934107221, 2007040⟩, ⟨51956319540483653949218301457121, 31360⟩, ⟨1076631910413139447472809690601, 196⟩, ⟨648084812577402167649823211100, 49⟩]

theorem dh_special_D_r6_endpoint_R_01 (x : ℝ) (hx : (5/16 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < realHorner ((activityControlPolynomial numerator_D_r6_endpoint_R ⟨0, 1⟩ ⟨5, 21⟩ 7 6 1).map fractionValue) x := by
  have hp : ∀ c ∈ (activityControlPolynomial numerator_D_r6_endpoint_R ⟨0, 1⟩ ⟨5, 21⟩ 7 6 1), 0 < c.den :=
    activityControlPolynomial_den_pos numerator_D_r6_endpoint_R ⟨0, 1⟩ ⟨5, 21⟩ 7 6 1
      (by norm_num [numerator_D_r6_endpoint_R]) (by norm_num) (by norm_num)
  apply bernstein_positive_of_allEq (activityControlPolynomial numerator_D_r6_endpoint_R ⟨0, 1⟩ ⟨5, 21⟩ 7 6 1) dh_special_D_r6_endpoint_R_01_coefficients ⟨5, 16⟩ Fraction.one 6 x hp
  · norm_num [Fraction.one, Fraction.ofInt]
  · norm_num [Fraction.one, Fraction.ofInt]
  · simp [activityControlPolynomial]
  · norm_num [fractionValue, Fraction.one, Fraction.ofInt]
  · simpa only [fractionValue, Int.cast_ofNat, Nat.cast_ofNat] using hx.1
  · simpa only [fractionValue_one] using hx.2
  · exact reconstruct_137_D_r6_endpoint_R
  · intro c hc
    simp only [dh_special_D_r6_endpoint_R_01_coefficients, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cert_0209_D_r6_endpoint_R_positive_parent_control_1_0
    · exact cert_0210_D_r6_endpoint_R_positive_parent_control_1_1
    · exact cert_0211_D_r6_endpoint_R_positive_parent_control_1_2
    · exact cert_0212_D_r6_endpoint_R_positive_parent_control_1_3
    · exact cert_0213_D_r6_endpoint_R_positive_parent_control_1_4
    · exact cert_0214_D_r6_endpoint_R_positive_parent_control_1_5
    · exact cert_0215_D_r6_endpoint_R_positive_parent_control_1_6

def dh_special_D_r6_endpoint_R_02_coefficients : List Fraction :=
  [⟨910165140988012056984480564532704805, 1213857792⟩, ⟨267773917636228287574170487722081479, 520224768⟩, ⟨334845724252464560451259361950073921, 1137991680⟩, ⟨511820074941227967502024259484107, 967680⟩, ⟨8647531944001191336373740262416383, 4445280⟩, ⟨312428347057406584988386457152871, 55566⟩, ⟨120637030318937291676052444746800, 9261⟩]

theorem dh_special_D_r6_endpoint_R_02 (x : ℝ) (hx : (5/16 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < realHorner ((activityControlPolynomial numerator_D_r6_endpoint_R ⟨0, 1⟩ ⟨5, 21⟩ 7 6 2).map fractionValue) x := by
  have hp : ∀ c ∈ (activityControlPolynomial numerator_D_r6_endpoint_R ⟨0, 1⟩ ⟨5, 21⟩ 7 6 2), 0 < c.den :=
    activityControlPolynomial_den_pos numerator_D_r6_endpoint_R ⟨0, 1⟩ ⟨5, 21⟩ 7 6 2
      (by norm_num [numerator_D_r6_endpoint_R]) (by norm_num) (by norm_num)
  apply bernstein_positive_of_allEq (activityControlPolynomial numerator_D_r6_endpoint_R ⟨0, 1⟩ ⟨5, 21⟩ 7 6 2) dh_special_D_r6_endpoint_R_02_coefficients ⟨5, 16⟩ Fraction.one 6 x hp
  · norm_num [Fraction.one, Fraction.ofInt]
  · norm_num [Fraction.one, Fraction.ofInt]
  · simp [activityControlPolynomial]
  · norm_num [fractionValue, Fraction.one, Fraction.ofInt]
  · simpa only [fractionValue, Int.cast_ofNat, Nat.cast_ofNat] using hx.1
  · simpa only [fractionValue_one] using hx.2
  · exact reconstruct_138_D_r6_endpoint_R
  · intro c hc
    simp only [dh_special_D_r6_endpoint_R_02_coefficients, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cert_0216_D_r6_endpoint_R_positive_parent_control_2_0
    · exact cert_0217_D_r6_endpoint_R_positive_parent_control_2_1
    · exact cert_0218_D_r6_endpoint_R_positive_parent_control_2_2
    · exact cert_0219_D_r6_endpoint_R_positive_parent_control_2_3
    · exact cert_0220_D_r6_endpoint_R_positive_parent_control_2_4
    · exact cert_0221_D_r6_endpoint_R_positive_parent_control_2_5
    · exact cert_0222_D_r6_endpoint_R_positive_parent_control_2_6

def dh_special_D_r6_endpoint_R_03_coefficients : List Fraction :=
  [⟨1629980615796872659884271553934845, 1843968⟩, ⟨341069907855732163724661938974745449, 472055808⟩, ⟨127317850251751663277500379455214777, 221276160⟩, ⟨47199875022504408947179840937056771, 55319040⟩, ⟨831089744456992013484134119938709, 370440⟩, ⟨374627667366156891877401282069212, 64827⟩, ⟨39743757446838240221684506686400, 3087⟩]

theorem dh_special_D_r6_endpoint_R_03 (x : ℝ) (hx : (5/16 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < realHorner ((activityControlPolynomial numerator_D_r6_endpoint_R ⟨0, 1⟩ ⟨5, 21⟩ 7 6 3).map fractionValue) x := by
  have hp : ∀ c ∈ (activityControlPolynomial numerator_D_r6_endpoint_R ⟨0, 1⟩ ⟨5, 21⟩ 7 6 3), 0 < c.den :=
    activityControlPolynomial_den_pos numerator_D_r6_endpoint_R ⟨0, 1⟩ ⟨5, 21⟩ 7 6 3
      (by norm_num [numerator_D_r6_endpoint_R]) (by norm_num) (by norm_num)
  apply bernstein_positive_of_allEq (activityControlPolynomial numerator_D_r6_endpoint_R ⟨0, 1⟩ ⟨5, 21⟩ 7 6 3) dh_special_D_r6_endpoint_R_03_coefficients ⟨5, 16⟩ Fraction.one 6 x hp
  · norm_num [Fraction.one, Fraction.ofInt]
  · norm_num [Fraction.one, Fraction.ofInt]
  · simp [activityControlPolynomial]
  · norm_num [fractionValue, Fraction.one, Fraction.ofInt]
  · simpa only [fractionValue, Int.cast_ofNat, Nat.cast_ofNat] using hx.1
  · simpa only [fractionValue_one] using hx.2
  · exact reconstruct_139_D_r6_endpoint_R
  · intro c hc
    simp only [dh_special_D_r6_endpoint_R_03_coefficients, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cert_0223_D_r6_endpoint_R_positive_parent_control_3_0
    · exact cert_0224_D_r6_endpoint_R_positive_parent_control_3_1
    · exact cert_0225_D_r6_endpoint_R_positive_parent_control_3_2
    · exact cert_0226_D_r6_endpoint_R_positive_parent_control_3_3
    · exact cert_0227_D_r6_endpoint_R_positive_parent_control_3_4
    · exact cert_0228_D_r6_endpoint_R_positive_parent_control_3_5
    · exact cert_0229_D_r6_endpoint_R_positive_parent_control_3_6

def dh_special_D_r6_endpoint_R_04_coefficients : List Fraction :=
  [⟨29922572025140831647571077085026974535, 29739515904⟩, ⟨2189364110618443339221175315461642859, 2389782528⟩, ⟨2202218281620636695424437988171157883, 2613824640⟩, ⟨63594462125996595599360822243828557, 54454680⟩, ⟨51898500853856300315066028244058743, 20420505⟩, ⟨24299865917619849374644641029979856, 4084101⟩, ⟨17368054889648155576315787875187200, 1361367⟩]

theorem dh_special_D_r6_endpoint_R_04 (x : ℝ) (hx : (5/16 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < realHorner ((activityControlPolynomial numerator_D_r6_endpoint_R ⟨0, 1⟩ ⟨5, 21⟩ 7 6 4).map fractionValue) x := by
  have hp : ∀ c ∈ (activityControlPolynomial numerator_D_r6_endpoint_R ⟨0, 1⟩ ⟨5, 21⟩ 7 6 4), 0 < c.den :=
    activityControlPolynomial_den_pos numerator_D_r6_endpoint_R ⟨0, 1⟩ ⟨5, 21⟩ 7 6 4
      (by norm_num [numerator_D_r6_endpoint_R]) (by norm_num) (by norm_num)
  apply bernstein_positive_of_allEq (activityControlPolynomial numerator_D_r6_endpoint_R ⟨0, 1⟩ ⟨5, 21⟩ 7 6 4) dh_special_D_r6_endpoint_R_04_coefficients ⟨5, 16⟩ Fraction.one 6 x hp
  · norm_num [Fraction.one, Fraction.ofInt]
  · norm_num [Fraction.one, Fraction.ofInt]
  · simp [activityControlPolynomial]
  · norm_num [fractionValue, Fraction.one, Fraction.ofInt]
  · simpa only [fractionValue, Int.cast_ofNat, Nat.cast_ofNat] using hx.1
  · simpa only [fractionValue_one] using hx.2
  · exact reconstruct_140_D_r6_endpoint_R
  · intro c hc
    simp only [dh_special_D_r6_endpoint_R_04_coefficients, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cert_0230_D_r6_endpoint_R_positive_parent_control_4_0
    · exact cert_0231_D_r6_endpoint_R_positive_parent_control_4_1
    · exact cert_0232_D_r6_endpoint_R_positive_parent_control_4_2
    · exact cert_0233_D_r6_endpoint_R_positive_parent_control_4_3
    · exact cert_0234_D_r6_endpoint_R_positive_parent_control_4_4
    · exact cert_0235_D_r6_endpoint_R_positive_parent_control_4_5
    · exact cert_0236_D_r6_endpoint_R_positive_parent_control_4_6

def dh_special_D_r6_endpoint_R_05_coefficients : List Fraction :=
  [⟨391537279330039505468079276296576516515, 351298031616⟩, ⟨287772984438907673416803137912890237961, 263473523712⟩, ⟨44881207645484960596986817658600040151, 41167738080⟩, ⟨5024032834068067113374911261091692091, 3430644840⟩, ⟨3637634743123914047179928325025886984, 1286491815⟩, ⟨1574703041642025548372232919449801728, 257298363⟩, ⟨155071512319858430841525038895616000, 12252303⟩]

theorem dh_special_D_r6_endpoint_R_05 (x : ℝ) (hx : (5/16 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < realHorner ((activityControlPolynomial numerator_D_r6_endpoint_R ⟨0, 1⟩ ⟨5, 21⟩ 7 6 5).map fractionValue) x := by
  have hp : ∀ c ∈ (activityControlPolynomial numerator_D_r6_endpoint_R ⟨0, 1⟩ ⟨5, 21⟩ 7 6 5), 0 < c.den :=
    activityControlPolynomial_den_pos numerator_D_r6_endpoint_R ⟨0, 1⟩ ⟨5, 21⟩ 7 6 5
      (by norm_num [numerator_D_r6_endpoint_R]) (by norm_num) (by norm_num)
  apply bernstein_positive_of_allEq (activityControlPolynomial numerator_D_r6_endpoint_R ⟨0, 1⟩ ⟨5, 21⟩ 7 6 5) dh_special_D_r6_endpoint_R_05_coefficients ⟨5, 16⟩ Fraction.one 6 x hp
  · norm_num [Fraction.one, Fraction.ofInt]
  · norm_num [Fraction.one, Fraction.ofInt]
  · simp [activityControlPolynomial]
  · norm_num [fractionValue, Fraction.one, Fraction.ofInt]
  · simpa only [fractionValue, Int.cast_ofNat, Nat.cast_ofNat] using hx.1
  · simpa only [fractionValue_one] using hx.2
  · exact reconstruct_141_D_r6_endpoint_R
  · intro c hc
    simp only [dh_special_D_r6_endpoint_R_05_coefficients, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cert_0237_D_r6_endpoint_R_positive_parent_control_5_0
    · exact cert_0238_D_r6_endpoint_R_positive_parent_control_5_1
    · exact cert_0239_D_r6_endpoint_R_positive_parent_control_5_2
    · exact cert_0240_D_r6_endpoint_R_positive_parent_control_5_3
    · exact cert_0241_D_r6_endpoint_R_positive_parent_control_5_4
    · exact cert_0242_D_r6_endpoint_R_positive_parent_control_5_5
    · exact cert_0243_D_r6_endpoint_R_positive_parent_control_5_6

def dh_special_D_r6_endpoint_R_06_coefficients : List Fraction :=
  [⟨61853660754278899489438088983495855385, 51230962944⟩, ⟨7988878159186683667098982047132226579, 6403870368⟩, ⟨3940725592150032843970313583208135567, 3001814235⟩, ⟨247883671291790322495702321878756284, 142943535⟩, ⟨3090286616894046827484280539471788032, 1000604745⟩, ⟨3764777626599205253602253962959122432, 600362847⟩, ⟨2510476548509764124785545456228761600, 200120949⟩]

theorem dh_special_D_r6_endpoint_R_06 (x : ℝ) (hx : (5/16 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < realHorner ((activityControlPolynomial numerator_D_r6_endpoint_R ⟨0, 1⟩ ⟨5, 21⟩ 7 6 6).map fractionValue) x := by
  have hp : ∀ c ∈ (activityControlPolynomial numerator_D_r6_endpoint_R ⟨0, 1⟩ ⟨5, 21⟩ 7 6 6), 0 < c.den :=
    activityControlPolynomial_den_pos numerator_D_r6_endpoint_R ⟨0, 1⟩ ⟨5, 21⟩ 7 6 6
      (by norm_num [numerator_D_r6_endpoint_R]) (by norm_num) (by norm_num)
  apply bernstein_positive_of_allEq (activityControlPolynomial numerator_D_r6_endpoint_R ⟨0, 1⟩ ⟨5, 21⟩ 7 6 6) dh_special_D_r6_endpoint_R_06_coefficients ⟨5, 16⟩ Fraction.one 6 x hp
  · norm_num [Fraction.one, Fraction.ofInt]
  · norm_num [Fraction.one, Fraction.ofInt]
  · simp [activityControlPolynomial]
  · norm_num [fractionValue, Fraction.one, Fraction.ofInt]
  · simpa only [fractionValue, Int.cast_ofNat, Nat.cast_ofNat] using hx.1
  · simpa only [fractionValue_one] using hx.2
  · exact reconstruct_142_D_r6_endpoint_R
  · intro c hc
    simp only [dh_special_D_r6_endpoint_R_06_coefficients, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cert_0244_D_r6_endpoint_R_positive_parent_control_6_0
    · exact cert_0245_D_r6_endpoint_R_positive_parent_control_6_1
    · exact cert_0246_D_r6_endpoint_R_positive_parent_control_6_2
    · exact cert_0247_D_r6_endpoint_R_positive_parent_control_6_3
    · exact cert_0248_D_r6_endpoint_R_positive_parent_control_6_4
    · exact cert_0249_D_r6_endpoint_R_positive_parent_control_6_5
    · exact cert_0250_D_r6_endpoint_R_positive_parent_control_6_6

def dh_special_D_r6_endpoint_R_07_coefficients : List Fraction :=
  [⟨456422608710170381064582281828753665, 355770576⟩, ⟨29799544790187421892122921397136189301, 21613062492⟩, ⟨40647621075220864937501870279210893528, 27016328115⟩, ⟨17717586763168607869214307477200813792, 9005442705⟩, ⟨89405947159733552055572046182130878464, 27016328115⟩, ⟨34472959200887155392610715825193484288, 5403265623⟩, ⟨22317145026175527040488643603647692800, 1801088541⟩]

theorem dh_special_D_r6_endpoint_R_07 (x : ℝ) (hx : (5/16 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < realHorner ((activityControlPolynomial numerator_D_r6_endpoint_R ⟨0, 1⟩ ⟨5, 21⟩ 7 6 7).map fractionValue) x := by
  have hp : ∀ c ∈ (activityControlPolynomial numerator_D_r6_endpoint_R ⟨0, 1⟩ ⟨5, 21⟩ 7 6 7), 0 < c.den :=
    activityControlPolynomial_den_pos numerator_D_r6_endpoint_R ⟨0, 1⟩ ⟨5, 21⟩ 7 6 7
      (by norm_num [numerator_D_r6_endpoint_R]) (by norm_num) (by norm_num)
  apply bernstein_positive_of_allEq (activityControlPolynomial numerator_D_r6_endpoint_R ⟨0, 1⟩ ⟨5, 21⟩ 7 6 7) dh_special_D_r6_endpoint_R_07_coefficients ⟨5, 16⟩ Fraction.one 6 x hp
  · norm_num [Fraction.one, Fraction.ofInt]
  · norm_num [Fraction.one, Fraction.ofInt]
  · simp [activityControlPolynomial]
  · norm_num [fractionValue, Fraction.one, Fraction.ofInt]
  · simpa only [fractionValue, Int.cast_ofNat, Nat.cast_ofNat] using hx.1
  · simpa only [fractionValue_one] using hx.2
  · exact reconstruct_143_D_r6_endpoint_R
  · intro c hc
    simp only [dh_special_D_r6_endpoint_R_07_coefficients, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cert_0251_D_r6_endpoint_R_positive_parent_control_7_0
    · exact cert_0252_D_r6_endpoint_R_positive_parent_control_7_1
    · exact cert_0253_D_r6_endpoint_R_positive_parent_control_7_2
    · exact cert_0254_D_r6_endpoint_R_positive_parent_control_7_3
    · exact cert_0255_D_r6_endpoint_R_positive_parent_control_7_4
    · exact cert_0256_D_r6_endpoint_R_positive_parent_control_7_5
    · exact cert_0257_D_r6_endpoint_R_positive_parent_control_7_6

theorem dh_special_D_r6_endpoint_R_rectangle_positive (v x : ℝ)
    (hv : (0/1 : ℝ) ≤ v ∧ v ≤ (5/21 : ℝ)) (hx : (5/16 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < matrixValue numerator_D_r6_endpoint_R v x := by
  apply activityControlPolynomial_rectangle_positive numerator_D_r6_endpoint_R ⟨0, 1⟩ ⟨5, 21⟩ 7 6 v x
  · norm_num [numerator_D_r6_endpoint_R]
  · norm_num [Fraction.one, Fraction.ofInt]
  · norm_num [Fraction.one, Fraction.ofInt]
  · norm_num [numerator_D_r6_endpoint_R]
  · norm_num [numerator_D_r6_endpoint_R]
  · norm_num [fractionValue, Fraction.one, Fraction.ofInt]
  · simpa only [fractionValue, Int.cast_ofNat, Nat.cast_ofNat, Int.cast_zero, zero_div] using hv.1
  · simpa only [fractionValue, Int.cast_ofNat, Nat.cast_ofNat] using hv.2
  · intro j hj
    interval_cases j
    · exact dh_special_D_r6_endpoint_R_00 x hx
    · exact dh_special_D_r6_endpoint_R_01 x hx
    · exact dh_special_D_r6_endpoint_R_02 x hx
    · exact dh_special_D_r6_endpoint_R_03 x hx
    · exact dh_special_D_r6_endpoint_R_04 x hx
    · exact dh_special_D_r6_endpoint_R_05 x hx
    · exact dh_special_D_r6_endpoint_R_06 x hx
    · exact dh_special_D_r6_endpoint_R_07 x hx

end F4Heavy.Analysis
