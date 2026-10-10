module

public import F4Heavy.Analysis.ECommonClosed
public import F4Heavy.Analysis.EParametricAssembly
public import F4Heavy.Analysis.PolynomialSemantics
public import F4Heavy.Finite.Factorizations.Check0273
public import F4Heavy.Finite.Factorizations.Check0283
public import F4Heavy.Finite.Factorizations.Check0292
public import F4Heavy.Finite.Factorizations.Check0303
public import F4Heavy.Finite.Factorizations.Check0401
public import F4Heavy.Finite.Factorizations.Check0413
public import F4Heavy.Finite.Factorizations.Check0422
public import F4Heavy.Finite.Factorizations.Check0432
public import F4Heavy.Finite.Factorizations.Check0441
public import F4Heavy.Finite.Factorizations.Check0452
public import F4Heavy.Finite.Factorizations.Check0463
public import F4Heavy.Finite.Factorizations.Check0475

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Heavy.Finite

def e_record_E1_r8_H0_denominator : Polynomial :=
  [⟨0, 0, ⟨285941742698496000000000000, 1⟩⟩, ⟨0, 1, ⟨3717242655080448000000000000, 1⟩⟩, ⟨0, 2, ⟨6004776596668416000000000000, 1⟩⟩, ⟨0, 3, ⟨2573475684286464000000000000, 1⟩⟩, ⟨1, 0, ⟨1143766970793984000000000000, 1⟩⟩, ⟨1, 1, ⟨15726795848417280000000000000, 1⟩⟩, ⟨1, 2, ⟨35170834351915008000000000000, 1⟩⟩, ⟨1, 3, ⟨28308232527151104000000000000, 1⟩⟩, ⟨1, 4, ⟨7720427052859392000000000000, 1⟩⟩, ⟨2, 0, ⟨1715650456190976000000000000, 1⟩⟩, ⟨2, 1, ⟨24876931614769152000000000000, 1⟩⟩, ⟨2, 2, ⟨70341668703830016000000000000, 1⟩⟩, ⟨2, 3, ⟨80635571440975872000000000000, 1⟩⟩, ⟨2, 4, ⟨41175610948583424000000000000, 1⟩⟩, ⟨2, 5, ⟨7720427052859392000000000000, 1⟩⟩, ⟨3, 0, ⟨1143766970793984000000000000, 1⟩⟩, ⟨3, 1, ⟨17442446304608256000000000000, 1⟩⟩, ⟨3, 2, ⟨59189940738588672000000000000, 1⟩⟩, ⟨3, 3, ⟨86926289780342784000000000000, 1⟩⟩, ⟨3, 4, ⟨62907183393669120000000000000, 1⟩⟩, ⟨3, 5, ⟨21445630702387200000000000000, 1⟩⟩, ⟨3, 6, ⟨2573475684286464000000000000, 1⟩⟩, ⟨4, 0, ⟨285941742698496000000000000, 1⟩⟩, ⟨4, 1, ⟨4575067883175936000000000000, 1⟩⟩, ⟨4, 2, ⟨18014329790005248000000000000, 1⟩⟩, ⟨4, 3, ⟨32025475182231552000000000000, 1⟩⟩, ⟨4, 4, ⟨29451999497945088000000000000, 1⟩⟩, ⟨4, 5, ⟨13725203649527808000000000000, 1⟩⟩, ⟨4, 6, ⟨2573475684286464000000000000, 1⟩⟩]

def e_record_E1_r8_H0_factors : List (Polynomial × Nat) :=
  [([⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩], 1), ([⟨0, 0, ⟨1, 1⟩⟩, ⟨0, 1, ⟨1, 1⟩⟩], 1), ([⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩, ⟨1, 1, ⟨1, 1⟩⟩], 3), ([⟨0, 0, ⟨1, 9⟩⟩, ⟨0, 1, ⟨4, 3⟩⟩, ⟨0, 2, ⟨1, 1⟩⟩], 1)]

noncomputable def e_record_E1_r8_H0 (lam x : ℝ) : ℝ :=
  matrixValue numerator_E1_r8_H0 lam x / polynomialValue e_record_E1_r8_H0_denominator lam x

theorem e_record_E1_r8_H0_denominator_value (lam x : ℝ) :
    polynomialValue e_record_E1_r8_H0_denominator lam x = (2573475684286464000000000000 : ℝ)*(lam+1)^1*(x+1)^1*(lam*x+lam+1)^3*(x^2+4*x/3+1/9)^1 := by
  rw [factorCheck_sound e_record_E1_r8_H0_denominator ⟨2573475684286464000000000000, 1⟩ e_record_E1_r8_H0_factors lam x (by norm_num)
    (by norm_num [e_record_E1_r8_H0_factors, validPolynomial]) cert_0273_E1_r8_H0_allowed_denominator_factors]
  have hf0 : polynomialValue [⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩] lam x = (lam+1) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  have hf1 : polynomialValue [⟨0, 0, ⟨1, 1⟩⟩, ⟨0, 1, ⟨1, 1⟩⟩] lam x = (x+1) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  have hf2 : polynomialValue [⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩, ⟨1, 1, ⟨1, 1⟩⟩] lam x = (lam*x+lam+1) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  have hf3 : polynomialValue [⟨0, 0, ⟨1, 9⟩⟩, ⟨0, 1, ⟨4, 3⟩⟩, ⟨0, 2, ⟨1, 1⟩⟩] lam x = (x^2+4*x/3+1/9) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  simp only [e_record_E1_r8_H0_factors, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    hf0, hf1, hf2, hf3, mul_one]
  norm_num only [fractionValue, Int.cast_ofNat, Nat.cast_one, div_one]
  ac_rfl


theorem e_record_E1_r8_H0_denominator_positive (lam x : ℝ) (hlam : 0 ≤ lam) (hx : 0 ≤ x) :
    0 < polynomialValue e_record_E1_r8_H0_denominator lam x := by
  rw [e_record_E1_r8_H0_denominator_value]
  positivity

theorem e_record_E1_r8_H0_positive (lam x : ℝ)
    (hlam : (13/10 : ℝ) ≤ lam ∧ lam ≤ 29/20)
    (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) : 0 < e_record_E1_r8_H0 lam x := by
  apply div_pos ((e_common_E1_r8_H0_numerator_rectangle_positive lam x hlam hx))
    (e_record_E1_r8_H0_denominator_positive lam x (by linarith only [hlam.1]) (by linarith only [hx.1]))

def e_record_E1_r8_U0_denominator : Polynomial :=
  [⟨0, 0, ⟨57672845273955841210947993600000000000000000000000000000000000, 1⟩⟩, ⟨0, 1, ⟨749746988561425935742323916800000000000000000000000000000000000, 1⟩⟩, ⟨0, 2, ⟨1211129750753072665429907865600000000000000000000000000000000000, 1⟩⟩, ⟨0, 3, ⟨519055607465602570898531942400000000000000000000000000000000000, 1⟩⟩, ⟨1, 0, ⟨173018535821867523632843980800000000000000000000000000000000000, 1⟩⟩, ⟨1, 1, ⟨2364586656232189489648867737600000000000000000000000000000000000, 1⟩⟩, ⟨1, 2, ⟨5132883229382069867774371430400000000000000000000000000000000000, 1⟩⟩, ⟨1, 3, ⟨3979426323902953043555411558400000000000000000000000000000000000, 1⟩⟩, ⟨1, 4, ⟨1038111214931205141797063884800000000000000000000000000000000000, 1⟩⟩, ⟨2, 0, ⟨173018535821867523632843980800000000000000000000000000000000000, 1⟩⟩, ⟨2, 1, ⟨2479932346780101172070763724800000000000000000000000000000000000, 1⟩⟩, ⟨2, 2, ⟨6690050051778877580469967257600000000000000000000000000000000000, 1⟩⟩, ⟨2, 3, ⟨7151432813970524310157551206400000000000000000000000000000000000, 1⟩⟩, ⟨2, 4, ⟨3287352180615482949024035635200000000000000000000000000000000000, 1⟩⟩, ⟨2, 5, ⟨519055607465602570898531942400000000000000000000000000000000000, 1⟩⟩, ⟨3, 0, ⟨57672845273955841210947993600000000000000000000000000000000000, 1⟩⟩, ⟨3, 1, ⟨865092679109337618164219904000000000000000000000000000000000000, 1⟩⟩, ⟨3, 2, ⟨2768296573149880378125503692800000000000000000000000000000000000, 1⟩⟩, ⟨3, 3, ⟨3691062097533173837500671590400000000000000000000000000000000000, 1⟩⟩, ⟨3, 4, ⟨2249240965684277807226971750400000000000000000000000000000000000, 1⟩⟩, ⟨3, 5, ⟨519055607465602570898531942400000000000000000000000000000000000, 1⟩⟩]

def e_record_E1_r8_U0_factors : List (Polynomial × Nat) :=
  [([⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩], 1), ([⟨0, 0, ⟨1, 1⟩⟩, ⟨0, 1, ⟨1, 1⟩⟩], 1), ([⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩, ⟨1, 1, ⟨1, 1⟩⟩], 2), ([⟨0, 0, ⟨1, 9⟩⟩, ⟨0, 1, ⟨4, 3⟩⟩, ⟨0, 2, ⟨1, 1⟩⟩], 1)]

noncomputable def e_record_E1_r8_U0 (lam x : ℝ) : ℝ :=
  matrixValue numerator_E1_r8_U0 lam x / polynomialValue e_record_E1_r8_U0_denominator lam x

theorem e_record_E1_r8_U0_denominator_value (lam x : ℝ) :
    polynomialValue e_record_E1_r8_U0_denominator lam x = (519055607465602570898531942400000000000000000000000000000000000 : ℝ)*(lam+1)^1*(x+1)^1*(lam*x+lam+1)^2*(x^2+4*x/3+1/9)^1 := by
  rw [factorCheck_sound e_record_E1_r8_U0_denominator ⟨519055607465602570898531942400000000000000000000000000000000000, 1⟩ e_record_E1_r8_U0_factors lam x (by norm_num)
    (by norm_num [e_record_E1_r8_U0_factors, validPolynomial]) cert_0283_E1_r8_U0_allowed_denominator_factors]
  have hf0 : polynomialValue [⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩] lam x = (lam+1) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  have hf1 : polynomialValue [⟨0, 0, ⟨1, 1⟩⟩, ⟨0, 1, ⟨1, 1⟩⟩] lam x = (x+1) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  have hf2 : polynomialValue [⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩, ⟨1, 1, ⟨1, 1⟩⟩] lam x = (lam*x+lam+1) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  have hf3 : polynomialValue [⟨0, 0, ⟨1, 9⟩⟩, ⟨0, 1, ⟨4, 3⟩⟩, ⟨0, 2, ⟨1, 1⟩⟩] lam x = (x^2+4*x/3+1/9) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  simp only [e_record_E1_r8_U0_factors, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    hf0, hf1, hf2, hf3, mul_one]
  norm_num only [fractionValue, Int.cast_ofNat, Nat.cast_one, div_one]
  ac_rfl


theorem e_record_E1_r8_U0_denominator_positive (lam x : ℝ) (hlam : 0 ≤ lam) (hx : 0 ≤ x) :
    0 < polynomialValue e_record_E1_r8_U0_denominator lam x := by
  rw [e_record_E1_r8_U0_denominator_value]
  positivity

theorem e_record_E1_r8_U0_positive (lam x : ℝ)
    (hlam : (13/10 : ℝ) ≤ lam ∧ lam ≤ 29/20)
    (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) : 0 < e_record_E1_r8_U0 lam x := by
  apply div_pos ((e_common_E1_r8_U0_numerator_rectangle_positive lam x hlam hx))
    (e_record_E1_r8_U0_denominator_positive lam x (by linarith only [hlam.1]) (by linarith only [hx.1]))

def e_record_E1_r8_U1_denominator : Polynomial :=
  [⟨0, 0, ⟨25904030620142989989642240000000000000000000000000000000000, 1⟩⟩, ⟨0, 1, ⟨336752398061858869865349120000000000000000000000000000000000, 1⟩⟩, ⟨0, 2, ⟨543984643023002789782487040000000000000000000000000000000000, 1⟩⟩, ⟨0, 3, ⟨233136275581286909906780160000000000000000000000000000000000, 1⟩⟩, ⟨1, 0, ⟨129520153100714949948211200000000000000000000000000000000000, 1⟩⟩, ⟨1, 1, ⟨1787378112789866309285314560000000000000000000000000000000000, 1⟩⟩, ⟨1, 2, ⟨4066932807362449428373831680000000000000000000000000000000000, 1⟩⟩, ⟨1, 3, ⟨3341619949998445708663848960000000000000000000000000000000000, 1⟩⟩, ⟨1, 4, ⟨932545102325147639627120640000000000000000000000000000000000, 1⟩⟩, ⟨2, 0, ⟨259040306201429899896422400000000000000000000000000000000000, 1⟩⟩, ⟨2, 1, ⟨3781988470540876538487767040000000000000000000000000000000000, 1⟩⟩, ⟨2, 2, ⟨10983308982940627755608309760000000000000000000000000000000000, 1⟩⟩, ⟨2, 3, ⟨13055631432552066954779688960000000000000000000000000000000000, 1⟩⟩, ⟨2, 4, ⟨6994088267438607297203404800000000000000000000000000000000000, 1⟩⟩, ⟨2, 5, ⟨1398817653487721459440680960000000000000000000000000000000000, 1⟩⟩, ⟨3, 0, ⟨259040306201429899896422400000000000000000000000000000000000, 1⟩⟩, ⟨3, 1, ⟨3989220715502020458404904960000000000000000000000000000000000, 1⟩⟩, ⟨3, 2, ⟨13988176534877214594406809600000000000000000000000000000000000, 1⟩⟩, ⟨3, 3, ⟨21552153475958967671382343680000000000000000000000000000000000, 1⟩⟩, ⟨3, 4, ⟨16734003780612371533308887040000000000000000000000000000000000, 1⟩⟩, ⟨3, 5, ⟨6372391532555175537451991040000000000000000000000000000000000, 1⟩⟩, ⟨3, 6, ⟨932545102325147639627120640000000000000000000000000000000000, 1⟩⟩, ⟨4, 0, ⟨129520153100714949948211200000000000000000000000000000000000, 1⟩⟩, ⟨4, 1, ⟨2098226480231582189161021440000000000000000000000000000000000, 1⟩⟩, ⟨4, 2, ⟨8574234135267329686571581440000000000000000000000000000000000, 1⟩⟩, ⟨4, 3, ⟨16138211076349082763547115520000000000000000000000000000000000, 1⟩⟩, ⟨4, 4, ⟨16241827198829654723505684480000000000000000000000000000000000, 1⟩⟩, ⟨4, 5, ⟨8885082502709045566447288320000000000000000000000000000000000, 1⟩⟩, ⟨4, 6, ⟨2409074847673298069036728320000000000000000000000000000000000, 1⟩⟩, ⟨4, 7, ⟨233136275581286909906780160000000000000000000000000000000000, 1⟩⟩, ⟨5, 0, ⟨25904030620142989989642240000000000000000000000000000000000, 1⟩⟩, ⟨5, 1, ⟨440368520542430829823918080000000000000000000000000000000000, 1⟩⟩, ⟨5, 2, ⟨2046418418991296209181736960000000000000000000000000000000000, 1⟩⟩, ⟨5, 3, ⟨4533205358525023248187392000000000000000000000000000000000000, 1⟩⟩, ⟨5, 4, ⟨5569366583330742847773081600000000000000000000000000000000000, 1⟩⟩, ⟨5, 5, ⟨3911508623641591488435978240000000000000000000000000000000000, 1⟩⟩, ⟨5, 6, ⟨1476529745348150429409607680000000000000000000000000000000000, 1⟩⟩, ⟨5, 7, ⟨233136275581286909906780160000000000000000000000000000000000, 1⟩⟩]

def e_record_E1_r8_U1_factors : List (Polynomial × Nat) :=
  [([⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩], 1), ([⟨0, 0, ⟨1, 1⟩⟩, ⟨0, 1, ⟨1, 1⟩⟩], 1), ([⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩, ⟨1, 1, ⟨1, 1⟩⟩], 4), ([⟨0, 0, ⟨1, 9⟩⟩, ⟨0, 1, ⟨4, 3⟩⟩, ⟨0, 2, ⟨1, 1⟩⟩], 1)]

noncomputable def e_record_E1_r8_U1 (lam x : ℝ) : ℝ :=
  matrixValue numerator_E1_r8_U1 lam x / polynomialValue e_record_E1_r8_U1_denominator lam x

theorem e_record_E1_r8_U1_denominator_value (lam x : ℝ) :
    polynomialValue e_record_E1_r8_U1_denominator lam x = (233136275581286909906780160000000000000000000000000000000000 : ℝ)*(lam+1)^1*(x+1)^1*(lam*x+lam+1)^4*(x^2+4*x/3+1/9)^1 := by
  rw [factorCheck_sound e_record_E1_r8_U1_denominator ⟨233136275581286909906780160000000000000000000000000000000000, 1⟩ e_record_E1_r8_U1_factors lam x (by norm_num)
    (by norm_num [e_record_E1_r8_U1_factors, validPolynomial]) cert_0292_E1_r8_U1_allowed_denominator_factors]
  have hf0 : polynomialValue [⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩] lam x = (lam+1) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  have hf1 : polynomialValue [⟨0, 0, ⟨1, 1⟩⟩, ⟨0, 1, ⟨1, 1⟩⟩] lam x = (x+1) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  have hf2 : polynomialValue [⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩, ⟨1, 1, ⟨1, 1⟩⟩] lam x = (lam*x+lam+1) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  have hf3 : polynomialValue [⟨0, 0, ⟨1, 9⟩⟩, ⟨0, 1, ⟨4, 3⟩⟩, ⟨0, 2, ⟨1, 1⟩⟩] lam x = (x^2+4*x/3+1/9) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  simp only [e_record_E1_r8_U1_factors, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    hf0, hf1, hf2, hf3, mul_one]
  norm_num only [fractionValue, Int.cast_ofNat, Nat.cast_one, div_one]
  ac_rfl


theorem e_record_E1_r8_U1_denominator_positive (lam x : ℝ) (hlam : 0 ≤ lam) (hx : 0 ≤ x) :
    0 < polynomialValue e_record_E1_r8_U1_denominator lam x := by
  rw [e_record_E1_r8_U1_denominator_value]
  positivity

theorem e_record_E1_r8_U1_positive (lam x : ℝ)
    (hlam : (13/10 : ℝ) ≤ lam ∧ lam ≤ 29/20)
    (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) : 0 < e_record_E1_r8_U1 lam x := by
  apply div_pos ((e_common_E1_r8_U1_numerator_rectangle_positive lam x hlam hx))
    (e_record_E1_r8_U1_denominator_positive lam x (by linarith only [hlam.1]) (by linarith only [hx.1]))

def e_record_E1_r8_U2_denominator : Polynomial :=
  [⟨0, 0, ⟨108774651555961896960000000000000000000000000000000000000000, 1⟩⟩, ⟨0, 1, ⟨1414070470227504660480000000000000000000000000000000000000000, 1⟩⟩, ⟨0, 2, ⟨2284267682675199836160000000000000000000000000000000000000000, 1⟩⟩, ⟨0, 3, ⟨978971864003657072640000000000000000000000000000000000000000, 1⟩⟩, ⟨1, 0, ⟨543873257779809484800000000000000000000000000000000000000000, 1⟩⟩, ⟨1, 1, ⟨7505450957361370890240000000000000000000000000000000000000000, 1⟩⟩, ⟨1, 2, ⟨17077620294286017822720000000000000000000000000000000000000000, 1⟩⟩, ⟨1, 3, ⟨14031930050719084707840000000000000000000000000000000000000000, 1⟩⟩, ⟨1, 4, ⟨3915887456014628290560000000000000000000000000000000000000000, 1⟩⟩, ⟨2, 0, ⟨1087746515559618969600000000000000000000000000000000000000000, 1⟩⟩, ⟨2, 1, ⟨15881099127170436956160000000000000000000000000000000000000000, 1⟩⟩, ⟨2, 2, ⟨46120452259727844311040000000000000000000000000000000000000000, 1⟩⟩, ⟨2, 3, ⟨54822424384204796067840000000000000000000000000000000000000000, 1⟩⟩, ⟨2, 4, ⟨29369155920109712179200000000000000000000000000000000000000000, 1⟩⟩, ⟨2, 5, ⟨5873831184021942435840000000000000000000000000000000000000000, 1⟩⟩, ⟨3, 0, ⟨1087746515559618969600000000000000000000000000000000000000000, 1⟩⟩, ⟨3, 1, ⟨16751296339618132131840000000000000000000000000000000000000000, 1⟩⟩, ⟨3, 2, ⟨58738311840219424358400000000000000000000000000000000000000000, 1⟩⟩, ⟨3, 3, ⟨90500510094560298270720000000000000000000000000000000000000000, 1⟩⟩, ⟨3, 4, ⟨70268424905151385436160000000000000000000000000000000000000000, 1⟩⟩, ⟨3, 5, ⟨26758564282766626652160000000000000000000000000000000000000000, 1⟩⟩, ⟨3, 6, ⟨3915887456014628290560000000000000000000000000000000000000000, 1⟩⟩, ⟨4, 0, ⟨543873257779809484800000000000000000000000000000000000000000, 1⟩⟩, ⟨4, 1, ⟨8810746776032913653760000000000000000000000000000000000000000, 1⟩⟩, ⟨4, 2, ⟨36004409665023387893760000000000000000000000000000000000000000, 1⟩⟩, ⟨4, 3, ⟨67766607919364261806080000000000000000000000000000000000000000, 1⟩⟩, ⟨4, 4, ⟨68201706525588109393920000000000000000000000000000000000000000, 1⟩⟩, ⟨4, 5, ⟨37309705483694930657280000000000000000000000000000000000000000, 1⟩⟩, ⟨4, 6, ⟨10116042594704456417280000000000000000000000000000000000000000, 1⟩⟩, ⟨4, 7, ⟨978971864003657072640000000000000000000000000000000000000000, 1⟩⟩, ⟨5, 0, ⟨108774651555961896960000000000000000000000000000000000000000, 1⟩⟩, ⟨5, 1, ⟨1849169076451352248320000000000000000000000000000000000000000, 1⟩⟩, ⟨5, 2, ⟨8593197472920989859840000000000000000000000000000000000000000, 1⟩⟩, ⟨5, 3, ⟨19035564022293331968000000000000000000000000000000000000000000, 1⟩⟩, ⟨5, 4, ⟨23386550084531807846400000000000000000000000000000000000000000, 1⟩⟩, ⟨5, 5, ⟨16424972384950246440960000000000000000000000000000000000000000, 1⟩⟩, ⟨5, 6, ⟨6200155138689828126720000000000000000000000000000000000000000, 1⟩⟩, ⟨5, 7, ⟨978971864003657072640000000000000000000000000000000000000000, 1⟩⟩]

def e_record_E1_r8_U2_factors : List (Polynomial × Nat) :=
  [([⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩], 1), ([⟨0, 0, ⟨1, 1⟩⟩, ⟨0, 1, ⟨1, 1⟩⟩], 1), ([⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩, ⟨1, 1, ⟨1, 1⟩⟩], 4), ([⟨0, 0, ⟨1, 9⟩⟩, ⟨0, 1, ⟨4, 3⟩⟩, ⟨0, 2, ⟨1, 1⟩⟩], 1)]

noncomputable def e_record_E1_r8_U2 (lam x : ℝ) : ℝ :=
  matrixValue numerator_E1_r8_U2 lam x / polynomialValue e_record_E1_r8_U2_denominator lam x

theorem e_record_E1_r8_U2_denominator_value (lam x : ℝ) :
    polynomialValue e_record_E1_r8_U2_denominator lam x = (978971864003657072640000000000000000000000000000000000000000 : ℝ)*(lam+1)^1*(x+1)^1*(lam*x+lam+1)^4*(x^2+4*x/3+1/9)^1 := by
  rw [factorCheck_sound e_record_E1_r8_U2_denominator ⟨978971864003657072640000000000000000000000000000000000000000, 1⟩ e_record_E1_r8_U2_factors lam x (by norm_num)
    (by norm_num [e_record_E1_r8_U2_factors, validPolynomial]) cert_0303_E1_r8_U2_allowed_denominator_factors]
  have hf0 : polynomialValue [⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩] lam x = (lam+1) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  have hf1 : polynomialValue [⟨0, 0, ⟨1, 1⟩⟩, ⟨0, 1, ⟨1, 1⟩⟩] lam x = (x+1) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  have hf2 : polynomialValue [⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩, ⟨1, 1, ⟨1, 1⟩⟩] lam x = (lam*x+lam+1) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  have hf3 : polynomialValue [⟨0, 0, ⟨1, 9⟩⟩, ⟨0, 1, ⟨4, 3⟩⟩, ⟨0, 2, ⟨1, 1⟩⟩] lam x = (x^2+4*x/3+1/9) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  simp only [e_record_E1_r8_U2_factors, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    hf0, hf1, hf2, hf3, mul_one]
  norm_num only [fractionValue, Int.cast_ofNat, Nat.cast_one, div_one]
  ac_rfl


theorem e_record_E1_r8_U2_denominator_positive (lam x : ℝ) (hlam : 0 ≤ lam) (hx : 0 ≤ x) :
    0 < polynomialValue e_record_E1_r8_U2_denominator lam x := by
  rw [e_record_E1_r8_U2_denominator_value]
  positivity

theorem e_record_E1_r8_U2_positive (lam x : ℝ)
    (hlam : (13/10 : ℝ) ≤ lam ∧ lam ≤ 29/20)
    (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) : 0 < e_record_E1_r8_U2 lam x := by
  apply div_pos ((e_u2_numerator_rectangle_positive lam x hlam hx))
    (e_record_E1_r8_U2_denominator_positive lam x (by linarith only [hlam.1]) (by linarith only [hx.1]))

def e_record_E1_r8_U3_denominator : Polynomial :=
  [⟨0, 0, ⟨17403944248953903513600000000000000000000000000000, 1⟩⟩, ⟨0, 1, ⟨226251275236400745676800000000000000000000000000000, 1⟩⟩, ⟨0, 2, ⟨365482829228031973785600000000000000000000000000000, 1⟩⟩, ⟨0, 3, ⟨156635498240585131622400000000000000000000000000000, 1⟩⟩, ⟨1, 0, ⟨87019721244769517568000000000000000000000000000000, 1⟩⟩, ⟨1, 1, ⟨1200872153177819342438400000000000000000000000000000, 1⟩⟩, ⟨1, 2, ⟨2732419247085762851635200000000000000000000000000000, 1⟩⟩, ⟨1, 3, ⟨2245108808115053553254400000000000000000000000000000, 1⟩⟩, ⟨1, 4, ⟨626541992962340526489600000000000000000000000000000, 1⟩⟩, ⟨2, 0, ⟨174039442489539035136000000000000000000000000000000, 1⟩⟩, ⟨2, 1, ⟨2540975860347269912985600000000000000000000000000000, 1⟩⟩, ⟨2, 2, ⟨7379272361556455089766400000000000000000000000000000, 1⟩⟩, ⟨2, 3, ⟨8771587901472767370854400000000000000000000000000000, 1⟩⟩, ⟨2, 4, ⟨4699064947217553948672000000000000000000000000000000, 1⟩⟩, ⟨2, 5, ⟨939812989443510789734400000000000000000000000000000, 1⟩⟩, ⟨3, 0, ⟨174039442489539035136000000000000000000000000000000, 1⟩⟩, ⟨3, 1, ⟨2680207414338901141094400000000000000000000000000000, 1⟩⟩, ⟨3, 2, ⟨9398129894435107897344000000000000000000000000000000, 1⟩⟩, ⟨3, 3, ⟨14480081615129647723315200000000000000000000000000000, 1⟩⟩, ⟨3, 4, ⟨11242947984824221669785600000000000000000000000000000, 1⟩⟩, ⟨3, 5, ⟨4281370285242660264345600000000000000000000000000000, 1⟩⟩, ⟨3, 6, ⟨626541992962340526489600000000000000000000000000000, 1⟩⟩, ⟨4, 0, ⟨87019721244769517568000000000000000000000000000000, 1⟩⟩, ⟨4, 1, ⟨1409719484165266184601600000000000000000000000000000, 1⟩⟩, ⟨4, 2, ⟨5760705546403742063001600000000000000000000000000000, 1⟩⟩, ⟨4, 3, ⟨10842657267098281888972800000000000000000000000000000, 1⟩⟩, ⟨4, 4, ⟨10912273044094097503027200000000000000000000000000000, 1⟩⟩, ⟨4, 5, ⟨5969552877391188905164800000000000000000000000000000, 1⟩⟩, ⟨4, 6, ⟨1618566815152713026764800000000000000000000000000000, 1⟩⟩, ⟨4, 7, ⟨156635498240585131622400000000000000000000000000000, 1⟩⟩, ⟨5, 0, ⟨17403944248953903513600000000000000000000000000000, 1⟩⟩, ⟨5, 1, ⟨295867052232216359731200000000000000000000000000000, 1⟩⟩, ⟨5, 2, ⟨1374911595667358377574400000000000000000000000000000, 1⟩⟩, ⟨5, 3, ⟨3045690243566933114880000000000000000000000000000000, 1⟩⟩, ⟨5, 4, ⟨3741848013525089255424000000000000000000000000000000, 1⟩⟩, ⟨5, 5, ⟨2627995581592039430553600000000000000000000000000000, 1⟩⟩, ⟨5, 6, ⟨992024822190372500275200000000000000000000000000000, 1⟩⟩, ⟨5, 7, ⟨156635498240585131622400000000000000000000000000000, 1⟩⟩]

def e_record_E1_r8_U3_factors : List (Polynomial × Nat) :=
  [([⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩], 1), ([⟨0, 0, ⟨1, 1⟩⟩, ⟨0, 1, ⟨1, 1⟩⟩], 1), ([⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩, ⟨1, 1, ⟨1, 1⟩⟩], 4), ([⟨0, 0, ⟨1, 9⟩⟩, ⟨0, 1, ⟨4, 3⟩⟩, ⟨0, 2, ⟨1, 1⟩⟩], 1)]

noncomputable def e_record_E1_r8_U3 (lam x : ℝ) : ℝ :=
  matrixValue numerator_E1_r8_U3 lam x / polynomialValue e_record_E1_r8_U3_denominator lam x

theorem e_record_E1_r8_U3_denominator_value (lam x : ℝ) :
    polynomialValue e_record_E1_r8_U3_denominator lam x = (156635498240585131622400000000000000000000000000000 : ℝ)*(lam+1)^1*(x+1)^1*(lam*x+lam+1)^4*(x^2+4*x/3+1/9)^1 := by
  rw [factorCheck_sound e_record_E1_r8_U3_denominator ⟨156635498240585131622400000000000000000000000000000, 1⟩ e_record_E1_r8_U3_factors lam x (by norm_num)
    (by norm_num [e_record_E1_r8_U3_factors, validPolynomial]) cert_0401_E1_r8_U3_allowed_denominator_factors]
  have hf0 : polynomialValue [⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩] lam x = (lam+1) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  have hf1 : polynomialValue [⟨0, 0, ⟨1, 1⟩⟩, ⟨0, 1, ⟨1, 1⟩⟩] lam x = (x+1) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  have hf2 : polynomialValue [⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩, ⟨1, 1, ⟨1, 1⟩⟩] lam x = (lam*x+lam+1) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  have hf3 : polynomialValue [⟨0, 0, ⟨1, 9⟩⟩, ⟨0, 1, ⟨4, 3⟩⟩, ⟨0, 2, ⟨1, 1⟩⟩] lam x = (x^2+4*x/3+1/9) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  simp only [e_record_E1_r8_U3_factors, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    hf0, hf1, hf2, hf3, mul_one]
  norm_num only [fractionValue, Int.cast_ofNat, Nat.cast_one, div_one]
  ac_rfl


theorem e_record_E1_r8_U3_denominator_positive (lam x : ℝ) (hlam : 0 ≤ lam) (hx : 0 ≤ x) :
    0 < polynomialValue e_record_E1_r8_U3_denominator lam x := by
  rw [e_record_E1_r8_U3_denominator_value]
  positivity

theorem e_record_E1_r8_U3_positive (lam x : ℝ)
    (hlam : (13/10 : ℝ) ≤ lam ∧ lam ≤ 29/20)
    (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) : 0 < e_record_E1_r8_U3 lam x := by
  apply div_pos ((e_common_E1_r8_U3_numerator_rectangle_positive lam x hlam hx))
    (e_record_E1_r8_U3_denominator_positive lam x (by linarith only [hlam.1]) (by linarith only [hx.1]))

def e_record_E1_r8_D_denominator : Polynomial :=
  [⟨0, 0, ⟨72718745600000000000, 1⟩⟩, ⟨0, 1, ⟨872624947200000000000, 1⟩⟩, ⟨0, 2, ⟨654468710400000000000, 1⟩⟩, ⟨1, 0, ⟨145437491200000000000, 1⟩⟩, ⟨1, 1, ⟨1890687385600000000000, 1⟩⟩, ⟨1, 2, ⟨3054187315200000000000, 1⟩⟩, ⟨1, 3, ⟨1308937420800000000000, 1⟩⟩, ⟨2, 0, ⟨72718745600000000000, 1⟩⟩, ⟨2, 1, ⟨1018062438400000000000, 1⟩⟩, ⟨2, 2, ⟨2472437350400000000000, 1⟩⟩, ⟨2, 3, ⟨2181562368000000000000, 1⟩⟩, ⟨2, 4, ⟨654468710400000000000, 1⟩⟩]

def e_record_E1_r8_D_factors : List (Polynomial × Nat) :=
  [([⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩, ⟨1, 1, ⟨1, 1⟩⟩], 2), ([⟨0, 0, ⟨1, 9⟩⟩, ⟨0, 1, ⟨4, 3⟩⟩, ⟨0, 2, ⟨1, 1⟩⟩], 1)]

noncomputable def e_record_E1_r8_D (lam x : ℝ) : ℝ :=
  matrixValue numerator_E1_r8_D lam x / polynomialValue e_record_E1_r8_D_denominator lam x

theorem e_record_E1_r8_D_denominator_value (lam x : ℝ) :
    polynomialValue e_record_E1_r8_D_denominator lam x = (654468710400000000000 : ℝ)*(lam*x+lam+1)^2*(x^2+4*x/3+1/9)^1 := by
  rw [factorCheck_sound e_record_E1_r8_D_denominator ⟨654468710400000000000, 1⟩ e_record_E1_r8_D_factors lam x (by norm_num)
    (by norm_num [e_record_E1_r8_D_factors, validPolynomial]) cert_0413_E1_r8_D_allowed_denominator_factors]
  have hf0 : polynomialValue [⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩, ⟨1, 1, ⟨1, 1⟩⟩] lam x = (lam*x+lam+1) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  have hf1 : polynomialValue [⟨0, 0, ⟨1, 9⟩⟩, ⟨0, 1, ⟨4, 3⟩⟩, ⟨0, 2, ⟨1, 1⟩⟩] lam x = (x^2+4*x/3+1/9) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  simp only [e_record_E1_r8_D_factors, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    hf0, hf1, mul_one]
  norm_num only [fractionValue, Int.cast_ofNat, Nat.cast_one, div_one]
  ac_rfl


theorem e_record_E1_r8_D_denominator_positive (lam x : ℝ) (hlam : 0 ≤ lam) (hx : 0 ≤ x) :
    0 < polynomialValue e_record_E1_r8_D_denominator lam x := by
  rw [e_record_E1_r8_D_denominator_value]
  positivity

theorem e_record_E1_r8_D_positive (lam x : ℝ)
    (hlam : (13/10 : ℝ) ≤ lam ∧ lam ≤ 29/20)
    (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) : 0 < e_record_E1_r8_D lam x := by
  apply div_pos ((e_common_E1_r8_D_numerator_rectangle_positive lam x hlam hx))
    (e_record_E1_r8_D_denominator_positive lam x (by linarith only [hlam.1]) (by linarith only [hx.1]))

def e_record_E2_r8_H0_denominator : Polynomial :=
  [⟨0, 0, ⟨194560781558218752000000000000, 1⟩⟩, ⟨0, 1, ⟨2529290160256843776000000000000, 1⟩⟩, ⟨0, 2, ⟨4085776412722593792000000000000, 1⟩⟩, ⟨0, 3, ⟨1751047034023968768000000000000, 1⟩⟩, ⟨1, 0, ⟨778243126232875008000000000000, 1⟩⟩, ⟨1, 1, ⟨10700842985702031360000000000000, 1⟩⟩, ⟨1, 2, ⟨23930976131660906496000000000000, 1⟩⟩, ⟨1, 3, ⟨19261517374263656448000000000000, 1⟩⟩, ⟨1, 4, ⟨5253141102071906304000000000000, 1⟩⟩, ⟨2, 0, ⟨1167364689349312512000000000000, 1⟩⟩, ⟨2, 1, ⟨16926787995565031424000000000000, 1⟩⟩, ⟨2, 2, ⟨47861952263321812992000000000000, 1⟩⟩, ⟨2, 3, ⟨54866140399417688064000000000000, 1⟩⟩, ⟨2, 4, ⟨28016752544383500288000000000000, 1⟩⟩, ⟨2, 5, ⟨5253141102071906304000000000000, 1⟩⟩, ⟨3, 0, ⟨778243126232875008000000000000, 1⟩⟩, ⟨3, 1, ⟨11868207675051343872000000000000, 1⟩⟩, ⟨3, 2, ⟨40274081782551281664000000000000, 1⟩⟩, ⟨3, 3, ⟨59146477593698500608000000000000, 1⟩⟩, ⟨3, 4, ⟨42803371942808125440000000000000, 1⟩⟩, ⟨3, 5, ⟨14592058616866406400000000000000, 1⟩⟩, ⟨3, 6, ⟨1751047034023968768000000000000, 1⟩⟩, ⟨4, 0, ⟨194560781558218752000000000000, 1⟩⟩, ⟨4, 1, ⟨3112972504931500032000000000000, 1⟩⟩, ⟨4, 2, ⟨12257329238167781376000000000000, 1⟩⟩, ⟨4, 3, ⟨21790807534520500224000000000000, 1⟩⟩, ⟨4, 4, ⟨20039760500496531456000000000000, 1⟩⟩, ⟨4, 5, ⟨9338917514794500096000000000000, 1⟩⟩, ⟨4, 6, ⟨1751047034023968768000000000000, 1⟩⟩]

def e_record_E2_r8_H0_factors : List (Polynomial × Nat) :=
  [([⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩], 1), ([⟨0, 0, ⟨1, 1⟩⟩, ⟨0, 1, ⟨1, 1⟩⟩], 1), ([⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩, ⟨1, 1, ⟨1, 1⟩⟩], 3), ([⟨0, 0, ⟨1, 9⟩⟩, ⟨0, 1, ⟨4, 3⟩⟩, ⟨0, 2, ⟨1, 1⟩⟩], 1)]

noncomputable def e_record_E2_r8_H0 (lam x : ℝ) : ℝ :=
  matrixValue numerator_E2_r8_H0 lam x / polynomialValue e_record_E2_r8_H0_denominator lam x

theorem e_record_E2_r8_H0_denominator_value (lam x : ℝ) :
    polynomialValue e_record_E2_r8_H0_denominator lam x = (1751047034023968768000000000000 : ℝ)*(lam+1)^1*(x+1)^1*(lam*x+lam+1)^3*(x^2+4*x/3+1/9)^1 := by
  rw [factorCheck_sound e_record_E2_r8_H0_denominator ⟨1751047034023968768000000000000, 1⟩ e_record_E2_r8_H0_factors lam x (by norm_num)
    (by norm_num [e_record_E2_r8_H0_factors, validPolynomial]) cert_0422_E2_r8_H0_allowed_denominator_factors]
  have hf0 : polynomialValue [⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩] lam x = (lam+1) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  have hf1 : polynomialValue [⟨0, 0, ⟨1, 1⟩⟩, ⟨0, 1, ⟨1, 1⟩⟩] lam x = (x+1) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  have hf2 : polynomialValue [⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩, ⟨1, 1, ⟨1, 1⟩⟩] lam x = (lam*x+lam+1) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  have hf3 : polynomialValue [⟨0, 0, ⟨1, 9⟩⟩, ⟨0, 1, ⟨4, 3⟩⟩, ⟨0, 2, ⟨1, 1⟩⟩] lam x = (x^2+4*x/3+1/9) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  simp only [e_record_E2_r8_H0_factors, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    hf0, hf1, hf2, hf3, mul_one]
  norm_num only [fractionValue, Int.cast_ofNat, Nat.cast_one, div_one]
  ac_rfl


theorem e_record_E2_r8_H0_denominator_positive (lam x : ℝ) (hlam : 0 ≤ lam) (hx : 0 ≤ x) :
    0 < polynomialValue e_record_E2_r8_H0_denominator lam x := by
  rw [e_record_E2_r8_H0_denominator_value]
  positivity

theorem e_record_E2_r8_H0_positive (lam x : ℝ)
    (hlam : (29/20 : ℝ) ≤ lam ∧ lam ≤ 8/5)
    (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) : 0 < e_record_E2_r8_H0 lam x := by
  apply div_pos ((e_common_E2_r8_H0_numerator_rectangle_positive lam x hlam hx))
    (e_record_E2_r8_H0_denominator_positive lam x (by linarith only [hlam.1]) (by linarith only [hx.1]))

def e_record_E2_r8_U0_denominator : Polynomial :=
  [⟨0, 0, ⟨12036405220320858166523854848000000000000000000000000000000000000, 1⟩⟩, ⟨0, 1, ⟨156473267864171156164810113024000000000000000000000000000000000000, 1⟩⟩, ⟨0, 2, ⟨252764509626738021497000951808000000000000000000000000000000000000, 1⟩⟩, ⟨0, 3, ⟨108327646982887723498714693632000000000000000000000000000000000000, 1⟩⟩, ⟨1, 0, ⟨36109215660962574499571564544000000000000000000000000000000000000, 1⟩⟩, ⟨1, 1, ⟨493492614033155184827478048768000000000000000000000000000000000000, 1⟩⟩, ⟨1, 2, ⟨1071240064608556376820623081472000000000000000000000000000000000000, 1⟩⟩, ⟨1, 3, ⟨830511960202139213490145984512000000000000000000000000000000000000, 1⟩⟩, ⟨1, 4, ⟨216655293965775446997429387264000000000000000000000000000000000000, 1⟩⟩, ⟨2, 0, ⟨36109215660962574499571564544000000000000000000000000000000000000, 1⟩⟩, ⟨2, 1, ⟨517565424473796901160525758464000000000000000000000000000000000000, 1⟩⟩, ⟨2, 2, ⟨1396223005557219547316767162368000000000000000000000000000000000000, 1⟩⟩, ⟨2, 3, ⟨1492514247319786412648958001152000000000000000000000000000000000000, 1⟩⟩, ⟨2, 4, ⟨686075097558288915491859726336000000000000000000000000000000000000, 1⟩⟩, ⟨2, 5, ⟨108327646982887723498714693632000000000000000000000000000000000000, 1⟩⟩, ⟨3, 0, ⟨12036405220320858166523854848000000000000000000000000000000000000, 1⟩⟩, ⟨3, 1, ⟨180546078304812872497857822720000000000000000000000000000000000000, 1⟩⟩, ⟨3, 2, ⟨577747450575401191993145032704000000000000000000000000000000000000, 1⟩⟩, ⟨3, 3, ⟨770329934100534922657526710272000000000000000000000000000000000000, 1⟩⟩, ⟨3, 4, ⟨469419803592513468494430339072000000000000000000000000000000000000, 1⟩⟩, ⟨3, 5, ⟨108327646982887723498714693632000000000000000000000000000000000000, 1⟩⟩]

def e_record_E2_r8_U0_factors : List (Polynomial × Nat) :=
  [([⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩], 1), ([⟨0, 0, ⟨1, 1⟩⟩, ⟨0, 1, ⟨1, 1⟩⟩], 1), ([⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩, ⟨1, 1, ⟨1, 1⟩⟩], 2), ([⟨0, 0, ⟨1, 9⟩⟩, ⟨0, 1, ⟨4, 3⟩⟩, ⟨0, 2, ⟨1, 1⟩⟩], 1)]

noncomputable def e_record_E2_r8_U0 (lam x : ℝ) : ℝ :=
  matrixValue numerator_E2_r8_U0 lam x / polynomialValue e_record_E2_r8_U0_denominator lam x

theorem e_record_E2_r8_U0_denominator_value (lam x : ℝ) :
    polynomialValue e_record_E2_r8_U0_denominator lam x = (108327646982887723498714693632000000000000000000000000000000000000 : ℝ)*(lam+1)^1*(x+1)^1*(lam*x+lam+1)^2*(x^2+4*x/3+1/9)^1 := by
  rw [factorCheck_sound e_record_E2_r8_U0_denominator ⟨108327646982887723498714693632000000000000000000000000000000000000, 1⟩ e_record_E2_r8_U0_factors lam x (by norm_num)
    (by norm_num [e_record_E2_r8_U0_factors, validPolynomial]) cert_0432_E2_r8_U0_allowed_denominator_factors]
  have hf0 : polynomialValue [⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩] lam x = (lam+1) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  have hf1 : polynomialValue [⟨0, 0, ⟨1, 1⟩⟩, ⟨0, 1, ⟨1, 1⟩⟩] lam x = (x+1) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  have hf2 : polynomialValue [⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩, ⟨1, 1, ⟨1, 1⟩⟩] lam x = (lam*x+lam+1) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  have hf3 : polynomialValue [⟨0, 0, ⟨1, 9⟩⟩, ⟨0, 1, ⟨4, 3⟩⟩, ⟨0, 2, ⟨1, 1⟩⟩] lam x = (x^2+4*x/3+1/9) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  simp only [e_record_E2_r8_U0_factors, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    hf0, hf1, hf2, hf3, mul_one]
  norm_num only [fractionValue, Int.cast_ofNat, Nat.cast_one, div_one]
  ac_rfl


theorem e_record_E2_r8_U0_denominator_positive (lam x : ℝ) (hlam : 0 ≤ lam) (hx : 0 ≤ x) :
    0 < polynomialValue e_record_E2_r8_U0_denominator lam x := by
  rw [e_record_E2_r8_U0_denominator_value]
  positivity

theorem e_record_E2_r8_U0_positive (lam x : ℝ)
    (hlam : (29/20 : ℝ) ≤ lam ∧ lam ≤ 8/5)
    (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) : 0 < e_record_E2_r8_U0 lam x := by
  apply div_pos ((e_common_E2_r8_U0_numerator_rectangle_positive lam x hlam hx))
    (e_record_E2_r8_U0_denominator_positive lam x (by linarith only [hlam.1]) (by linarith only [hx.1]))

def e_record_E2_r8_U1_denominator : Polynomial :=
  [⟨0, 0, ⟨3858592717780864486657228800000000000000000000000000000000000, 1⟩⟩, ⟨0, 1, ⟨50161705331151238326543974400000000000000000000000000000000000, 1⟩⟩, ⟨0, 2, ⟨81030447073398154219801804800000000000000000000000000000000000, 1⟩⟩, ⟨0, 3, ⟨34727334460027780379915059200000000000000000000000000000000000, 1⟩⟩, ⟨1, 0, ⟨19292963588904322433286144000000000000000000000000000000000000, 1⟩⟩, ⟨1, 1, ⟨266242897526879649579348787200000000000000000000000000000000000, 1⟩⟩, ⟨1, 2, ⟨605799056691595724405184921600000000000000000000000000000000000, 1⟩⟩, ⟨1, 3, ⟨497758460593731518778782515200000000000000000000000000000000000, 1⟩⟩, ⟨1, 4, ⟨138909337840111121519660236800000000000000000000000000000000000, 1⟩⟩, ⟨2, 0, ⟨38585927177808644866572288000000000000000000000000000000000000, 1⟩⟩, ⟨2, 1, ⟨563354536796006215051955404800000000000000000000000000000000000, 1⟩⟩, ⟨2, 2, ⟨1636043312339086542342665011200000000000000000000000000000000000, 1⟩⟩, ⟨2, 3, ⟨1944730729761555701275243315200000000000000000000000000000000000, 1⟩⟩, ⟨2, 4, ⟨1041820033800833411397451776000000000000000000000000000000000000, 1⟩⟩, ⟨2, 5, ⟨208364006760166682279490355200000000000000000000000000000000000, 1⟩⟩, ⟨3, 0, ⟨38585927177808644866572288000000000000000000000000000000000000, 1⟩⟩, ⟨3, 1, ⟨594223278538253130945213235200000000000000000000000000000000000, 1⟩⟩, ⟨3, 2, ⟨2083640067601666822794903552000000000000000000000000000000000000, 1⟩⟩, ⟨3, 3, ⟨3210349141193679252898814361600000000000000000000000000000000000, 1⟩⟩, ⟨3, 4, ⟨2492650895686438458380569804800000000000000000000000000000000000, 1⟩⟩, ⟨3, 5, ⟨949213808574092663717678284800000000000000000000000000000000000, 1⟩⟩, ⟨3, 6, ⟨138909337840111121519660236800000000000000000000000000000000000, 1⟩⟩, ⟨4, 0, ⟨19292963588904322433286144000000000000000000000000000000000000, 1⟩⟩, ⟨4, 1, ⟨312546010140250023419235532800000000000000000000000000000000000, 1⟩⟩, ⟨4, 2, ⟨1277194189585466145083542732800000000000000000000000000000000000, 1⟩⟩, ⟨4, 3, ⟨2403903263177478575187453542400000000000000000000000000000000000, 1⟩⟩, ⟨4, 4, ⟨2419337634048602033134082457600000000000000000000000000000000000, 1⟩⟩, ⟨4, 5, ⟨1323497302198836518923429478400000000000000000000000000000000000, 1⟩⟩, ⟨4, 6, ⟨358849122753620397259122278400000000000000000000000000000000000, 1⟩⟩, ⟨4, 7, ⟨34727334460027780379915059200000000000000000000000000000000000, 1⟩⟩, ⟨5, 0, ⟨3858592717780864486657228800000000000000000000000000000000000, 1⟩⟩, ⟨5, 1, ⟨65596076202274696273172889600000000000000000000000000000000000, 1⟩⟩, ⟨5, 2, ⟨304828824704688294445921075200000000000000000000000000000000000, 1⟩⟩, ⟨5, 3, ⟨675253725611651285165015040000000000000000000000000000000000000, 1⟩⟩, ⟨5, 4, ⟨829597434322885864631304192000000000000000000000000000000000000, 1⟩⟩, ⟨5, 5, ⟨582647500384910537485241548800000000000000000000000000000000000, 1⟩⟩, ⟨5, 6, ⟨219939784913509275739462041600000000000000000000000000000000000, 1⟩⟩, ⟨5, 7, ⟨34727334460027780379915059200000000000000000000000000000000000, 1⟩⟩]

def e_record_E2_r8_U1_factors : List (Polynomial × Nat) :=
  [([⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩], 1), ([⟨0, 0, ⟨1, 1⟩⟩, ⟨0, 1, ⟨1, 1⟩⟩], 1), ([⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩, ⟨1, 1, ⟨1, 1⟩⟩], 4), ([⟨0, 0, ⟨1, 9⟩⟩, ⟨0, 1, ⟨4, 3⟩⟩, ⟨0, 2, ⟨1, 1⟩⟩], 1)]

noncomputable def e_record_E2_r8_U1 (lam x : ℝ) : ℝ :=
  matrixValue numerator_E2_r8_U1 lam x / polynomialValue e_record_E2_r8_U1_denominator lam x

theorem e_record_E2_r8_U1_denominator_value (lam x : ℝ) :
    polynomialValue e_record_E2_r8_U1_denominator lam x = (34727334460027780379915059200000000000000000000000000000000000 : ℝ)*(lam+1)^1*(x+1)^1*(lam*x+lam+1)^4*(x^2+4*x/3+1/9)^1 := by
  rw [factorCheck_sound e_record_E2_r8_U1_denominator ⟨34727334460027780379915059200000000000000000000000000000000000, 1⟩ e_record_E2_r8_U1_factors lam x (by norm_num)
    (by norm_num [e_record_E2_r8_U1_factors, validPolynomial]) cert_0441_E2_r8_U1_allowed_denominator_factors]
  have hf0 : polynomialValue [⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩] lam x = (lam+1) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  have hf1 : polynomialValue [⟨0, 0, ⟨1, 1⟩⟩, ⟨0, 1, ⟨1, 1⟩⟩] lam x = (x+1) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  have hf2 : polynomialValue [⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩, ⟨1, 1, ⟨1, 1⟩⟩] lam x = (lam*x+lam+1) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  have hf3 : polynomialValue [⟨0, 0, ⟨1, 9⟩⟩, ⟨0, 1, ⟨4, 3⟩⟩, ⟨0, 2, ⟨1, 1⟩⟩] lam x = (x^2+4*x/3+1/9) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  simp only [e_record_E2_r8_U1_factors, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    hf0, hf1, hf2, hf3, mul_one]
  norm_num only [fractionValue, Int.cast_ofNat, Nat.cast_one, div_one]
  ac_rfl


theorem e_record_E2_r8_U1_denominator_positive (lam x : ℝ) (hlam : 0 ≤ lam) (hx : 0 ≤ x) :
    0 < polynomialValue e_record_E2_r8_U1_denominator lam x := by
  rw [e_record_E2_r8_U1_denominator_value]
  positivity

theorem e_record_E2_r8_U1_positive (lam x : ℝ)
    (hlam : (29/20 : ℝ) ≤ lam ∧ lam ≤ 8/5)
    (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) : 0 < e_record_E2_r8_U1 lam x := by
  apply div_pos ((e_common_E2_r8_U1_numerator_rectangle_positive lam x hlam hx))
    (e_record_E2_r8_U1_denominator_positive lam x (by linarith only [hlam.1]) (by linarith only [hx.1]))

def e_record_E2_r8_U2_denominator : Polynomial :=
  [⟨0, 0, ⟨648110843486439211008000000000000000000000000000000000000000, 1⟩⟩, ⟨0, 1, ⟨8425440965323709743104000000000000000000000000000000000000000, 1⟩⟩, ⟨0, 2, ⟨13610327713215223431168000000000000000000000000000000000000000, 1⟩⟩, ⟨0, 3, ⟨5832997591377952899072000000000000000000000000000000000000000, 1⟩⟩, ⟨1, 0, ⟨3240554217432196055040000000000000000000000000000000000000000, 1⟩⟩, ⟨1, 1, ⟨44719648200564305559552000000000000000000000000000000000000000, 1⟩⟩, ⟨1, 2, ⟨101753402427370956128256000000000000000000000000000000000000000, 1⟩⟩, ⟨1, 3, ⟨83606298809750658220032000000000000000000000000000000000000000, 1⟩⟩, ⟨1, 4, ⟨23331990365511811596288000000000000000000000000000000000000000, 1⟩⟩, ⟨2, 0, ⟨6481108434864392110080000000000000000000000000000000000000000, 1⟩⟩, ⟨2, 1, ⟨94624183149020124807168000000000000000000000000000000000000000, 1⟩⟩, ⟨2, 2, ⟨274798997638250225467392000000000000000000000000000000000000000, 1⟩⟩, ⟨2, 3, ⟨326647865117165362348032000000000000000000000000000000000000000, 1⟩⟩, ⟨2, 4, ⟨174989927741338586972160000000000000000000000000000000000000000, 1⟩⟩, ⟨2, 5, ⟨34997985548267717394432000000000000000000000000000000000000000, 1⟩⟩, ⟨3, 0, ⟨6481108434864392110080000000000000000000000000000000000000000, 1⟩⟩, ⟨3, 1, ⟨99809069896911638495232000000000000000000000000000000000000000, 1⟩⟩, ⟨3, 2, ⟨349979855482677173944320000000000000000000000000000000000000000, 1⟩⟩, ⟨3, 3, ⟨539228221780717423558656000000000000000000000000000000000000000, 1⟩⟩, ⟨3, 4, ⟨418679604892239730311168000000000000000000000000000000000000000, 1⟩⟩, ⟨3, 5, ⟨159435267497664045907968000000000000000000000000000000000000000, 1⟩⟩, ⟨3, 6, ⟨23331990365511811596288000000000000000000000000000000000000000, 1⟩⟩, ⟨4, 0, ⟨3240554217432196055040000000000000000000000000000000000000000, 1⟩⟩, ⟨4, 1, ⟨52496978322401576091648000000000000000000000000000000000000000, 1⟩⟩, ⟨4, 2, ⟨214524689194011378843648000000000000000000000000000000000000000, 1⟩⟩, ⟨4, 3, ⟨403773055492051628457984000000000000000000000000000000000000000, 1⟩⟩, ⟨4, 4, ⟨406365498865997385302016000000000000000000000000000000000000000, 1⟩⟩, ⟨4, 5, ⟨222302019315848649375744000000000000000000000000000000000000000, 1⟩⟩, ⟨4, 6, ⟨60274308444238846623744000000000000000000000000000000000000000, 1⟩⟩, ⟨4, 7, ⟨5832997591377952899072000000000000000000000000000000000000000, 1⟩⟩, ⟨5, 0, ⟨648110843486439211008000000000000000000000000000000000000000, 1⟩⟩, ⟨5, 1, ⟨11017884339269466587136000000000000000000000000000000000000000, 1⟩⟩, ⟨5, 2, ⟨51200756635428697669632000000000000000000000000000000000000000, 1⟩⟩, ⟨5, 3, ⟨113419397610126861926400000000000000000000000000000000000000000, 1⟩⟩, ⟨5, 4, ⟨139343831349584430366720000000000000000000000000000000000000000, 1⟩⟩, ⟨5, 5, ⟨97864737366452320862208000000000000000000000000000000000000000, 1⟩⟩, ⟨5, 6, ⟨36942318078727035027456000000000000000000000000000000000000000, 1⟩⟩, ⟨5, 7, ⟨5832997591377952899072000000000000000000000000000000000000000, 1⟩⟩]

def e_record_E2_r8_U2_factors : List (Polynomial × Nat) :=
  [([⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩], 1), ([⟨0, 0, ⟨1, 1⟩⟩, ⟨0, 1, ⟨1, 1⟩⟩], 1), ([⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩, ⟨1, 1, ⟨1, 1⟩⟩], 4), ([⟨0, 0, ⟨1, 9⟩⟩, ⟨0, 1, ⟨4, 3⟩⟩, ⟨0, 2, ⟨1, 1⟩⟩], 1)]

noncomputable def e_record_E2_r8_U2 (lam x : ℝ) : ℝ :=
  matrixValue numerator_E2_r8_U2 lam x / polynomialValue e_record_E2_r8_U2_denominator lam x

theorem e_record_E2_r8_U2_denominator_value (lam x : ℝ) :
    polynomialValue e_record_E2_r8_U2_denominator lam x = (5832997591377952899072000000000000000000000000000000000000000 : ℝ)*(lam+1)^1*(x+1)^1*(lam*x+lam+1)^4*(x^2+4*x/3+1/9)^1 := by
  rw [factorCheck_sound e_record_E2_r8_U2_denominator ⟨5832997591377952899072000000000000000000000000000000000000000, 1⟩ e_record_E2_r8_U2_factors lam x (by norm_num)
    (by norm_num [e_record_E2_r8_U2_factors, validPolynomial]) cert_0452_E2_r8_U2_allowed_denominator_factors]
  have hf0 : polynomialValue [⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩] lam x = (lam+1) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  have hf1 : polynomialValue [⟨0, 0, ⟨1, 1⟩⟩, ⟨0, 1, ⟨1, 1⟩⟩] lam x = (x+1) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  have hf2 : polynomialValue [⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩, ⟨1, 1, ⟨1, 1⟩⟩] lam x = (lam*x+lam+1) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  have hf3 : polynomialValue [⟨0, 0, ⟨1, 9⟩⟩, ⟨0, 1, ⟨4, 3⟩⟩, ⟨0, 2, ⟨1, 1⟩⟩] lam x = (x^2+4*x/3+1/9) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  simp only [e_record_E2_r8_U2_factors, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    hf0, hf1, hf2, hf3, mul_one]
  norm_num only [fractionValue, Int.cast_ofNat, Nat.cast_one, div_one]
  ac_rfl


theorem e_record_E2_r8_U2_denominator_positive (lam x : ℝ) (hlam : 0 ≤ lam) (hx : 0 ≤ x) :
    0 < polynomialValue e_record_E2_r8_U2_denominator lam x := by
  rw [e_record_E2_r8_U2_denominator_value]
  positivity

theorem e_record_E2_r8_U2_positive (lam x : ℝ)
    (hlam : (29/20 : ℝ) ≤ lam ∧ lam ≤ 8/5)
    (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) : 0 < e_record_E2_r8_U2 lam x := by
  apply div_pos ((e_common_E2_r8_U2_numerator_rectangle_positive lam x hlam hx))
    (e_record_E2_r8_U2_denominator_positive lam x (by linarith only [hlam.1]) (by linarith only [hx.1]))

def e_record_E2_r8_U3_denominator : Polynomial :=
  [⟨0, 0, ⟨41479093983132109504512000000000000000000000000000, 1⟩⟩, ⟨0, 1, ⟨539228221780717423558656000000000000000000000000000, 1⟩⟩, ⟨0, 2, ⟨871060973645774299594752000000000000000000000000000, 1⟩⟩, ⟨0, 3, ⟨373311845848188985540608000000000000000000000000000, 1⟩⟩, ⟨1, 0, ⟨207395469915660547522560000000000000000000000000000, 1⟩⟩, ⟨1, 1, ⟨2862057484836115555811328000000000000000000000000000, 1⟩⟩, ⟨1, 2, ⟨6512217755351741192208384000000000000000000000000000, 1⟩⟩, ⟨1, 3, ⟨5350803123824042126082048000000000000000000000000000, 1⟩⟩, ⟨1, 4, ⟨1493247383392755942162432000000000000000000000000000, 1⟩⟩, ⟨2, 0, ⟨414790939831321095045120000000000000000000000000000, 1⟩⟩, ⟨2, 1, ⟨6055947721537287987658752000000000000000000000000000, 1⟩⟩, ⟨2, 2, ⟨17587135848848014429913088000000000000000000000000000, 1⟩⟩, ⟨2, 3, ⟨20905463367498583190274048000000000000000000000000000, 1⟩⟩, ⟨2, 4, ⟨11199355375445669566218240000000000000000000000000000, 1⟩⟩, ⟨2, 5, ⟨2239871075089133913243648000000000000000000000000000, 1⟩⟩, ⟨3, 0, ⟨414790939831321095045120000000000000000000000000000, 1⟩⟩, ⟨3, 1, ⟨6387780473402344863694848000000000000000000000000000, 1⟩⟩, ⟨3, 2, ⟨22398710750891339132436480000000000000000000000000000, 1⟩⟩, ⟨3, 3, ⟨34510606193965915107753984000000000000000000000000000, 1⟩⟩, ⟨3, 4, ⟨26795494713103342739914752000000000000000000000000000, 1⟩⟩, ⟨3, 5, ⟨10203857119850498938109952000000000000000000000000000, 1⟩⟩, ⟨3, 6, ⟨1493247383392755942162432000000000000000000000000000, 1⟩⟩, ⟨4, 0, ⟨207395469915660547522560000000000000000000000000000, 1⟩⟩, ⟨4, 1, ⟨3359806612633700869865472000000000000000000000000000, 1⟩⟩, ⟨4, 2, ⟨13729580108416728245993472000000000000000000000000000, 1⟩⟩, ⟨4, 3, ⟨25841475551491304221310976000000000000000000000000000, 1⟩⟩, ⟨4, 4, ⟨26007391927423832659329024000000000000000000000000000, 1⟩⟩, ⟨4, 5, ⟨14227329236214313560047616000000000000000000000000000, 1⟩⟩, ⟨4, 6, ⟨3857555740431286183919616000000000000000000000000000, 1⟩⟩, ⟨4, 7, ⟨373311845848188985540608000000000000000000000000000, 1⟩⟩, ⟨5, 0, ⟨41479093983132109504512000000000000000000000000000, 1⟩⟩, ⟨5, 1, ⟨705144597713245861576704000000000000000000000000000, 1⟩⟩, ⟨5, 2, ⟨3276848424667436650856448000000000000000000000000000, 1⟩⟩, ⟨5, 3, ⟨7258841447048119163289600000000000000000000000000000, 1⟩⟩, ⟨5, 4, ⟨8918005206373403543470080000000000000000000000000000, 1⟩⟩, ⟨5, 5, ⟨6263343191452948535181312000000000000000000000000000, 1⟩⟩, ⟨5, 6, ⟨2364308357038530241757184000000000000000000000000000, 1⟩⟩, ⟨5, 7, ⟨373311845848188985540608000000000000000000000000000, 1⟩⟩]

def e_record_E2_r8_U3_factors : List (Polynomial × Nat) :=
  [([⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩], 1), ([⟨0, 0, ⟨1, 1⟩⟩, ⟨0, 1, ⟨1, 1⟩⟩], 1), ([⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩, ⟨1, 1, ⟨1, 1⟩⟩], 4), ([⟨0, 0, ⟨1, 9⟩⟩, ⟨0, 1, ⟨4, 3⟩⟩, ⟨0, 2, ⟨1, 1⟩⟩], 1)]

noncomputable def e_record_E2_r8_U3 (lam x : ℝ) : ℝ :=
  matrixValue numerator_E2_r8_U3 lam x / polynomialValue e_record_E2_r8_U3_denominator lam x

theorem e_record_E2_r8_U3_denominator_value (lam x : ℝ) :
    polynomialValue e_record_E2_r8_U3_denominator lam x = (373311845848188985540608000000000000000000000000000 : ℝ)*(lam+1)^1*(x+1)^1*(lam*x+lam+1)^4*(x^2+4*x/3+1/9)^1 := by
  rw [factorCheck_sound e_record_E2_r8_U3_denominator ⟨373311845848188985540608000000000000000000000000000, 1⟩ e_record_E2_r8_U3_factors lam x (by norm_num)
    (by norm_num [e_record_E2_r8_U3_factors, validPolynomial]) cert_0463_E2_r8_U3_allowed_denominator_factors]
  have hf0 : polynomialValue [⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩] lam x = (lam+1) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  have hf1 : polynomialValue [⟨0, 0, ⟨1, 1⟩⟩, ⟨0, 1, ⟨1, 1⟩⟩] lam x = (x+1) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  have hf2 : polynomialValue [⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩, ⟨1, 1, ⟨1, 1⟩⟩] lam x = (lam*x+lam+1) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  have hf3 : polynomialValue [⟨0, 0, ⟨1, 9⟩⟩, ⟨0, 1, ⟨4, 3⟩⟩, ⟨0, 2, ⟨1, 1⟩⟩] lam x = (x^2+4*x/3+1/9) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  simp only [e_record_E2_r8_U3_factors, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    hf0, hf1, hf2, hf3, mul_one]
  norm_num only [fractionValue, Int.cast_ofNat, Nat.cast_one, div_one]
  ac_rfl


theorem e_record_E2_r8_U3_denominator_positive (lam x : ℝ) (hlam : 0 ≤ lam) (hx : 0 ≤ x) :
    0 < polynomialValue e_record_E2_r8_U3_denominator lam x := by
  rw [e_record_E2_r8_U3_denominator_value]
  positivity

theorem e_record_E2_r8_U3_positive (lam x : ℝ)
    (hlam : (29/20 : ℝ) ≤ lam ∧ lam ≤ 8/5)
    (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) : 0 < e_record_E2_r8_U3 lam x := by
  apply div_pos ((e_common_E2_r8_U3_numerator_rectangle_positive lam x hlam hx))
    (e_record_E2_r8_U3_denominator_positive lam x (by linarith only [hlam.1]) (by linarith only [hx.1]))

def e_record_E2_r8_D_denominator : Polynomial :=
  [⟨0, 0, ⟨773115084800000000000, 1⟩⟩, ⟨0, 1, ⟨9277381017600000000000, 1⟩⟩, ⟨0, 2, ⟨6958035763200000000000, 1⟩⟩, ⟨1, 0, ⟨1546230169600000000000, 1⟩⟩, ⟨1, 1, ⟨20100992204800000000000, 1⟩⟩, ⟨1, 2, ⟨32470833561600000000000, 1⟩⟩, ⟨1, 3, ⟨13916071526400000000000, 1⟩⟩, ⟨2, 0, ⟨773115084800000000000, 1⟩⟩, ⟨2, 1, ⟨10823611187200000000000, 1⟩⟩, ⟨2, 2, ⟨26285912883200000000000, 1⟩⟩, ⟨2, 3, ⟨23193452544000000000000, 1⟩⟩, ⟨2, 4, ⟨6958035763200000000000, 1⟩⟩]

def e_record_E2_r8_D_factors : List (Polynomial × Nat) :=
  [([⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩, ⟨1, 1, ⟨1, 1⟩⟩], 2), ([⟨0, 0, ⟨1, 9⟩⟩, ⟨0, 1, ⟨4, 3⟩⟩, ⟨0, 2, ⟨1, 1⟩⟩], 1)]

noncomputable def e_record_E2_r8_D (lam x : ℝ) : ℝ :=
  matrixValue numerator_E2_r8_D lam x / polynomialValue e_record_E2_r8_D_denominator lam x

theorem e_record_E2_r8_D_denominator_value (lam x : ℝ) :
    polynomialValue e_record_E2_r8_D_denominator lam x = (6958035763200000000000 : ℝ)*(lam*x+lam+1)^2*(x^2+4*x/3+1/9)^1 := by
  rw [factorCheck_sound e_record_E2_r8_D_denominator ⟨6958035763200000000000, 1⟩ e_record_E2_r8_D_factors lam x (by norm_num)
    (by norm_num [e_record_E2_r8_D_factors, validPolynomial]) cert_0475_E2_r8_D_allowed_denominator_factors]
  have hf0 : polynomialValue [⟨0, 0, ⟨1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩, ⟨1, 1, ⟨1, 1⟩⟩] lam x = (lam*x+lam+1) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  have hf1 : polynomialValue [⟨0, 0, ⟨1, 9⟩⟩, ⟨0, 1, ⟨4, 3⟩⟩, ⟨0, 2, ⟨1, 1⟩⟩] lam x = (x^2+4*x/3+1/9) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  simp only [e_record_E2_r8_D_factors, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    hf0, hf1, mul_one]
  norm_num only [fractionValue, Int.cast_ofNat, Nat.cast_one, div_one]
  ac_rfl


theorem e_record_E2_r8_D_denominator_positive (lam x : ℝ) (hlam : 0 ≤ lam) (hx : 0 ≤ x) :
    0 < polynomialValue e_record_E2_r8_D_denominator lam x := by
  rw [e_record_E2_r8_D_denominator_value]
  positivity

theorem e_record_E2_r8_D_positive (lam x : ℝ)
    (hlam : (29/20 : ℝ) ≤ lam ∧ lam ≤ 8/5)
    (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) : 0 < e_record_E2_r8_D lam x := by
  apply div_pos ((e_common_E2_r8_D_numerator_rectangle_positive lam x hlam hx))
    (e_record_E2_r8_D_denominator_positive lam x (by linarith only [hlam.1]) (by linarith only [hx.1]))

end F4Heavy.Analysis
