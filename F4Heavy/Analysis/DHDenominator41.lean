module

public import F4Heavy.Analysis.DHOrdinary41
public import F4Heavy.Analysis.HFactorSigns
public import F4Heavy.Finite.Factorizations.Check1100

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Heavy.Finite

def dh_record_H_r6_endpoint_R_denominator : Polynomial :=
  [⟨0, 0, ⟨1183470487339008000000000000, 1⟩⟩, ⟨0, 1, ⟨16734859535843328000000000000, 1⟩⟩, ⟨0, 2, ⟨43010393999671296000000000000, 1⟩⟩, ⟨0, 3, ⟨46963756105728000000000000000, 1⟩⟩, ⟨0, 4, ⟨25368195577675776000000000000, 1⟩⟩, ⟨0, 5, ⟨6586088105705472000000000000, 1⟩⟩, ⟨0, 6, ⟨635168083673088000000000000, 1⟩⟩, ⟨1, 0, ⟨-753117582852096000000000000, 1⟩⟩, ⟨1, 1, ⟨-9155669127069696000000000000, 1⟩⟩, ⟨1, 2, ⟨-7258446546075648000000000000, 1⟩⟩, ⟨1, 3, ⟨10762261673017344000000000000, 1⟩⟩, ⟨1, 4, ⟨15263838001692672000000000000, 1⟩⟩, ⟨1, 5, ⟨5905550873198592000000000000, 1⟩⟩, ⟨1, 6, ⟨635168083673088000000000000, 1⟩⟩, ⟨2, 0, ⟨-1163908991680512000000000000, 1⟩⟩, ⟨2, 1, ⟨-18069729532968960000000000000, 1⟩⟩, ⟨2, 2, ⟨-63555696209166336000000000000, 1⟩⟩, ⟨2, 3, ⟨-84504309135310848000000000000, 1⟩⟩, ⟨2, 4, ⟨-51860177770512384000000000000, 1⟩⟩, ⟨2, 5, ⟨-15312087731404800000000000000, 1⟩⟩, ⟨2, 6, ⟨-1905504251019264000000000000, 1⟩⟩, ⟨3, 0, ⟨93361683824640000000000000, 1⟩⟩, ⟨3, 1, ⟨521025066369024000000000000, 1⟩⟩, ⟨3, 2, ⟨-8238667067817984000000000000, 1⟩⟩, ⟨3, 3, ⟨-29231723241799680000000000000, 1⟩⟩, ⟨3, 4, ⟨-31502392558092288000000000000, 1⟩⟩, ⟨3, 5, ⟨-13270476033884160000000000000, 1⟩⟩, ⟨3, 6, ⟨-1905504251019264000000000000, 1⟩⟩, ⟨4, 0, ⟨432858715914240000000000000, 1⟩⟩, ⟨4, 1, ⟨6643082455941120000000000000, 1⟩⟩, ⟨4, 2, ⟨23092588122734592000000000000, 1⟩⟩, ⟨4, 3, ⟨35702330917650432000000000000, 1⟩⟩, ⟨4, 4, ⟨27615768807997440000000000000, 1⟩⟩, ⟨4, 5, ⟨10865911145693184000000000000, 1⟩⟩, ⟨4, 6, ⟨1905504251019264000000000000, 1⟩⟩, ⟨5, 0, ⟨176384139853824000000000000, 1⟩⟩, ⟨5, 1, ⟨2827238693142528000000000000, 1⟩⟩, ⟨5, 2, ⟨11073158652100608000000000000, 1⟩⟩, ⟨5, 3, ⟨18591680500334592000000000000, 1⟩⟩, ⟨5, 4, ⟨17213271111106560000000000000, 1⟩⟩, ⟨5, 5, ⟨8824299448172544000000000000, 1⟩⟩, ⟨5, 6, ⟨1905504251019264000000000000, 1⟩⟩, ⟨6, 0, ⟨29165881393152000000000000, 1⟩⟩, ⟨6, 1, ⟨470820656775168000000000000, 1⟩⟩, ⟨6, 2, ⟨1786988923453440000000000000, 1⟩⟩, ⟨6, 3, ⟨1838222111932416000000000000, 1⟩⟩, ⟨6, 4, ⟨-1123786615160832000000000000, 1⟩⟩, ⟨6, 5, ⟨-2139911519993856000000000000, 1⟩⟩, ⟨6, 6, ⟨-635168083673088000000000000, 1⟩⟩, ⟨7, 0, ⟨1785666207744000000000000, 1⟩⟩, ⟨7, 1, ⟨28372251967488000000000000, 1⟩⟩, ⟨7, 2, ⟨89680125100032000000000000, 1⟩⟩, ⟨7, 3, ⟨-122218931552256000000000000, 1⟩⟩, ⟨7, 4, ⟨-974716554706944000000000000, 1⟩⟩, ⟨7, 5, ⟨-1459374287486976000000000000, 1⟩⟩, ⟨7, 6, ⟨-635168083673088000000000000, 1⟩⟩]

def dh_record_H_r6_endpoint_R_factors : List (Polynomial × Nat) :=
  [([⟨0, 0, ⟨-1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩], 2), ([⟨0, 0, ⟨11, 7⟩⟩, ⟨0, 1, ⟨1, 1⟩⟩, ⟨1, 0, ⟨3, 7⟩⟩, ⟨1, 1, ⟨1, 1⟩⟩], 3), ([⟨0, 0, ⟨-121, 28⟩⟩, ⟨0, 1, ⟨-1, 1⟩⟩, ⟨1, 0, ⟨-33, 14⟩⟩, ⟨2, 0, ⟨-9, 28⟩⟩, ⟨2, 1, ⟨1, 1⟩⟩], 1), ([⟨0, 0, ⟨1, 9⟩⟩, ⟨0, 1, ⟨4, 3⟩⟩, ⟨0, 2, ⟨1, 1⟩⟩], 1)]

noncomputable def dh_record_H_r6_endpoint_R (v x : ℝ) : ℝ :=
  matrixValue numerator_H_r6_endpoint_R v x/polynomialValue dh_record_H_r6_endpoint_R_denominator v x

theorem dh_record_H_r6_endpoint_R_denominator_value (v x : ℝ) :
    polynomialValue dh_record_H_r6_endpoint_R_denominator v x = (-635168083673088000000000000/1 : ℝ)*(v-1)^2*(v*x+3*v/7+x+11/7)^3*(v^2*x-9*v^2/28-33*v/14-x-121/28)^1*(x^2+4*x/3+1/9)^1 := by
  rw [factorCheck_sound dh_record_H_r6_endpoint_R_denominator ⟨-635168083673088000000000000, 1⟩ dh_record_H_r6_endpoint_R_factors v x (by norm_num)
    (by norm_num [dh_record_H_r6_endpoint_R_factors, validPolynomial]) cert_1100_H_r6_endpoint_R_allowed_denominator_factors]
  have hf0 : polynomialValue [⟨0, 0, ⟨-1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩] v x = (v-1) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  have hf1 : polynomialValue [⟨0, 0, ⟨11, 7⟩⟩, ⟨0, 1, ⟨1, 1⟩⟩, ⟨1, 0, ⟨3, 7⟩⟩, ⟨1, 1, ⟨1, 1⟩⟩] v x = (v*x+3*v/7+x+11/7) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  have hf2 : polynomialValue [⟨0, 0, ⟨-121, 28⟩⟩, ⟨0, 1, ⟨-1, 1⟩⟩, ⟨1, 0, ⟨-33, 14⟩⟩, ⟨2, 0, ⟨-9, 28⟩⟩, ⟨2, 1, ⟨1, 1⟩⟩] v x = (v^2*x-9*v^2/28-33*v/14-x-121/28) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  have hf3 : polynomialValue [⟨0, 0, ⟨1, 9⟩⟩, ⟨0, 1, ⟨4, 3⟩⟩, ⟨0, 2, ⟨1, 1⟩⟩] v x = (x^2+4*x/3+1/9) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  simp only [dh_record_H_r6_endpoint_R_factors, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    hf0, hf1, hf2, hf3, mul_one]
  norm_num only [fractionValue, Int.cast_ofNat, Nat.cast_one, div_one]
  ac_rfl

theorem dh_record_H_r6_endpoint_R_denominator_positive (v x : ℝ)
    (hv : 0 ≤ v ∧ v ≤ (1/7 : ℝ)) (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < polynomialValue dh_record_H_r6_endpoint_R_denominator v x := by
  rw [dh_record_H_r6_endpoint_R_denominator_value]
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := h_denominator_factor_signs v x hv hx
  have hn1 : v-1 = -(1-v) := by ring
  have hn5 : v^2*x-9*v^2/28-33*v/14-x-121/28 = -((1-v^2)*x+(3*v+11)^2/28) := by ring
  have he : (-635168083673088000000000000/1 : ℝ)*(v-1)^2*(v*x+3*v/7+x+11/7)^3*(v^2*x-9*v^2/28-33*v/14-x-121/28)^1*(x^2+4*x/3+1/9)^1 = (635168083673088000000000000/1 : ℝ)*(1-v)^2*(v*x+3*v/7+x+11/7)^3*((1-v^2)*x+(3*v+11)^2/28)^1*(x^2+4*x/3+1/9)^1 := by
    simp only [hn1, hn5]
    generalize v+1 = A
    generalize 1-v = q
    generalize v+11/3 = C
    generalize x+1 = T
    generalize v*x+3*v/7+x+11/7 = B
    generalize ((1-v^2)*x+(3*v+11)^2/28) = S
    generalize x^2+4*x/3+1/9 = E
    ring
  rw [he]
  positivity

theorem dh_record_H_r6_endpoint_R_positive (v x : ℝ)
    (hv : 0 ≤ v ∧ v ≤ (1/7 : ℝ)) (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < dh_record_H_r6_endpoint_R v x := by
  exact div_pos (dh_ordinary_H_r6_endpoint_R_rectangle_positive v x (by simpa using hv) hx)
    (dh_record_H_r6_endpoint_R_denominator_positive v x hv hx)

end F4Heavy.Analysis
