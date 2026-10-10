module

public import F4Heavy.Analysis.DHOrdinary43
public import F4Heavy.Analysis.HFactorSigns
public import F4Heavy.Finite.Factorizations.Check1116

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Heavy.Finite

def dh_record_H_r6_endpoint_D_denominator : Polynomial :=
  [⟨0, 0, ⟨133982846976000000000000, 1⟩⟩, ⟨0, 1, ⟨389768282112000000000000, 1⟩⟩, ⟨0, 2, ⟨418557984768000000000000, 1⟩⟩, ⟨0, 3, ⟨197300060160000000000000, 1⟩⟩, ⟨0, 4, ⟨34527510528000000000000, 1⟩⟩, ⟨1, 0, ⟨-158343364608000000000000, 1⟩⟩, ⟨1, 1, ⟨-274609471488000000000000, 1⟩⟩, ⟨1, 2, ⟨-71873593344000000000000, 1⟩⟩, ⟨1, 3, ⟨78920024064000000000000, 1⟩⟩, ⟨1, 4, ⟨34527510528000000000000, 1⟩⟩, ⟨2, 0, ⟨-55364812800000000000000, 1⟩⟩, ⟨2, 1, ⟨-431644213248000000000000, 1⟩⟩, ⟨2, 2, ⟨-701824499712000000000000, 1⟩⟩, ⟨2, 3, ⟨-394600120320000000000000, 1⟩⟩, ⟨2, 4, ⟨-69055021056000000000000, 1⟩⟩, ⟨3, 0, ⟨52546240512000000000000, 1⟩⟩, ⟨3, 1, ⟨149786984448000000000000, 1⟩⟩, ⟨3, 2, ⟨8455716864000000000000, 1⟩⟩, ⟨3, 3, ⟨-157840048128000000000000, 1⟩⟩, ⟨3, 4, ⟨-69055021056000000000000, 1⟩⟩, ⟨4, 0, ⟨24461180928000000000000, 1⟩⟩, ⟨4, 1, ⟨144955146240000000000000, 1⟩⟩, ⟨4, 2, ⟨283266514944000000000000, 1⟩⟩, ⟨4, 3, ⟨197300060160000000000000, 1⟩⟩, ⟨4, 4, ⟨34527510528000000000000, 1⟩⟩, ⟨5, 0, ⟨2717908992000000000000, 1⟩⟩, ⟨5, 1, ⟨21743271936000000000000, 1⟩⟩, ⟨5, 2, ⟨63417876480000000000000, 1⟩⟩, ⟨5, 3, ⟨78920024064000000000000, 1⟩⟩, ⟨5, 4, ⟨34527510528000000000000, 1⟩⟩]

def dh_record_H_r6_endpoint_D_factors : List (Polynomial × Nat) :=
  [([⟨0, 0, ⟨-1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩], 2), ([⟨0, 0, ⟨1, 1⟩⟩, ⟨0, 1, ⟨1, 1⟩⟩], 1), ([⟨0, 0, ⟨11, 7⟩⟩, ⟨0, 1, ⟨1, 1⟩⟩, ⟨1, 0, ⟨3, 7⟩⟩, ⟨1, 1, ⟨1, 1⟩⟩], 3)]

noncomputable def dh_record_H_r6_endpoint_D (v x : ℝ) : ℝ :=
  matrixValue numerator_H_r6_endpoint_D v x/polynomialValue dh_record_H_r6_endpoint_D_denominator v x

theorem dh_record_H_r6_endpoint_D_denominator_value (v x : ℝ) :
    polynomialValue dh_record_H_r6_endpoint_D_denominator v x = (34527510528000000000000/1 : ℝ)*(v-1)^2*(x+1)^1*(v*x+3*v/7+x+11/7)^3 := by
  rw [factorCheck_sound dh_record_H_r6_endpoint_D_denominator ⟨34527510528000000000000, 1⟩ dh_record_H_r6_endpoint_D_factors v x (by norm_num)
    (by norm_num [dh_record_H_r6_endpoint_D_factors, validPolynomial]) cert_1116_H_r6_endpoint_D_allowed_denominator_factors]
  have hf0 : polynomialValue [⟨0, 0, ⟨-1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩] v x = (v-1) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  have hf1 : polynomialValue [⟨0, 0, ⟨1, 1⟩⟩, ⟨0, 1, ⟨1, 1⟩⟩] v x = (x+1) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  have hf2 : polynomialValue [⟨0, 0, ⟨11, 7⟩⟩, ⟨0, 1, ⟨1, 1⟩⟩, ⟨1, 0, ⟨3, 7⟩⟩, ⟨1, 1, ⟨1, 1⟩⟩] v x = (v*x+3*v/7+x+11/7) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  simp only [dh_record_H_r6_endpoint_D_factors, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    hf0, hf1, hf2, mul_one]
  norm_num only [fractionValue, Int.cast_ofNat, Nat.cast_one, div_one]
  ac_rfl

theorem dh_record_H_r6_endpoint_D_denominator_positive (v x : ℝ)
    (hv : 0 ≤ v ∧ v ≤ (1/7 : ℝ)) (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < polynomialValue dh_record_H_r6_endpoint_D_denominator v x := by
  rw [dh_record_H_r6_endpoint_D_denominator_value]
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := h_denominator_factor_signs v x hv hx
  have hn1 : v-1 = -(1-v) := by ring
  have hn5 : v^2*x-9*v^2/28-33*v/14-x-121/28 = -((1-v^2)*x+(3*v+11)^2/28) := by ring
  have he : (34527510528000000000000/1 : ℝ)*(v-1)^2*(x+1)^1*(v*x+3*v/7+x+11/7)^3 = (34527510528000000000000/1 : ℝ)*(1-v)^2*(x+1)^1*(v*x+3*v/7+x+11/7)^3 := by
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

theorem dh_record_H_r6_endpoint_D_positive (v x : ℝ)
    (hv : 0 ≤ v ∧ v ≤ (1/7 : ℝ)) (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < dh_record_H_r6_endpoint_D v x := by
  exact div_pos (dh_ordinary_H_r6_endpoint_D_rectangle_positive v x (by simpa using hv) hx)
    (dh_record_H_r6_endpoint_D_denominator_positive v x hv hx)

end F4Heavy.Analysis
