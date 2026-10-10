module

public import F4Heavy.Analysis.DHOrdinary42
public import F4Heavy.Analysis.HFactorSigns
public import F4Heavy.Finite.Factorizations.Check1109

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Heavy.Finite

def dh_record_H_r6_endpoint_C_denominator : Polynomial :=
  [⟨0, 0, ⟨6754968535040, 1⟩⟩, ⟨0, 1, ⟨14458982236160, 1⟩⟩, ⟨0, 2, ⟨11190612787200, 1⟩⟩, ⟨0, 3, ⟨3639775068160, 1⟩⟩, ⟨0, 4, ⟨402820956160, 1⟩⟩, ⟨1, 0, ⟨2456352194560, 1⟩⟩, ⟨1, 1, ⟨13783992893440, 1⟩⟩, ⟨1, 2, ⟨16548542545920, 1⟩⟩, ⟨1, 3, ⟨6847956254720, 1⟩⟩, ⟨1, 4, ⟨805641912320, 1⟩⟩, ⟨2, 0, ⟨-4186963968000, 1⟩⟩, ⟨2, 1, ⟨-9633938800640, 1⟩⟩, ⟨2, 2, ⟨-5407254773760, 1⟩⟩, ⟨2, 3, ⟨-1251622256640, 1⟩⟩, ⟨2, 4, ⟨-402820956160, 1⟩⟩, ⟨3, 0, ⟨-3654077644800, 1⟩⟩, ⟨3, 1, ⟨-13054687313920, 1⟩⟩, ⟨3, 2, ⟨-16178604933120, 1⟩⟩, ⟨3, 3, ⟨-8056419123200, 1⟩⟩, ⟨3, 4, ⟨-1611283824640, 1⟩⟩, ⟨4, 0, ⟨-1183422873600, 1⟩⟩, ⟨4, 1, ⟨-4785407262720, 1⟩⟩, ⟨4, 2, ⟨-5838848655360, 1⟩⟩, ⟨4, 3, ⟨-2776587304960, 1⟩⟩, ⟨4, 4, ⟨-402820956160, 1⟩⟩, ⟨5, 0, ⟨-176664084480, 1⟩⟩, ⟨5, 1, ⟨-729305579520, 1⟩⟩, ⟨5, 2, ⟨-369937612800, 1⟩⟩, ⟨5, 3, ⟨1208462868480, 1⟩⟩, ⟨5, 4, ⟨805641912320, 1⟩⟩, ⟨6, 0, ⟨-10192158720, 1⟩⟩, ⟨6, 1, ⟨-39636172800, 1⟩⟩, ⟨6, 2, ⟨55490641920, 1⟩⟩, ⟨6, 3, ⟨388434493440, 1⟩⟩, ⟨6, 4, ⟨402820956160, 1⟩⟩]

def dh_record_H_r6_endpoint_C_factors : List (Polynomial × Nat) :=
  [([⟨0, 0, ⟨-1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩], 1), ([⟨0, 0, ⟨11, 7⟩⟩, ⟨0, 1, ⟨1, 1⟩⟩, ⟨1, 0, ⟨3, 7⟩⟩, ⟨1, 1, ⟨1, 1⟩⟩], 3), ([⟨0, 0, ⟨-121, 28⟩⟩, ⟨0, 1, ⟨-1, 1⟩⟩, ⟨1, 0, ⟨-33, 14⟩⟩, ⟨2, 0, ⟨-9, 28⟩⟩, ⟨2, 1, ⟨1, 1⟩⟩], 1)]

noncomputable def dh_record_H_r6_endpoint_C (v x : ℝ) : ℝ :=
  matrixValue numerator_H_r6_endpoint_C v x/polynomialValue dh_record_H_r6_endpoint_C_denominator v x

theorem dh_record_H_r6_endpoint_C_denominator_value (v x : ℝ) :
    polynomialValue dh_record_H_r6_endpoint_C_denominator v x = (402820956160/1 : ℝ)*(v-1)^1*(v*x+3*v/7+x+11/7)^3*(v^2*x-9*v^2/28-33*v/14-x-121/28)^1 := by
  rw [factorCheck_sound dh_record_H_r6_endpoint_C_denominator ⟨402820956160, 1⟩ dh_record_H_r6_endpoint_C_factors v x (by norm_num)
    (by norm_num [dh_record_H_r6_endpoint_C_factors, validPolynomial]) cert_1109_H_r6_endpoint_C_allowed_denominator_factors]
  have hf0 : polynomialValue [⟨0, 0, ⟨-1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩] v x = (v-1) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  have hf1 : polynomialValue [⟨0, 0, ⟨11, 7⟩⟩, ⟨0, 1, ⟨1, 1⟩⟩, ⟨1, 0, ⟨3, 7⟩⟩, ⟨1, 1, ⟨1, 1⟩⟩] v x = (v*x+3*v/7+x+11/7) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  have hf2 : polynomialValue [⟨0, 0, ⟨-121, 28⟩⟩, ⟨0, 1, ⟨-1, 1⟩⟩, ⟨1, 0, ⟨-33, 14⟩⟩, ⟨2, 0, ⟨-9, 28⟩⟩, ⟨2, 1, ⟨1, 1⟩⟩] v x = (v^2*x-9*v^2/28-33*v/14-x-121/28) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  simp only [dh_record_H_r6_endpoint_C_factors, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    hf0, hf1, hf2, mul_one]
  norm_num only [fractionValue, Int.cast_ofNat, Nat.cast_one, div_one]
  ac_rfl

theorem dh_record_H_r6_endpoint_C_denominator_positive (v x : ℝ)
    (hv : 0 ≤ v ∧ v ≤ (1/7 : ℝ)) (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < polynomialValue dh_record_H_r6_endpoint_C_denominator v x := by
  rw [dh_record_H_r6_endpoint_C_denominator_value]
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := h_denominator_factor_signs v x hv hx
  have hn1 : v-1 = -(1-v) := by ring
  have hn5 : v^2*x-9*v^2/28-33*v/14-x-121/28 = -((1-v^2)*x+(3*v+11)^2/28) := by ring
  have he : (402820956160/1 : ℝ)*(v-1)^1*(v*x+3*v/7+x+11/7)^3*(v^2*x-9*v^2/28-33*v/14-x-121/28)^1 = (402820956160/1 : ℝ)*(1-v)^1*(v*x+3*v/7+x+11/7)^3*((1-v^2)*x+(3*v+11)^2/28)^1 := by
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

theorem dh_record_H_r6_endpoint_C_positive (v x : ℝ)
    (hv : 0 ≤ v ∧ v ≤ (1/7 : ℝ)) (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < dh_record_H_r6_endpoint_C v x := by
  exact div_pos (dh_ordinary_H_r6_endpoint_C_rectangle_positive v x (by simpa using hv) hx)
    (dh_record_H_r6_endpoint_C_denominator_positive v x hv hx)

end F4Heavy.Analysis
