module

public import F4Heavy.Analysis.DHOrdinary14
public import F4Heavy.Analysis.DHFactorSigns
public import F4Heavy.Finite.Factorizations.Check0265

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Heavy.Finite

def dh_record_D_r6_endpoint_D_denominator : Polynomial :=
  [⟨0, 0, ⟨57330892800000000000000, 1⟩⟩, ⟨0, 1, ⟨133772083200000000000000, 1⟩⟩, ⟨0, 2, ⟨110415052800000000000000, 1⟩⟩, ⟨0, 3, ⟨39007027200000000000000, 1⟩⟩, ⟨0, 4, ⟨5033164800000000000000, 1⟩⟩, ⟨1, 0, ⟨-133772083200000000000000, 1⟩⟩, ⟨1, 1, ⟨-227200204800000000000000, 1⟩⟩, ⟨1, 2, ⟨-97202995200000000000000, 1⟩⟩, ⟨1, 3, ⟨1258291200000000000000, 1⟩⟩, ⟨1, 4, ⟨5033164800000000000000, 1⟩⟩, ⟨2, 0, ⟨97674854400000000000000, 1⟩⟩, ⟨2, 1, ⟨39164313600000000000000, 1⟩⟩, ⟨2, 2, ⟨-126458265600000000000000, 1⟩⟩, ⟨2, 3, ⟨-78014054400000000000000, 1⟩⟩, ⟨2, 4, ⟨-10066329600000000000000, 1⟩⟩, ⟨3, 0, ⟨-23435673600000000000000, 1⟩⟩, ⟨3, 1, ⟨69048729600000000000000, 1⟩⟩, ⟨3, 2, ⟨100034150400000000000000, 1⟩⟩, ⟨3, 3, ⟨-2516582400000000000000, 1⟩⟩, ⟨3, 4, ⟨-10066329600000000000000, 1⟩⟩, ⟨4, 0, ⟨2280652800000000000000, 1⟩⟩, ⟨4, 1, ⟨-15649996800000000000000, 1⟩⟩, ⟨4, 2, ⟨16043212800000000000000, 1⟩⟩, ⟨4, 3, ⟨39007027200000000000000, 1⟩⟩, ⟨4, 4, ⟨5033164800000000000000, 1⟩⟩, ⟨5, 0, ⟨-78643200000000000000, 1⟩⟩, ⟨5, 1, ⟨865075200000000000000, 1⟩⟩, ⟨5, 2, ⟨-2831155200000000000000, 1⟩⟩, ⟨5, 3, ⟨1258291200000000000000, 1⟩⟩, ⟨5, 4, ⟨5033164800000000000000, 1⟩⟩]

def dh_record_D_r6_endpoint_D_factors : List (Polynomial × Nat) :=
  [([⟨0, 0, ⟨-1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩], 2), ([⟨0, 0, ⟨1, 1⟩⟩, ⟨0, 1, ⟨1, 1⟩⟩], 1), ([⟨0, 0, ⟨9, 4⟩⟩, ⟨0, 1, ⟨1, 1⟩⟩, ⟨1, 0, ⟨-1, 4⟩⟩, ⟨1, 1, ⟨1, 1⟩⟩], 3)]

noncomputable def dh_record_D_r6_endpoint_D (v x : ℝ) : ℝ :=
  matrixValue numerator_D_r6_endpoint_D v x/polynomialValue dh_record_D_r6_endpoint_D_denominator v x

theorem dh_record_D_r6_endpoint_D_denominator_value (v x : ℝ) :
    polynomialValue dh_record_D_r6_endpoint_D_denominator v x = (5033164800000000000000/1 : ℝ)*(v-1)^2*(x+1)^1*(v*x-v/4+x+9/4)^3 := by
  rw [factorCheck_sound dh_record_D_r6_endpoint_D_denominator ⟨5033164800000000000000, 1⟩ dh_record_D_r6_endpoint_D_factors v x (by norm_num)
    (by norm_num [dh_record_D_r6_endpoint_D_factors, validPolynomial]) cert_0265_D_r6_endpoint_D_allowed_denominator_factors]
  have hf0 : polynomialValue [⟨0, 0, ⟨-1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩] v x = (v-1) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  have hf1 : polynomialValue [⟨0, 0, ⟨1, 1⟩⟩, ⟨0, 1, ⟨1, 1⟩⟩] v x = (x+1) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  have hf2 : polynomialValue [⟨0, 0, ⟨9, 4⟩⟩, ⟨0, 1, ⟨1, 1⟩⟩, ⟨1, 0, ⟨-1, 4⟩⟩, ⟨1, 1, ⟨1, 1⟩⟩] v x = (v*x-v/4+x+9/4) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  simp only [dh_record_D_r6_endpoint_D_factors, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    hf0, hf1, hf2, mul_one]
  norm_num only [fractionValue, Int.cast_ofNat, Nat.cast_one, div_one]
  ac_rfl


theorem dh_record_D_r6_endpoint_D_denominator_positive (v x : ℝ)
    (hv : 0 ≤ v ∧ v ≤ (5/21 : ℝ)) (hx : (5/16 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < polynomialValue dh_record_D_r6_endpoint_D_denominator v x := by
  rw [dh_record_D_r6_endpoint_D_denominator_value]
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := d_denominator_factor_signs v x hv hx
  have he : (5033164800000000000000/1 : ℝ)*(v-1)^2*(x+1)^1*(v*x-v/4+x+9/4)^3 = (5033164800000000000000/1 : ℝ)*(1-v)^2*(x+1)^1*(v*x-v/4+x+9/4)^3 := by ring
  rw [he]
  positivity

theorem dh_record_D_r6_endpoint_D_positive (v x : ℝ)
    (hv : 0 ≤ v ∧ v ≤ (5/21 : ℝ)) (hx : (5/16 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < dh_record_D_r6_endpoint_D v x := by
  exact div_pos (dh_ordinary_D_r6_endpoint_D_rectangle_positive v x (by simpa using hv) hx)
    (dh_record_D_r6_endpoint_D_denominator_positive v x hv hx)

end F4Heavy.Analysis
