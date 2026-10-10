module

public import F4Heavy.Analysis.DHSpecial12
public import F4Heavy.Analysis.DHFactorSigns
public import F4Heavy.Finite.Factorizations.Check0194

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Heavy.Finite

def dh_record_D_r6_endpoint_R_denominator : Polynomial :=
  [⟨0, 0, ⟨2779780066836480000000000000, 1⟩⟩, ⟨0, 1, ⟨37750099673088000000000000000, 1⟩⟩, ⟨0, 2, ⟨80293318062243840000000000000, 1⟩⟩, ⟨0, 3, ⟨70934598065848320000000000000, 1⟩⟩, ⟨0, 4, ⟨30931449670533120000000000000, 1⟩⟩, ⟨0, 5, ⟨6580069749227520000000000000, 1⟩⟩, ⟨0, 6, ⟨542313440870400000000000000, 1⟩⟩, ⟨1, 0, ⟨-7103882393026560000000000000, 1⟩⟩, ⟨1, 1, ⟨-92201758595481600000000000000, 1⟩⟩, ⟨1, 2, ⟨-149064593917870080000000000000, 1⟩⟩, ⟨1, 3, ⟨-82463277963018240000000000000, 1⟩⟩, ⟨1, 4, ⟨-13212864416317440000000000000, 1⟩⟩, ⟨1, 5, ⟨2024636845916160000000000000, 1⟩⟩, ⟨1, 6, ⟨542313440870400000000000000, 1⟩⟩, ⟨2, 0, ⟨6211607309844480000000000000, 1⟩⟩, ⟨2, 1, ⟨73237735460044800000000000000, 1⟩⟩, ⟨2, 2, ⟨35436652674416640000000000000, 1⟩⟩, ⟨2, 3, ⟨-71663708358574080000000000000, 1⟩⟩, ⟨2, 4, ⟨-64937515265556480000000000000, 1⟩⟩, ⟨2, 5, ⟨-18004806236897280000000000000, 1⟩⟩, ⟨2, 6, ⟨-1626940322611200000000000000, 1⟩⟩, ⟨3, 0, ⟨-2268819121766400000000000000, 1⟩⟩, ⟨3, 1, ⟨-20846114399846400000000000000, 1⟩⟩, ⟨3, 2, ⟨59458878465638400000000000000, 1⟩⟩, ⟨3, 3, ⟨97036445260185600000000000000, 1⟩⟩, ⟨3, 4, ⟨26821918929715200000000000000, 1⟩⟩, ⟨3, 5, ⟨-4338507526963200000000000000, 1⟩⟩, ⟨3, 6, ⟨-1626940322611200000000000000, 1⟩⟩, ⟨4, 0, ⟨421563963801600000000000000, 1⟩⟩, ⟨4, 1, ⟨2015786591846400000000000000, 1⟩⟩, ⟨4, 2, ⟨-30710617001164800000000000000, 1⟩⟩, ⟨4, 3, ⟨-1687197371596800000000000000, 1⟩⟩, ⟨4, 4, ⟨37080681519513600000000000000, 1⟩⟩, ⟨4, 5, ⟨16269403226112000000000000000, 1⟩⟩, ⟨4, 6, ⟨1626940322611200000000000000, 1⟩⟩, ⟨5, 0, ⟨-42415313387520000000000000, 1⟩⟩, ⟨5, 1, ⟨64964630937600000000000000, 1⟩⟩, ⟨5, 2, ⟨4865144719933440000000000000, 1⟩⟩, ⟨5, 3, ⟨-14472236740116480000000000000, 1⟩⟩, ⟨5, 4, ⟨-14005244610478080000000000000, 1⟩⟩, ⟨5, 5, ⟨2603104516177920000000000000, 1⟩⟩, ⟨5, 6, ⟨1626940322611200000000000000, 1⟩⟩, ⟨6, 0, ⟨2212563517440000000000000, 1⟩⟩, ⟨6, 1, ⟨-21654876979200000000000000, 1⟩⟩, ⟨6, 2, ⟨-282878599495680000000000000, 1⟩⟩, ⟨6, 3, ⟨2416307664322560000000000000, 1⟩⟩, ⟨6, 4, ⟨-3074615924490240000000000000, 1⟩⟩, ⟨6, 5, ⟨-4844666738442240000000000000, 1⟩⟩, ⟨6, 6, ⟨-542313440870400000000000000, 1⟩⟩, ⟨7, 0, ⟨-47075819520000000000000, 1⟩⟩, ⟨7, 1, ⟨941516390400000000000000, 1⟩⟩, ⟨7, 2, ⟨4095596298240000000000000, 1⟩⟩, ⟨7, 3, ⟨-100930557050880000000000000, 1⟩⟩, ⟨7, 4, ⟨396190097080320000000000000, 1⟩⟩, ⟨7, 5, ⟨-289233835130880000000000000, 1⟩⟩, ⟨7, 6, ⟨-542313440870400000000000000, 1⟩⟩]

def dh_record_D_r6_endpoint_R_factors : List (Polynomial × Nat) :=
  [([⟨0, 0, ⟨-1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩], 2), ([⟨0, 0, ⟨9, 4⟩⟩, ⟨0, 1, ⟨1, 1⟩⟩, ⟨1, 0, ⟨-1, 4⟩⟩, ⟨1, 1, ⟨1, 1⟩⟩], 3), ([⟨0, 0, ⟨-81, 20⟩⟩, ⟨0, 1, ⟨-1, 1⟩⟩, ⟨1, 0, ⟨9, 10⟩⟩, ⟨2, 0, ⟨-1, 20⟩⟩, ⟨2, 1, ⟨1, 1⟩⟩], 1), ([⟨0, 0, ⟨1, 9⟩⟩, ⟨0, 1, ⟨4, 3⟩⟩, ⟨0, 2, ⟨1, 1⟩⟩], 1)]

noncomputable def dh_record_D_r6_endpoint_R (v x : ℝ) : ℝ :=
  matrixValue numerator_D_r6_endpoint_R v x/polynomialValue dh_record_D_r6_endpoint_R_denominator v x

theorem dh_record_D_r6_endpoint_R_denominator_value (v x : ℝ) :
    polynomialValue dh_record_D_r6_endpoint_R_denominator v x = (-542313440870400000000000000/1 : ℝ)*(v-1)^2*(v*x-v/4+x+9/4)^3*(v^2*x-v^2/20+9*v/10-x-81/20)^1*(x^2+4*x/3+1/9)^1 := by
  rw [factorCheck_sound dh_record_D_r6_endpoint_R_denominator ⟨-542313440870400000000000000, 1⟩ dh_record_D_r6_endpoint_R_factors v x (by norm_num)
    (by norm_num [dh_record_D_r6_endpoint_R_factors, validPolynomial]) cert_0194_D_r6_endpoint_R_allowed_denominator_factors]
  have hf0 : polynomialValue [⟨0, 0, ⟨-1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩] v x = (v-1) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  have hf1 : polynomialValue [⟨0, 0, ⟨9, 4⟩⟩, ⟨0, 1, ⟨1, 1⟩⟩, ⟨1, 0, ⟨-1, 4⟩⟩, ⟨1, 1, ⟨1, 1⟩⟩] v x = (v*x-v/4+x+9/4) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  have hf2 : polynomialValue [⟨0, 0, ⟨-81, 20⟩⟩, ⟨0, 1, ⟨-1, 1⟩⟩, ⟨1, 0, ⟨9, 10⟩⟩, ⟨2, 0, ⟨-1, 20⟩⟩, ⟨2, 1, ⟨1, 1⟩⟩] v x = (v^2*x-v^2/20+9*v/10-x-81/20) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  have hf3 : polynomialValue [⟨0, 0, ⟨1, 9⟩⟩, ⟨0, 1, ⟨4, 3⟩⟩, ⟨0, 2, ⟨1, 1⟩⟩] v x = (x^2+4*x/3+1/9) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  simp only [dh_record_D_r6_endpoint_R_factors, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    hf0, hf1, hf2, hf3, mul_one]
  norm_num only [fractionValue, Int.cast_ofNat, Nat.cast_one, div_one]
  ac_rfl


theorem dh_record_D_r6_endpoint_R_denominator_positive (v x : ℝ)
    (hv : 0 ≤ v ∧ v ≤ (5/21 : ℝ)) (hx : (5/16 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < polynomialValue dh_record_D_r6_endpoint_R_denominator v x := by
  rw [dh_record_D_r6_endpoint_R_denominator_value]
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := d_denominator_factor_signs v x hv hx
  have he : (-542313440870400000000000000/1 : ℝ)*(v-1)^2*(v*x-v/4+x+9/4)^3*(v^2*x-v^2/20+9*v/10-x-81/20)^1*(x^2+4*x/3+1/9)^1 = (542313440870400000000000000/1 : ℝ)*(1-v)^2*(v*x-v/4+x+9/4)^3*((1-v^2)*x+(v-9)^2/20)^1*(x^2+4*x/3+1/9)^1 := by ring
  rw [he]
  positivity

theorem dh_record_D_r6_endpoint_R_positive (v x : ℝ)
    (hv : 0 ≤ v ∧ v ≤ (5/21 : ℝ)) (hx : (5/16 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < dh_record_D_r6_endpoint_R v x := by
  exact div_pos (dh_special_D_r6_endpoint_R_rectangle_positive v x (by simpa using hv) hx)
    (dh_record_D_r6_endpoint_R_denominator_positive v x hv hx)

end F4Heavy.Analysis
