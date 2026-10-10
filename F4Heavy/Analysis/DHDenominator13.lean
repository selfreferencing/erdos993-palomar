module

public import F4Heavy.Analysis.DHOrdinary13
public import F4Heavy.Analysis.DHFactorSigns
public import F4Heavy.Finite.Factorizations.Check0258

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Heavy.Finite

def dh_record_D_r6_endpoint_C_denominator : Polynomial :=
  [⟨0, 0, ⟨18575209267200, 1⟩⟩, ⟨0, 1, ⟨29353417113600, 1⟩⟩, ⟨0, 2, ⟨17122826649600, 1⟩⟩, ⟨0, 3, ⟨4348654387200, 1⟩⟩, ⟨0, 4, ⟨402653184000, 1⟩⟩, ⟨1, 0, ⟨-28894769971200, 1⟩⟩, ⟨1, 1, ⟨-17122826649600, 1⟩⟩, ⟨1, 2, ⟨5979399782400, 1⟩⟩, ⟨1, 3, ⟨5315022028800, 1⟩⟩, ⟨1, 4, ⟨805306368000, 1⟩⟩, ⟨2, 0, ⟨12612796416000, 1⟩⟩, ⟨2, 1, ⟨-25820135424000, 1⟩⟩, ⟨2, 2, ⟨-26424115200000, 1⟩⟩, ⟨2, 3, ⟨-6442450944000, 1⟩⟩, ⟨2, 4, ⟨-402653184000, 1⟩⟩, ⟨3, 0, ⟨-2548039680000, 1⟩⟩, ⟨3, 1, ⟨16810770432000, 1⟩⟩, ⟨3, 2, ⟨-4227858432000, 1⟩⟩, ⟨3, 3, ⟨-8053063680000, 1⟩⟩, ⟨3, 4, ⟨-1610612736000, 1⟩⟩, ⟨4, 0, ⟨268959744000, 1⟩⟩, ⟨4, 1, ⟨-3523215360000, 1⟩⟩, ⟨4, 2, ⟨9210691584000, 1⟩⟩, ⟨4, 3, ⟨2415919104000, 1⟩⟩, ⟨4, 4, ⟨-402653184000, 1⟩⟩, ⟨5, 0, ⟨-14470348800, 1⟩⟩, ⟨5, 1, ⟨312056217600, 1⟩⟩, ⟨5, 2, ⟨-1751541350400, 1⟩⟩, ⟨5, 3, ⟨2738041651200, 1⟩⟩, ⟨5, 4, ⟨805306368000, 1⟩⟩, ⟨6, 0, ⟨314572800, 1⟩⟩, ⟨6, 1, ⟨-10066329600, 1⟩⟩, ⟨6, 2, ⟨90596966400, 1⟩⟩, ⟨6, 3, ⟨-322122547200, 1⟩⟩, ⟨6, 4, ⟨402653184000, 1⟩⟩]

def dh_record_D_r6_endpoint_C_factors : List (Polynomial × Nat) :=
  [([⟨0, 0, ⟨-1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩], 1), ([⟨0, 0, ⟨9, 4⟩⟩, ⟨0, 1, ⟨1, 1⟩⟩, ⟨1, 0, ⟨-1, 4⟩⟩, ⟨1, 1, ⟨1, 1⟩⟩], 3), ([⟨0, 0, ⟨-81, 20⟩⟩, ⟨0, 1, ⟨-1, 1⟩⟩, ⟨1, 0, ⟨9, 10⟩⟩, ⟨2, 0, ⟨-1, 20⟩⟩, ⟨2, 1, ⟨1, 1⟩⟩], 1)]

noncomputable def dh_record_D_r6_endpoint_C (v x : ℝ) : ℝ :=
  matrixValue numerator_D_r6_endpoint_C v x/polynomialValue dh_record_D_r6_endpoint_C_denominator v x

theorem dh_record_D_r6_endpoint_C_denominator_value (v x : ℝ) :
    polynomialValue dh_record_D_r6_endpoint_C_denominator v x = (402653184000/1 : ℝ)*(v-1)^1*(v*x-v/4+x+9/4)^3*(v^2*x-v^2/20+9*v/10-x-81/20)^1 := by
  rw [factorCheck_sound dh_record_D_r6_endpoint_C_denominator ⟨402653184000, 1⟩ dh_record_D_r6_endpoint_C_factors v x (by norm_num)
    (by norm_num [dh_record_D_r6_endpoint_C_factors, validPolynomial]) cert_0258_D_r6_endpoint_C_allowed_denominator_factors]
  have hf0 : polynomialValue [⟨0, 0, ⟨-1, 1⟩⟩, ⟨1, 0, ⟨1, 1⟩⟩] v x = (v-1) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  have hf1 : polynomialValue [⟨0, 0, ⟨9, 4⟩⟩, ⟨0, 1, ⟨1, 1⟩⟩, ⟨1, 0, ⟨-1, 4⟩⟩, ⟨1, 1, ⟨1, 1⟩⟩] v x = (v*x-v/4+x+9/4) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  have hf2 : polynomialValue [⟨0, 0, ⟨-81, 20⟩⟩, ⟨0, 1, ⟨-1, 1⟩⟩, ⟨1, 0, ⟨9, 10⟩⟩, ⟨2, 0, ⟨-1, 20⟩⟩, ⟨2, 1, ⟨1, 1⟩⟩] v x = (v^2*x-v^2/20+9*v/10-x-81/20) := by
    norm_num [polynomialValue, termValue, fractionValue]
    <;> ring
  simp only [dh_record_D_r6_endpoint_C_factors, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    hf0, hf1, hf2, mul_one]
  norm_num only [fractionValue, Int.cast_ofNat, Nat.cast_one, div_one]
  ac_rfl


theorem dh_record_D_r6_endpoint_C_denominator_positive (v x : ℝ)
    (hv : 0 ≤ v ∧ v ≤ (5/21 : ℝ)) (hx : (5/16 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < polynomialValue dh_record_D_r6_endpoint_C_denominator v x := by
  rw [dh_record_D_r6_endpoint_C_denominator_value]
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := d_denominator_factor_signs v x hv hx
  have he : (402653184000/1 : ℝ)*(v-1)^1*(v*x-v/4+x+9/4)^3*(v^2*x-v^2/20+9*v/10-x-81/20)^1 = (402653184000/1 : ℝ)*(1-v)^1*(v*x-v/4+x+9/4)^3*((1-v^2)*x+(v-9)^2/20)^1 := by ring
  rw [he]
  positivity

theorem dh_record_D_r6_endpoint_C_positive (v x : ℝ)
    (hv : 0 ≤ v ∧ v ≤ (5/21 : ℝ)) (hx : (5/16 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < dh_record_D_r6_endpoint_C v x := by
  exact div_pos (dh_ordinary_D_r6_endpoint_C_rectangle_positive v x (by simpa using hv) hx)
    (dh_record_D_r6_endpoint_C_denominator_positive v x hv hx)

end F4Heavy.Analysis
