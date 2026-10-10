module

public import Erdos993Lean.BCFG.NatFractionPairs

/-! Small-omega rational gates.
Every finite strict or weak comparison is an unevaluated whole Nat cross-product
proved with `decide +kernel`, then transported to Real. No CSV label is claimed. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Erdos993Lean.BCFG.Analytic

theorem tail_fraction_lt {a b c d : ℕ} (hb : 0 < b) (hd : 0 < d)
    (h : a*d < c*b) : (a : ℝ)/b < (c : ℝ)/d :=
  NatLog.value_lt_of_cross (p := (a,b)) (q := (c,d)) hb hd h

theorem tail_fraction_le {a b c d : ℕ} (hb : 0 < b) (hd : 0 < d)
    (h : a*d ≤ c*b) : (a : ℝ)/b ≤ (c : ℝ)/d := by
  apply (div_le_div_iff₀ (by exact_mod_cast hb) (by exact_mod_cast hd)).2
  exact_mod_cast h

theorem tail_fraction_pos {a b : ℕ} (hb : 0 < b) (h : 0*b < a*1) :
    (0 : ℝ) < (a : ℝ)/b := by
  simpa only [Nat.cast_zero, Nat.cast_ofNat, zero_div] using
    (tail_fraction_lt (b := 1) (by decide +kernel) hb h)

/-- A positive-denominator square-margin comparison, with no Nat subtraction. -/
theorem tail_square_gate {A a B b C c E e : ℕ}
    (ha : 0 < a) (hB : 0 < B) (hb : 0 < b) (hc : 0 < c) (he : 0 < e)
    (h : E*a*c^2*B+e*a*C^2*b < A*e*c^2*B) :
    (E : ℝ)/e+((C : ℝ)/c)^2/((B : ℝ)/b) < (A : ℝ)/a := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have hR : (E : ℝ)*a*c^2*B+e*a*C^2*b < A*e*c^2*B := by exact_mod_cast h
  have hD : (0 : ℝ) < a*e*c^2*B := by positivity
  apply (mul_lt_mul_iff_left₀ hD).mp
  convert hR using 1 <;> field_simp [haR.ne',hBR.ne',hbR.ne',hcR.ne',heR.ne'] <;> ring

theorem tail_log_two_upper_gate : (25 : ℝ)/36 < 3/4 :=
  tail_fraction_lt (by decide +kernel) (by decide +kernel)
    (by decide +kernel : (25 : ℕ)*4 < 3*36)

theorem tail_BC_p_gate : (1 : ℝ)/21 < 2/3 := by
  simpa only [Nat.cast_one, Nat.cast_ofNat] using
    (tail_fraction_lt (by decide +kernel) (by decide +kernel)
    (by decide +kernel : (1 : ℕ)*3 < 2*21))

theorem tail_FG_p_gate : (7 : ℝ)/263 < 2/3 :=
  tail_fraction_lt (by decide +kernel) (by decide +kernel)
    (by decide +kernel : (7 : ℕ)*3 < 2*263)

theorem tail_cubic_positive_gate : (0 : ℝ) < 50/81 := by
  simpa only [Nat.cast_zero, Nat.cast_ofNat, zero_div] using
    (tail_fraction_lt (by decide +kernel) (by decide +kernel)
      (by decide +kernel : (0 : ℕ)*81 < 50*1))

theorem tail_BC_response_gate : (32 : ℝ)/125 < 89/189 :=
  tail_fraction_lt (by decide +kernel) (by decide +kernel)
    (by decide +kernel : (32 : ℕ)*189 < 89*125)

def tailFGNumerator : ℕ := 157*2893-1024*140
def tailFGResponse : ℝ := 157/140-1024/2893

theorem tail_FG_numerator_guard : (1024 : ℕ)*140 ≤ 157*2893 := by decide +kernel

theorem tail_FG_response_identity :
    tailFGResponse = (tailFGNumerator : ℝ)/(140*2893) := by
  unfold tailFGResponse tailFGNumerator
  rw [Nat.cast_sub tail_FG_numerator_guard]
  push_cast
  norm_num

theorem tail_FG_response_positive_gate : 0 < tailFGResponse := by
  have h : (1024 : ℝ)/2893 < 157/140 :=
    tail_fraction_lt (by decide +kernel) (by decide +kernel)
      (by decide +kernel : (1024 : ℕ)*140 < 157*2893)
  exact sub_pos.mpr h

theorem tail_FG_response_gate : (33 : ℝ)/80 < tailFGResponse := by
  have hR : (33 : ℝ)*2893*140+1024*80*140 < 157*80*2893 := by
    exact_mod_cast (by decide +kernel :
      (33 : ℕ)*2893*140+1024*80*140 < 157*80*2893)
  have hD : (0 : ℝ) < 80*140*2893 := by
    exact_mod_cast (by decide +kernel : (0 : ℕ) < 80*140*2893)
  have hR' : (33 : ℝ)*2893*140 < 157*80*2893-1024*80*140 := by
    linarith only [hR]
  apply (mul_lt_mul_iff_left₀ hD).mp
  unfold tailFGResponse
  convert hR' using 1 <;> norm_num <;> ring

theorem tail_FG_K_gate : (4 : ℝ)/5 < 11/20+(219/280)*(4/11) := by
  have h := tail_fraction_lt
    (a := 4) (b := 5) (c := 11*280*11+219*4*20) (d := 20*280*11)
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel : (4 : ℕ)*(20*280*11) < (11*280*11+219*4*20)*5)
  convert h using 1 <;> norm_num <;> ring

theorem tail_FG_alpha_gate : (43 : ℝ)/40 ≤ 11/10 :=
  tail_fraction_le (by decide +kernel) (by decide +kernel)
    (by decide +kernel : (43 : ℕ)*10 ≤ 11*40)

theorem tail_FG_beta_gate : (8 : ℝ)/7 ≤ 23/20 :=
  tail_fraction_le (by decide +kernel) (by decide +kernel)
    (by decide +kernel : (8 : ℕ)*20 ≤ 23*7)

theorem tail_BC_square_gate : (1 : ℝ)/4+(89/189)^2/(169/375) < 397/500 := by
  simpa only [Nat.cast_one, Nat.cast_ofNat] using
    (tail_square_gate (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel :
      (1 : ℕ)*500*189^2*169+4*500*89^2*375 < 397*4*189^2*169))

theorem tail_FG_square_gate : (1 : ℝ)/2+tailFGResponse^2/(329/120) < 4/5 := by
  rw [tail_FG_response_identity]
  simpa only [Nat.cast_one, Nat.cast_ofNat, Nat.cast_mul] using
    (tail_square_gate (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel :
      (1 : ℕ)*5*(140*2893)^2*329+2*5*tailFGNumerator^2*120 <
        4*2*(140*2893)^2*329))

theorem tail_epsilon_BC_gate : (1 : ℝ)/10000 < 1/4 := by
  simpa only [Nat.cast_one, Nat.cast_ofNat] using
    (tail_fraction_lt (by decide +kernel) (by decide +kernel)
    (by decide +kernel : (1 : ℕ)*4 < 1*10000))

theorem tail_epsilon_FG_gate : (1 : ℝ)/10000 < 1/2 := by
  simpa only [Nat.cast_one, Nat.cast_ofNat] using
    (tail_fraction_lt (by decide +kernel) (by decide +kernel)
    (by decide +kernel : (1 : ℕ)*2 < 1*10000))

theorem tail_B_row_upper_gate : (39 : ℝ)/50 ≤ 4/5 :=
  tail_fraction_le (by decide +kernel) (by decide +kernel)
    (by decide +kernel : (39 : ℕ)*5 ≤ 4*50)

theorem tail_F_row_upper_gate : (33 : ℝ)/20 ≤ 7/4 :=
  tail_fraction_le (by decide +kernel) (by decide +kernel)
    (by decide +kernel : (33 : ℕ)*4 ≤ 7*20)

theorem tail_FG_center_gate : (89 : ℝ)/80 ≤ 157/140 :=
  tail_fraction_le (by decide +kernel) (by decide +kernel)
    (by decide +kernel : (89 : ℕ)*140 ≤ 157*80)

end Erdos993Lean.BCFG.Analytic

#check Erdos993Lean.BCFG.Analytic.tail_fraction_lt
#print axioms Erdos993Lean.BCFG.Analytic.tail_fraction_lt
#check Erdos993Lean.BCFG.Analytic.tail_fraction_le
#print axioms Erdos993Lean.BCFG.Analytic.tail_fraction_le
#check Erdos993Lean.BCFG.Analytic.tail_fraction_pos
#print axioms Erdos993Lean.BCFG.Analytic.tail_fraction_pos
#check Erdos993Lean.BCFG.Analytic.tail_square_gate
#print axioms Erdos993Lean.BCFG.Analytic.tail_square_gate
#check Erdos993Lean.BCFG.Analytic.tail_log_two_upper_gate
#print axioms Erdos993Lean.BCFG.Analytic.tail_log_two_upper_gate
#check Erdos993Lean.BCFG.Analytic.tail_BC_p_gate
#print axioms Erdos993Lean.BCFG.Analytic.tail_BC_p_gate
#check Erdos993Lean.BCFG.Analytic.tail_FG_p_gate
#print axioms Erdos993Lean.BCFG.Analytic.tail_FG_p_gate
#check Erdos993Lean.BCFG.Analytic.tail_cubic_positive_gate
#print axioms Erdos993Lean.BCFG.Analytic.tail_cubic_positive_gate
#check Erdos993Lean.BCFG.Analytic.tail_BC_response_gate
#print axioms Erdos993Lean.BCFG.Analytic.tail_BC_response_gate
#check Erdos993Lean.BCFG.Analytic.tailFGNumerator
#print axioms Erdos993Lean.BCFG.Analytic.tailFGNumerator
#check Erdos993Lean.BCFG.Analytic.tailFGResponse
#print axioms Erdos993Lean.BCFG.Analytic.tailFGResponse
#check Erdos993Lean.BCFG.Analytic.tail_FG_numerator_guard
#print axioms Erdos993Lean.BCFG.Analytic.tail_FG_numerator_guard
#check Erdos993Lean.BCFG.Analytic.tail_FG_response_identity
#print axioms Erdos993Lean.BCFG.Analytic.tail_FG_response_identity
#check Erdos993Lean.BCFG.Analytic.tail_FG_response_positive_gate
#print axioms Erdos993Lean.BCFG.Analytic.tail_FG_response_positive_gate
#check Erdos993Lean.BCFG.Analytic.tail_FG_response_gate
#print axioms Erdos993Lean.BCFG.Analytic.tail_FG_response_gate
#check Erdos993Lean.BCFG.Analytic.tail_FG_K_gate
#print axioms Erdos993Lean.BCFG.Analytic.tail_FG_K_gate
#check Erdos993Lean.BCFG.Analytic.tail_FG_alpha_gate
#print axioms Erdos993Lean.BCFG.Analytic.tail_FG_alpha_gate
#check Erdos993Lean.BCFG.Analytic.tail_FG_beta_gate
#print axioms Erdos993Lean.BCFG.Analytic.tail_FG_beta_gate
#check Erdos993Lean.BCFG.Analytic.tail_BC_square_gate
#print axioms Erdos993Lean.BCFG.Analytic.tail_BC_square_gate
#check Erdos993Lean.BCFG.Analytic.tail_FG_square_gate
#print axioms Erdos993Lean.BCFG.Analytic.tail_FG_square_gate
#check Erdos993Lean.BCFG.Analytic.tail_epsilon_BC_gate
#print axioms Erdos993Lean.BCFG.Analytic.tail_epsilon_BC_gate
#check Erdos993Lean.BCFG.Analytic.tail_epsilon_FG_gate
#print axioms Erdos993Lean.BCFG.Analytic.tail_epsilon_FG_gate
#check Erdos993Lean.BCFG.Analytic.tail_B_row_upper_gate
#print axioms Erdos993Lean.BCFG.Analytic.tail_B_row_upper_gate
#check Erdos993Lean.BCFG.Analytic.tail_F_row_upper_gate
#print axioms Erdos993Lean.BCFG.Analytic.tail_F_row_upper_gate
#check Erdos993Lean.BCFG.Analytic.tail_FG_center_gate
#print axioms Erdos993Lean.BCFG.Analytic.tail_FG_center_gate
