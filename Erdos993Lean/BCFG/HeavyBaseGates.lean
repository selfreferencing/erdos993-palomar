module

public import Erdos993Lean.BCFG.TailRationalGates

/-! Individually named whole-Nat-cross-product gates for the heavy base bounds.
The four ellUpper affine estimates use the exact printed row data. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Erdos993Lean.BCFG.Analytic

theorem heavy_base_sum_gate {A a B b C c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : (A*b+B*a)*c < C*(a*b)) :
    (A : ℝ)/a+(B : ℝ)/b < (C : ℝ)/c := by
  have hvalue := NatLog.value_lt_of_cross
    (p := NatLog.add (A,a) (B,b)) (q := (C,c))
    (NatLog.add_den_pos ha hb) hc h
  rw [NatLog.value_add ha hb] at hvalue
  exact hvalue

theorem heavy_base_B_ell_gate : (52472853 : ℝ)/10^8+9/169 < 2/3 := by
  simpa only [Nat.cast_one, Nat.cast_ofNat, Nat.cast_pow] using
    (heavy_base_sum_gate (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel :
      ((52472853 : ℕ)*169+9*10^8)*3 < 2*(10^8*169)))

theorem heavy_base_C_ell_gate : (58221562 : ℝ)/10^8+1/179 < 2/3 := by
  simpa only [Nat.cast_one, Nat.cast_ofNat, Nat.cast_pow] using
    (heavy_base_sum_gate (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel :
      ((58221562 : ℕ)*179+1*10^8)*3 < 2*(10^8*179)))

theorem heavy_base_F_ell_gate : (96508090 : ℝ)/10^8+1/105 < 4/3 := by
  simpa only [Nat.cast_one, Nat.cast_ofNat, Nat.cast_pow] using
    (heavy_base_sum_gate (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel :
      ((96508090 : ℕ)*105+1*10^8)*3 < 4*(10^8*105)))

theorem heavy_base_G_ell_gate : (99325178 : ℝ)/10^8+1/54 < 4/3 := by
  simpa only [Nat.cast_one, Nat.cast_ofNat, Nat.cast_pow] using
    (heavy_base_sum_gate (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel :
      ((99325178 : ℕ)*54+1*10^8)*3 < 4*(10^8*54)))

theorem heavy_base_C_low_gate : (3 : ℝ)/5 ≤ 39/50 :=
  tail_fraction_le (by decide +kernel) (by decide +kernel)
    (by decide +kernel : (3 : ℕ)*50 ≤ 39*5)

theorem heavy_base_G_low_gate : (8 : ℝ)/5 ≤ 33/20 :=
  tail_fraction_le (by decide +kernel) (by decide +kernel)
    (by decide +kernel : (8 : ℕ)*20 ≤ 33*5)

theorem heavy_base_BC_margin_pos_gate : (0 : ℝ) < 4349/1125 :=
  tail_fraction_pos (by decide +kernel)
    (by decide +kernel : (0 : ℕ)*1125 < 4349*1)

theorem heavy_base_FG_margin_pos_gate : (0 : ℝ) < 16613/400 :=
  tail_fraction_pos (by decide +kernel)
    (by decide +kernel : (0 : ℕ)*400 < 16613*1)

end Erdos993Lean.BCFG.Analytic

#check Erdos993Lean.BCFG.Analytic.heavy_base_sum_gate
#print axioms Erdos993Lean.BCFG.Analytic.heavy_base_sum_gate
#check Erdos993Lean.BCFG.Analytic.heavy_base_B_ell_gate
#print axioms Erdos993Lean.BCFG.Analytic.heavy_base_B_ell_gate
#check Erdos993Lean.BCFG.Analytic.heavy_base_C_ell_gate
#print axioms Erdos993Lean.BCFG.Analytic.heavy_base_C_ell_gate
#check Erdos993Lean.BCFG.Analytic.heavy_base_F_ell_gate
#print axioms Erdos993Lean.BCFG.Analytic.heavy_base_F_ell_gate
#check Erdos993Lean.BCFG.Analytic.heavy_base_G_ell_gate
#print axioms Erdos993Lean.BCFG.Analytic.heavy_base_G_ell_gate
#check Erdos993Lean.BCFG.Analytic.heavy_base_C_low_gate
#print axioms Erdos993Lean.BCFG.Analytic.heavy_base_C_low_gate
#check Erdos993Lean.BCFG.Analytic.heavy_base_G_low_gate
#print axioms Erdos993Lean.BCFG.Analytic.heavy_base_G_low_gate
#check Erdos993Lean.BCFG.Analytic.heavy_base_BC_margin_pos_gate
#print axioms Erdos993Lean.BCFG.Analytic.heavy_base_BC_margin_pos_gate
#check Erdos993Lean.BCFG.Analytic.heavy_base_FG_margin_pos_gate
#print axioms Erdos993Lean.BCFG.Analytic.heavy_base_FG_margin_pos_gate
