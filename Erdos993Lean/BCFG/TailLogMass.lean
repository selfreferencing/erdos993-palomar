module

public import Erdos993Lean.BCFG.TailRationalGates
public import Erdos993Lean.BCFG.LogRemainder
public import Erdos993Lean.BCFG.RowParameters

/-! Actual logarithmic tail estimates. The entropy-product comparison follows
directly from log(t) <= t-1, avoiding a separate monotonicity theorem. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Erdos993Lean.BCFG.Analytic

theorem tail_log_two_bounds : (2 : ℝ)/3 < Real.log 2 ∧ Real.log 2 < 3/4 := by
  have hz : (0 : ℝ) < 1/3 :=
    div_pos zero_lt_one (by exact_mod_cast (by decide +kernel : 0 < (3 : ℕ)))
  have hz1 : (1 : ℝ)/3 < 1 := by
    simpa only [Nat.cast_one,Nat.cast_ofNat,div_one] using
      (tail_fraction_lt (by decide +kernel) (by decide +kernel)
        (by decide +kernel : (1 : ℕ)*1 < 1*3))
  have hl := logLower_lt 1 hz hz1
  have hu := log_lt_logUpper 1 hz hz1
  have harg : (1+(1 : ℝ)/3)/(1-1/3) = 2 := by norm_num
  have hlo : logLower 1 ((1 : ℝ)/3) = 2/3 := by norm_num [logLower]
  have hup : logUpper 1 ((1 : ℝ)/3) = 25/36 := by
    norm_num [logUpper,logLower]
  rw [harg,hlo] at hl
  rw [harg,hup] at hu
  exact ⟨hl,hu.trans tail_log_two_upper_gate⟩

theorem tail_logMass_two_pow (n : ℕ) :
    logMass (1/(2 : ℝ)^n) = (n : ℝ)*Real.log 2 := by
  simp only [logMass,one_div,Real.log_inv,Real.log_pow,neg_neg]

/-- The tangent inequality proves the actual product bound on the whole tail. -/
theorem tail_entropy_product_le {omega cutoff : ℝ}
    (hw : 0 < omega) (hc : 0 < cutoff) (hwc : omega ≤ cutoff)
    (hlog : 1 ≤ logMass cutoff) :
    omega*logMass omega ≤ cutoff*logMass cutoff := by
  have h := Real.log_le_sub_one_of_pos (div_pos hc hw)
  rw [Real.log_div hc.ne' hw.ne'] at h
  have hm := mul_le_mul_of_nonneg_left h hw.le
  have heq : omega*(cutoff/omega-1) = cutoff-omega := by
    field_simp [hw.ne'] <;> ring
  rw [heq] at hm
  have ht := mul_nonneg (sub_nonneg.mpr hwc) (sub_nonneg.mpr hlog)
  dsimp [logMass] at ht ⊢
  nlinarith only [hm,ht]

theorem tail_logMass_antitone {omega cutoff : ℝ}
    (hw : 0 < omega) (hwc : omega ≤ cutoff) :
    logMass cutoff ≤ logMass omega := by
  exact neg_le_neg (Real.log_le_log hw hwc)

theorem tail_BC_log_bounds {omega : ℝ} (hw : 0 < omega) (ht : omega ≤ 1/16) :
    (8 : ℝ)/3 < logMass omega ∧ omega*logMass omega < 3/16 := by
  have hc : (0 : ℝ) < 1/16 :=
    div_pos zero_lt_one (by exact_mod_cast (by decide +kernel : 0 < (16 : ℕ)))
  have hid : logMass ((1 : ℝ)/16) = 4*Real.log 2 := by
    convert tail_logMass_two_pow 4 using 1 <;> norm_num
  have hlow : (8 : ℝ)/3 < logMass ((1 : ℝ)/16) := by
    rw [hid]
    linarith only [tail_log_two_bounds.1]
  have hhigh : ((1 : ℝ)/16)*logMass (1/16) < 3/16 := by
    rw [hid]
    linarith only [tail_log_two_bounds.2]
  have hone : (1 : ℝ) ≤ logMass (1/16) := by linarith only [hlow]
  exact ⟨hlow.trans_le (tail_logMass_antitone hw ht),
    (tail_entropy_product_le hw hc ht hone).trans_lt hhigh⟩

theorem tail_FG_log_bounds {omega : ℝ} (hw : 0 < omega) (ht : omega ≤ 1/64) :
    (4 : ℝ) < logMass omega ∧ omega*logMass omega < 9/128 := by
  have hc : (0 : ℝ) < 1/64 :=
    div_pos zero_lt_one (by exact_mod_cast (by decide +kernel : 0 < (64 : ℕ)))
  have hid : logMass ((1 : ℝ)/64) = 6*Real.log 2 := by
    convert tail_logMass_two_pow 6 using 1 <;> norm_num
  have hlow : (4 : ℝ) < logMass ((1 : ℝ)/64) := by
    rw [hid]
    linarith only [tail_log_two_bounds.1]
  have hhigh : ((1 : ℝ)/64)*logMass (1/64) < 9/128 := by
    rw [hid]
    linarith only [tail_log_two_bounds.2]
  have hone : (1 : ℝ) ≤ logMass (1/64) := by linarith only [hlow]
  exact ⟨hlow.trans_le (tail_logMass_antitone hw ht),
    (tail_entropy_product_le hw hc ht hone).trans_lt hhigh⟩

end Erdos993Lean.BCFG.Analytic

#check Erdos993Lean.BCFG.Analytic.tail_log_two_bounds
#print axioms Erdos993Lean.BCFG.Analytic.tail_log_two_bounds
#check Erdos993Lean.BCFG.Analytic.tail_logMass_two_pow
#print axioms Erdos993Lean.BCFG.Analytic.tail_logMass_two_pow
#check Erdos993Lean.BCFG.Analytic.tail_entropy_product_le
#print axioms Erdos993Lean.BCFG.Analytic.tail_entropy_product_le
#check Erdos993Lean.BCFG.Analytic.tail_logMass_antitone
#print axioms Erdos993Lean.BCFG.Analytic.tail_logMass_antitone
#check Erdos993Lean.BCFG.Analytic.tail_BC_log_bounds
#print axioms Erdos993Lean.BCFG.Analytic.tail_BC_log_bounds
#check Erdos993Lean.BCFG.Analytic.tail_FG_log_bounds
#print axioms Erdos993Lean.BCFG.Analytic.tail_FG_log_bounds
