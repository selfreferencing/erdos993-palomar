module

public import Erdos993Lean.BCFG.NatFractionPairs
public import Erdos993Lean.BCFG.LogRemainder

/-! Literal fraction-pair interpretation of the printed lower sum and remainder. -/

@[expose] public section
set_option autoImplicit false

namespace Erdos993Lean.BCFG.Analytic.NatLog

def term (a b j : ℕ) : Pair := (2*a^(2*j+1), (2*j+1)*b^(2*j+1))

def lower (a b : ℕ) : ℕ → Pair
  | 0 => (0,1)
  | n+1 => add (lower a b n) (term a b n)

def remainder (a b n : ℕ) : Pair :=
  (2*a^(2*n+1)*b^2, (2*n+1)*b^(2*n+1)*(b^2-a^2))

def upper (a b n : ℕ) : Pair := add (lower a b n) (remainder a b n)

theorem term_den_pos (a j : ℕ) {b : ℕ} (hb : 0 < b) : 0 < (term a b j).2 := by
  unfold term
  exact Nat.mul_pos (by omega) (pow_pos hb _)

theorem lower_den_pos (a n : ℕ) {b : ℕ} (hb : 0 < b) : 0 < (lower a b n).2 := by
  induction n with
  | zero => norm_num [lower]
  | succ n ih => exact add_den_pos ih (term_den_pos a n hb)

theorem remainder_den_pos (n : ℕ) {a b : ℕ} (hab : a < b) :
    0 < (remainder a b n).2 := by
  have hb : 0 < b := lt_of_le_of_lt (Nat.zero_le a) hab
  have hsq : a^2 < b^2 := Nat.pow_lt_pow_left hab (by decide)
  have hsub : 0 < b^2-a^2 := Nat.sub_pos_of_lt hsq
  unfold remainder
  exact Nat.mul_pos (Nat.mul_pos (by omega) (pow_pos hb _)) hsub

theorem upper_den_pos (n : ℕ) {a b : ℕ} (hab : a < b) :
    0 < (upper a b n).2 :=
  add_den_pos (lower_den_pos a n (lt_of_le_of_lt (Nat.zero_le a) hab))
    (remainder_den_pos n hab)

theorem term_value (a j : ℕ) {b : ℕ} (hb : 0 < b) :
    value (term a b j) = 2*((a : ℝ)/b)^(2*j+1)/(2*(j : ℝ)+1) := by
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  have hjR : (2*(j : ℝ)+1) ≠ 0 := by positivity
  simp only [value, term, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    Nat.cast_ofNat, Nat.cast_pow, div_pow]
  field_simp [hbR, hjR] <;> ring

theorem lower_value (a n : ℕ) {b : ℕ} (hb : 0 < b) :
    value (lower a b n) = logLower n ((a : ℝ)/b) := by
  induction n with
  | zero => simp [lower, value, logLower]
  | succ n ih =>
      rw [lower, value_add (lower_den_pos a n hb) (term_den_pos a n hb), ih,
        term_value a n hb]
      simp only [logLower, Finset.sum_range_succ, Nat.cast_add, Nat.cast_mul,
        Nat.cast_one, Nat.cast_ofNat]
      ring

theorem remainder_value (n : ℕ) {a b : ℕ} (hab : a < b) :
    value (remainder a b n) =
      2*((a : ℝ)/b)^(2*n+1)/((2*(n : ℝ)+1)*(1-((a : ℝ)/b)^2)) := by
  have hb : 0 < b := lt_of_le_of_lt (Nat.zero_le a) hab
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have habR : (a : ℝ) < b := by exact_mod_cast hab
  have haR : (0 : ℝ) ≤ a := by positivity
  have hsq : a^2 ≤ b^2 := (Nat.pow_lt_pow_left hab (by decide : 2 ≠ 0)).le
  have hsR : (a : ℝ)^2 < (b : ℝ)^2 :=
    pow_lt_pow_left₀ habR haR (by decide : 2 ≠ 0)
  have hsqR : (b : ℝ)^2-(a : ℝ)^2 ≠ 0 := (sub_pos.mpr hsR).ne'
  have hz0 : (0 : ℝ) ≤ (a : ℝ)/b := div_nonneg haR hbR.le
  have hz1 : (a : ℝ)/b < 1 := (div_lt_one hbR).2 habR
  have hprod : 0 < (1-(a : ℝ)/b)*(1+(a : ℝ)/b) :=
    mul_pos (sub_pos.mpr hz1) (by linarith)
  have hz2 : 1-((a : ℝ)/b)^2 ≠ 0 := ne_of_gt (by nlinarith [hprod])
  have hn : (2*(n : ℝ)+1) ≠ 0 := by positivity
  simp only [value, remainder, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_sub hsq, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  simp only [div_pow]
  field_simp [hbR.ne', hsqR, hz2, hn] <;> ring

theorem upper_value (n : ℕ) {a b : ℕ} (hab : a < b) :
    value (upper a b n) = logUpper n ((a : ℝ)/b) := by
  have hb : 0 < b := lt_of_le_of_lt (Nat.zero_le a) hab
  rw [upper, value_add (lower_den_pos a n hb) (remainder_den_pos n hab),
    lower_value a n hb, remainder_value n hab]
  rfl

theorem lower_gt_rat_of_cross (n a b c d : ℕ) (hb : 0 < b) (hd : 0 < d)
    (h : c*(lower a b n).2 < (lower a b n).1*d) :
    (c : ℝ)/d < logLower n ((a : ℝ)/b) := by
  rw [← lower_value a n hb]
  exact value_lt_of_cross (p := (c,d)) hd (lower_den_pos a n hb) h

theorem upper_lt_rat_of_cross (n a b c d : ℕ) (hab : a < b) (hd : 0 < d)
    (h : (upper a b n).1*d < c*(upper a b n).2) :
    logUpper n ((a : ℝ)/b) < (c : ℝ)/d := by
  rw [← upper_value n hab]
  exact value_lt_of_cross (q := (c,d)) (upper_den_pos n hab) hd h

end Erdos993Lean.BCFG.Analytic.NatLog

#check Erdos993Lean.BCFG.Analytic.NatLog.term
#print axioms Erdos993Lean.BCFG.Analytic.NatLog.term
#check Erdos993Lean.BCFG.Analytic.NatLog.lower
#print axioms Erdos993Lean.BCFG.Analytic.NatLog.lower
#check Erdos993Lean.BCFG.Analytic.NatLog.remainder
#print axioms Erdos993Lean.BCFG.Analytic.NatLog.remainder
#check Erdos993Lean.BCFG.Analytic.NatLog.upper
#print axioms Erdos993Lean.BCFG.Analytic.NatLog.upper
#check Erdos993Lean.BCFG.Analytic.NatLog.term_den_pos
#print axioms Erdos993Lean.BCFG.Analytic.NatLog.term_den_pos
#check Erdos993Lean.BCFG.Analytic.NatLog.lower_den_pos
#print axioms Erdos993Lean.BCFG.Analytic.NatLog.lower_den_pos
#check Erdos993Lean.BCFG.Analytic.NatLog.remainder_den_pos
#print axioms Erdos993Lean.BCFG.Analytic.NatLog.remainder_den_pos
#check Erdos993Lean.BCFG.Analytic.NatLog.upper_den_pos
#print axioms Erdos993Lean.BCFG.Analytic.NatLog.upper_den_pos
#check Erdos993Lean.BCFG.Analytic.NatLog.term_value
#print axioms Erdos993Lean.BCFG.Analytic.NatLog.term_value
#check Erdos993Lean.BCFG.Analytic.NatLog.lower_value
#print axioms Erdos993Lean.BCFG.Analytic.NatLog.lower_value
#check Erdos993Lean.BCFG.Analytic.NatLog.remainder_value
#print axioms Erdos993Lean.BCFG.Analytic.NatLog.remainder_value
#check Erdos993Lean.BCFG.Analytic.NatLog.upper_value
#print axioms Erdos993Lean.BCFG.Analytic.NatLog.upper_value
#check Erdos993Lean.BCFG.Analytic.NatLog.lower_gt_rat_of_cross
#print axioms Erdos993Lean.BCFG.Analytic.NatLog.lower_gt_rat_of_cross
#check Erdos993Lean.BCFG.Analytic.NatLog.upper_lt_rat_of_cross
#print axioms Erdos993Lean.BCFG.Analytic.NatLog.upper_lt_rat_of_cross
