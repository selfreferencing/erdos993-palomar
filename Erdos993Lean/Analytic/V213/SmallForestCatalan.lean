module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Rat.BigOperators
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic

/-!
# Current Lemma 7.4: generic Catalan bounds

This new proof uses Pascal's adjacent
difference to express the same monotonicity/minimum used by the printed ratio
proof. There are no finite rank restrictions or inherited finite checks.

The scalar inequalities and the pure rising expression are proved here.
The forest decomposition/application is a separate consumer: this file does
not assume a numerical table or claim the small-forest theorem.

-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.SmallForestCatalan

open Finset

/-- The printed Catalan quotient, with genuine rational division. -/
def cat (n : ℕ) : ℚ := (Nat.choose (2 * n) n : ℚ) / ((n : ℚ) + 1)

/-- Adjacent binomial difference with the positive lower index written n+1. -/
def delta (m n : ℕ) : ℚ := (Nat.choose m (n + 1) : ℚ) - (Nat.choose m n : ℚ)

theorem cat_nonneg (n : ℕ) : 0 ≤ cat n := by
  unfold cat
  positivity

theorem cat_mul (n : ℕ) : ((n : ℚ) + 1) * cat n = (Nat.choose (2 * n) n : ℚ) := by
  unfold cat
  have hn : (n : ℚ) + 1 ≠ 0 := by positivity
  field_simp [hn]

/-- The identity used for the stronger of the two rising lines. -/
theorem cat_succ_mul (n : ℕ) :
    ((n : ℚ) + 1) * cat (n + 1) = (Nat.choose (2 * n + 2) n : ℚ) := by
  have hs : 2 * n + 2 - n = n + 2 := by omega
  have h := congrArg (fun x : ℕ => (x : ℚ))
    (Nat.choose_succ_right_eq (2 * n + 2) n)
  simp only [hs, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at h
  have he : 2 * (n + 1) = 2 * n + 2 := by omega
  unfold cat
  rw [he]
  push_cast
  rw [← mul_div_assoc]
  apply (div_eq_iff (by positivity : (n : ℚ) + 1 + 1 ≠ 0)).2
  nlinarith only [h]

theorem cat_le_succ (n : ℕ) : cat n ≤ cat (n + 1) := by
  apply (mul_le_mul_iff_of_pos_left (by positivity : (0 : ℚ) < (n : ℚ) + 1)).mp
  rw [cat_mul, cat_succ_mul]
  exact_mod_cast Nat.choose_le_choose n (by omega : 2 * n ≤ 2 * n + 2)

/-- A division-free identity, valid even when n exceeds m. -/
theorem delta_mul (m n : ℕ) :
    ((n : ℚ) + 1) * delta m n =
      (Nat.choose m n : ℚ) * ((m : ℚ) - 2 * (n : ℚ) - 1) := by
  by_cases hn : n ≤ m
  · have h := congrArg (fun x : ℕ => (x : ℚ)) (Nat.choose_succ_right_eq m n)
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hn] at h
    unfold delta
    nlinarith only [h]
  · have hz : Nat.choose m n = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have hz' : Nat.choose m (n + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [delta, hz, hz']

theorem delta_nonneg (m n : ℕ) (hm : 2 * n + 1 ≤ m) : 0 ≤ delta m n := by
  have hq : (0 : ℚ) ≤ (m : ℚ) - 2 * (n : ℚ) - 1 := by
    have : (2 : ℚ) * n + 1 ≤ m := by exact_mod_cast hm
    linarith
  apply (mul_le_mul_iff_of_pos_left (by positivity : (0 : ℚ) < (n : ℚ) + 1)).mp
  rw [mul_zero, delta_mul]
  exact mul_nonneg (by positivity) hq

theorem delta_nonpos (m n : ℕ) (hm : m ≤ 2 * n + 1) : delta m n ≤ 0 := by
  have hq : (m : ℚ) - 2 * (n : ℚ) - 1 ≤ 0 := by
    have : (m : ℚ) ≤ 2 * (n : ℚ) + 1 := by exact_mod_cast hm
    linarith
  apply (mul_le_mul_iff_of_pos_left (by positivity : (0 : ℚ) < (n : ℚ) + 1)).mp
  rw [mul_zero, delta_mul]
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hq

theorem delta_middle_zero (n : ℕ) : delta (2 * n + 1) n = 0 := by
  simp only [delta, Nat.choose_symm_half, sub_self]

theorem delta_minimum_value (n : ℕ) : delta (2 * n) n = -cat n := by
  have hcross : ((n : ℚ) + 1) * delta (2 * n) n = ((n : ℚ) + 1) * (-cat n) := by
    rw [delta_mul, mul_neg, cat_mul]
    push_cast
    ring
  exact (mul_left_cancel₀ (by positivity : (n : ℚ) + 1 ≠ 0)) hcross

/-- Pascal identifies the consecutive change of one binomial difference. -/
theorem delta_step (m n : ℕ) :
    delta (m + 1) (n + 1) = delta m (n + 1) + delta m n := by
  simp only [delta, Nat.choose_succ_succ, Nat.cast_add]
  ring

private theorem decreasing_segment (f : ℕ → ℚ) (top : ℕ)
    (hs : ∀ r < top, f (r + 1) ≤ f r) {m : ℕ} (hm : m ≤ top) : f top ≤ f m := by
  have aux : ∀ d m, m + d ≤ top → f (m + d) ≤ f m := by
    intro d
    induction d with
    | zero => intro m _; simp
    | succ d ih =>
      intro m h
      calc
        f (m + (d + 1)) = f ((m + d) + 1) := by rw [Nat.add_assoc]
        _ ≤ f (m + d) := hs _ (by omega)
        _ ≤ f m := ih m (by omega)
  have h := aux (top - m) m (by omega)
  have he : m + (top - m) = top := by omega
  simpa only [he] using h

/-- The global Catalan floor, including zero/outside-support and j=1 cases. -/
theorem delta_floor (m n : ℕ) : -cat n ≤ delta m n := by
  cases n with
  | zero =>
    simp only [delta, cat, Nat.mul_zero, Nat.choose_zero_right, Nat.choose_one_right,
      Nat.cast_zero, zero_add, div_one, Nat.cast_one]
    have hm : (0 : ℚ) ≤ m := by positivity
    linarith
  | succ n =>
    by_cases hm : m ≤ 2 * (n + 1)
    · calc
        -cat (n + 1) = delta (2 * (n + 1)) (n + 1) := (delta_minimum_value _).symm
        _ ≤ delta m (n + 1) := by
          apply decreasing_segment (fun r => delta r (n + 1)) (2 * (n + 1)) ?_ hm
          intro r hr
          change delta (r + 1) (n + 1) ≤ delta r (n + 1)
          rw [delta_step]
          have h := delta_nonpos r n (by omega)
          linarith
    · exact (neg_nonpos.mpr (cat_nonneg _)).trans (delta_nonneg _ _ (by omega))

/-- First weak rising line, valid on both sides of its zero. -/
theorem delta_rising_lower (m n : ℕ) :
    cat n * ((m : ℚ) - 2 * (n : ℚ) - 1) ≤ delta m n := by
  by_cases hm : m ≤ 2 * n
  · have hq : (m : ℚ) - 2 * (n : ℚ) - 1 ≤ -1 := by
      have : (m : ℚ) ≤ 2 * (n : ℚ) := by exact_mod_cast hm
      linarith
    calc
      cat n * ((m : ℚ) - 2 * (n : ℚ) - 1) ≤ cat n * (-1) :=
        mul_le_mul_of_nonneg_left hq (cat_nonneg n)
      _ = -cat n := by ring
      _ ≤ delta m n := delta_floor _ _
  · have hq : (0 : ℚ) ≤ (m : ℚ) - 2 * (n : ℚ) - 1 := by
      have : (2 : ℚ) * n + 1 ≤ m := by exact_mod_cast (show 2 * n + 1 ≤ m by omega)
      linarith
    have hc : ((n : ℚ) + 1) * cat n ≤ (Nat.choose m n : ℚ) := by
      rw [cat_mul]
      exact_mod_cast Nat.choose_le_choose n (by omega : 2 * n ≤ m)
    apply (mul_le_mul_iff_of_pos_left (by positivity : (0 : ℚ) < (n : ℚ) + 1)).mp
    calc
      ((n : ℚ) + 1) * (cat n * ((m : ℚ) - 2 * (n : ℚ) - 1)) =
          (((n : ℚ) + 1) * cat n) * ((m : ℚ) - 2 * (n : ℚ) - 1) := by ring
      _ ≤ (Nat.choose m n : ℚ) * ((m : ℚ) - 2 * (n : ℚ) - 1) :=
        mul_le_mul_of_nonneg_right hc hq
      _ = ((n : ℚ) + 1) * delta m n := (delta_mul _ _).symm

/-- Second weak rising line; the central zero is handled separately. -/
theorem delta_rising_upper (m n : ℕ) :
    cat (n + 1) * ((m : ℚ) - 2 * (n : ℚ) - 1) ≤ delta m n := by
  by_cases hm : m ≤ 2 * n
  · have hq : (m : ℚ) - 2 * (n : ℚ) - 1 ≤ 0 := by
      have : (m : ℚ) ≤ 2 * (n : ℚ) := by exact_mod_cast hm
      linarith
    exact (mul_le_mul_of_nonpos_right (cat_le_succ n) hq).trans (delta_rising_lower m n)
  · by_cases hmid : m = 2 * n + 1
    · subst m
      rw [delta_middle_zero]
      push_cast
      convert (le_rfl : (0 : ℚ) ≤ 0) using 1 <;> ring
    · have hq : (0 : ℚ) ≤ (m : ℚ) - 2 * (n : ℚ) - 1 := by
        have : (2 : ℚ) * n + 1 ≤ m := by exact_mod_cast (show 2 * n + 1 ≤ m by omega)
        linarith
      have hc : ((n : ℚ) + 1) * cat (n + 1) ≤ (Nat.choose m n : ℚ) := by
        rw [cat_succ_mul]
        exact_mod_cast Nat.choose_le_choose n (by omega : 2 * n + 2 ≤ m)
      apply (mul_le_mul_iff_of_pos_left (by positivity : (0 : ℚ) < (n : ℚ) + 1)).mp
      calc
        ((n : ℚ) + 1) * (cat (n + 1) * ((m : ℚ) - 2 * (n : ℚ) - 1)) =
            (((n : ℚ) + 1) * cat (n + 1)) * ((m : ℚ) - 2 * (n : ℚ) - 1) := by ring
        _ ≤ (Nat.choose m n : ℚ) * ((m : ℚ) - 2 * (n : ℚ) - 1) :=
          mul_le_mul_of_nonneg_right hc hq
        _ = ((n : ℚ) + 1) * delta m n := (delta_mul _ _).symm

theorem catalan_floor (j m : ℕ) (hj : 1 ≤ j) :
    -cat (j - 1) ≤ (Nat.choose m j : ℚ) - (Nat.choose m (j - 1) : ℚ) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel, delta] using delta_floor m n

theorem catalan_rising_lower (j m : ℕ) (hj : 1 ≤ j) :
    cat (j - 1) * ((m : ℚ) - 2 * (j : ℚ) + 1) ≤
      (Nat.choose m j : ℚ) - (Nat.choose m (j - 1) : ℚ) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  simpa [delta, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one,
    show (m : ℚ) - 2 * ((n : ℚ) + 1) + 1 = (m : ℚ) - 2 * (n : ℚ) - 1 by ring]
    using delta_rising_lower m n

theorem catalan_rising_upper (j m : ℕ) (hj : 1 ≤ j) :
    cat j * ((m : ℚ) - 2 * (j : ℚ) + 1) ≤
      (Nat.choose m j : ℚ) - (Nat.choose m (j - 1) : ℚ) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  simpa [delta, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one,
    show (m : ℚ) - 2 * ((n : ℚ) + 1) + 1 = (m : ℚ) - 2 * (n : ℚ) - 1 by ring]
    using delta_rising_upper m n

/-- Literal real Catalan value for the printed real-valued lower lines. -/
def realCatalan (n : ℕ) : ℝ := (cat n : ℝ)

theorem realCatalan_eq (n : ℕ) :
    realCatalan n = (Nat.choose (2 * n) n : ℝ) / ((n : ℝ) + 1) := by
  simp [realCatalan, cat]

theorem catalan_floor_real (j m : ℕ) (hj : 1 ≤ j) :
    -realCatalan (j - 1) ≤ (Nat.choose m j : ℝ) - (Nat.choose m (j - 1) : ℝ) := by
  unfold realCatalan
  exact_mod_cast catalan_floor j m hj

theorem catalan_rising_lower_real (j m : ℕ) (hj : 1 ≤ j) :
    realCatalan (j - 1) * ((m : ℝ) - 2 * (j : ℝ) + 1) ≤
      (Nat.choose m j : ℝ) - (Nat.choose m (j - 1) : ℝ) := by
  unfold realCatalan
  exact_mod_cast catalan_rising_lower j m hj

theorem catalan_rising_upper_real (j m : ℕ) (hj : 1 ≤ j) :
    realCatalan j * ((m : ℝ) - 2 * (j : ℝ) + 1) ≤
      (Nat.choose m j : ℝ) - (Nat.choose m (j - 1) : ℝ) := by
  unfold realCatalan
  exact_mod_cast catalan_rising_upper j m hj

/-- The adjacent difference is nondecreasing from exactly the printed threshold. -/
theorem delta_mono_from (m M n : ℕ) (hn : 2 * n ≤ m + 1) (hM : m ≤ M) :
    delta m n ≤ delta M n := by
  cases n with
  | zero =>
    simp only [delta, zero_add, Nat.choose_one_right, Nat.choose_zero_right, Nat.cast_one]
    exact sub_le_sub_right (by exact_mod_cast hM) 1
  | succ n =>
    have hs : ∀ r, m ≤ r → delta r (n + 1) ≤ delta (r + 1) (n + 1) := by
      intro r hr
      rw [delta_step]
      have h := delta_nonneg r n (by omega)
      linarith
    have aux : ∀ d, delta m (n + 1) ≤ delta (m + d) (n + 1) := by
      intro d
      induction d with
      | zero => simp
      | succ d ih =>
        calc
          delta m (n + 1) ≤ delta (m + d) (n + 1) := ih
          _ ≤ delta ((m + d) + 1) (n + 1) := hs _ (by omega)
          _ = delta (m + (d + 1)) (n + 1) := by rw [Nat.add_assoc]
    have h := aux (M - m)
    have he : m + (M - m) = M := by omega
    simpa only [he] using h

/-- Equivalent full-range expression; terms with h>c are zero. -/
def rising (a c k : ℕ) : ℚ :=
  (Nat.choose a k : ℚ) - (Nat.choose a (k - 1) : ℚ) -
    ∑ h ∈ Finset.Icc 1 (k - 1), (Nat.choose c h : ℚ) * cat (k - h - 1)

theorem rising_eq_printed (a c k : ℕ) :
    rising a c k = (Nat.choose a k : ℚ) - (Nat.choose a (k - 1) : ℚ) -
      ∑ h ∈ Finset.Icc 1 (min c (k - 1)), (Nat.choose c h : ℚ) * cat (k - h - 1) := by
  unfold rising
  congr 1
  symm
  apply Finset.sum_subset
  · intro h hh
    simp only [Finset.mem_Icc] at hh ⊢
    omega
  · intro h hh hn
    have hc : c < h := by
      simp only [Finset.mem_Icc] at hh hn
      omega
    simp [Nat.choose_eq_zero_of_lt hc]

theorem rising_antitone_c (a c C k : ℕ) (hc : c ≤ C) : rising a C k ≤ rising a c k := by
  have hs :
      (∑ h ∈ Finset.Icc 1 (k - 1), (Nat.choose c h : ℚ) * cat (k - h - 1)) ≤
        ∑ h ∈ Finset.Icc 1 (k - 1), (Nat.choose C h : ℚ) * cat (k - h - 1) := by
    apply Finset.sum_le_sum
    intro h _
    apply mul_le_mul_of_nonneg_right _ (cat_nonneg _)
    exact_mod_cast Nat.choose_le_choose h hc
  unfold rising
  linarith

theorem rising_monotone_a (a A c k : ℕ) (hk : 1 ≤ k) (ha : 2 * k - 3 ≤ a)
    (hA : a ≤ A) : rising a c k ≤ rising A c k := by
  have hs := delta_mono_from a A (k - 1) (by omega) hA
  have he : k - 1 + 1 = k := by omega
  simp only [delta, he] at hs
  unfold rising
  exact sub_le_sub_right hs _

/-- Real form of the *entire* pure lower expression. -/
def realRising (a c k : ℕ) : ℝ := (rising a c k : ℝ)

theorem realRising_eq_printed (a c k : ℕ) :
    realRising a c k = (Nat.choose a k : ℝ) - (Nat.choose a (k - 1) : ℝ) -
      ∑ h ∈ Finset.Icc 1 (min c (k - 1)), (Nat.choose c h : ℝ) * realCatalan (k - h - 1) := by
  unfold realRising
  rw [rising_eq_printed]
  simp [realCatalan]

theorem realRising_antitone_c (a c C k : ℕ) (hc : c ≤ C) :
    realRising a C k ≤ realRising a c k := by
  unfold realRising
  exact_mod_cast rising_antitone_c a c C k hc

theorem realRising_monotone_a (a A c k : ℕ) (hk : 1 ≤ k) (ha : 2 * k - 3 ≤ a)
    (hA : a ≤ A) : realRising a c k ≤ realRising A c k := by
  unfold realRising
  exact_mod_cast rising_monotone_a a A c k hk ha hA

end Erdos993Lean.Analytic.V213.SmallForestCatalan

#check Erdos993Lean.Analytic.V213.SmallForestCatalan.cat_nonneg
#print axioms Erdos993Lean.Analytic.V213.SmallForestCatalan.cat_nonneg
#check Erdos993Lean.Analytic.V213.SmallForestCatalan.cat_mul
#print axioms Erdos993Lean.Analytic.V213.SmallForestCatalan.cat_mul
#check Erdos993Lean.Analytic.V213.SmallForestCatalan.cat_succ_mul
#print axioms Erdos993Lean.Analytic.V213.SmallForestCatalan.cat_succ_mul
#check Erdos993Lean.Analytic.V213.SmallForestCatalan.cat_le_succ
#print axioms Erdos993Lean.Analytic.V213.SmallForestCatalan.cat_le_succ
#check Erdos993Lean.Analytic.V213.SmallForestCatalan.delta_mul
#print axioms Erdos993Lean.Analytic.V213.SmallForestCatalan.delta_mul
#check Erdos993Lean.Analytic.V213.SmallForestCatalan.delta_nonneg
#print axioms Erdos993Lean.Analytic.V213.SmallForestCatalan.delta_nonneg
#check Erdos993Lean.Analytic.V213.SmallForestCatalan.delta_nonpos
#print axioms Erdos993Lean.Analytic.V213.SmallForestCatalan.delta_nonpos
#check Erdos993Lean.Analytic.V213.SmallForestCatalan.delta_middle_zero
#print axioms Erdos993Lean.Analytic.V213.SmallForestCatalan.delta_middle_zero
#check Erdos993Lean.Analytic.V213.SmallForestCatalan.delta_minimum_value
#print axioms Erdos993Lean.Analytic.V213.SmallForestCatalan.delta_minimum_value
#check Erdos993Lean.Analytic.V213.SmallForestCatalan.delta_step
#print axioms Erdos993Lean.Analytic.V213.SmallForestCatalan.delta_step
#check Erdos993Lean.Analytic.V213.SmallForestCatalan.delta_floor
#print axioms Erdos993Lean.Analytic.V213.SmallForestCatalan.delta_floor
#check Erdos993Lean.Analytic.V213.SmallForestCatalan.delta_rising_lower
#print axioms Erdos993Lean.Analytic.V213.SmallForestCatalan.delta_rising_lower
#check Erdos993Lean.Analytic.V213.SmallForestCatalan.delta_rising_upper
#print axioms Erdos993Lean.Analytic.V213.SmallForestCatalan.delta_rising_upper
#check Erdos993Lean.Analytic.V213.SmallForestCatalan.catalan_floor
#print axioms Erdos993Lean.Analytic.V213.SmallForestCatalan.catalan_floor
#check Erdos993Lean.Analytic.V213.SmallForestCatalan.catalan_rising_lower
#print axioms Erdos993Lean.Analytic.V213.SmallForestCatalan.catalan_rising_lower
#check Erdos993Lean.Analytic.V213.SmallForestCatalan.catalan_rising_upper
#print axioms Erdos993Lean.Analytic.V213.SmallForestCatalan.catalan_rising_upper
#check Erdos993Lean.Analytic.V213.SmallForestCatalan.realCatalan_eq
#print axioms Erdos993Lean.Analytic.V213.SmallForestCatalan.realCatalan_eq
#check Erdos993Lean.Analytic.V213.SmallForestCatalan.catalan_floor_real
#print axioms Erdos993Lean.Analytic.V213.SmallForestCatalan.catalan_floor_real
#check Erdos993Lean.Analytic.V213.SmallForestCatalan.catalan_rising_lower_real
#print axioms Erdos993Lean.Analytic.V213.SmallForestCatalan.catalan_rising_lower_real
#check Erdos993Lean.Analytic.V213.SmallForestCatalan.catalan_rising_upper_real
#print axioms Erdos993Lean.Analytic.V213.SmallForestCatalan.catalan_rising_upper_real
#check Erdos993Lean.Analytic.V213.SmallForestCatalan.delta_mono_from
#print axioms Erdos993Lean.Analytic.V213.SmallForestCatalan.delta_mono_from
#check Erdos993Lean.Analytic.V213.SmallForestCatalan.rising_eq_printed
#print axioms Erdos993Lean.Analytic.V213.SmallForestCatalan.rising_eq_printed
#check Erdos993Lean.Analytic.V213.SmallForestCatalan.rising_antitone_c
#print axioms Erdos993Lean.Analytic.V213.SmallForestCatalan.rising_antitone_c
#check Erdos993Lean.Analytic.V213.SmallForestCatalan.rising_monotone_a
#print axioms Erdos993Lean.Analytic.V213.SmallForestCatalan.rising_monotone_a
#check Erdos993Lean.Analytic.V213.SmallForestCatalan.realRising_eq_printed
#print axioms Erdos993Lean.Analytic.V213.SmallForestCatalan.realRising_eq_printed
#check Erdos993Lean.Analytic.V213.SmallForestCatalan.realRising_antitone_c
#print axioms Erdos993Lean.Analytic.V213.SmallForestCatalan.realRising_antitone_c
#check Erdos993Lean.Analytic.V213.SmallForestCatalan.realRising_monotone_a
#print axioms Erdos993Lean.Analytic.V213.SmallForestCatalan.realRising_monotone_a
