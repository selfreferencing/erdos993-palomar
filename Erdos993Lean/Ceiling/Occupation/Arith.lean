module

public import Mathlib

/-!
# B5, part 4: the arithmetic of the matching-essential case (`N₃`, `N₅`)

With `f(d) = 1 + (7/3)(3/10)^d` (`fac`; the lower bound for a child ratio at root degree `d`), a
finite family of degrees `d_i` (`i ∈ N`, `k = |N|`, `D = ∑ d_i`) and `P = ∏ f(d_i)`:

* `N3_nonneg`: `(726k - 740) P + 1736 - 2499k + 714D ≥ 0` for `k ≥ 2` (ceiling proof, App. R3, (R4));
* `N5_nonneg`: `(1567k - 1749) P + 5082 - 5880k + 1680D ≥ 0` for `k ≥ 2` (ceiling proof, App. R3, (R5)).

The proof: `P ≥ 1` pays `714D ≥ 1773k - 996`
(resp. `1680D ≥ 4313k - 3333`).  Otherwise, for `k ≥ 13` (resp. `k ≥ 15`) the affine minorant
`(3/10)^d ≥ (837 - 189d)/10000` (`pow_ge_affine`, equality at `d = 3, 4`) gives
`P ≥ 1 + (1953k - 441D)/10000` and a quadratic inequality, split at `k = 23 | 24`
(resp. `25 | 26`).  The remaining 181 pairs `(k, D)` with `2 ≤ k ≤ 12` (resp. 247 pairs with
`2 ≤ k ≤ 14`) use the balancing lemma `P ≥ f(a)^(k-s) f(a+1)^s` for `D = ka + s`, `0 ≤ s < k`
(`balance`; `f` is log-convex: `fac_cross`, `fac_support`) and an exact integer check evaluated by
the kernel (`check3_all`, `check5_all`, `decide +kernel`; no `native_decide`).  An independent
numerical check enumerates the same 181 + 247 pairs; the minima there are
`5592/25` and `13693/20`, both at `(k, D) = (2, 2)`.
-/

@[expose] public section

namespace Erdos993Lean
namespace Occupation

open Finset

/-- The degree factor `f(d) = 1 + (7/3)(3/10)^d`. -/
def fac (d : ℕ) : ℚ := 1 + 7 / 3 * (3 / 10) ^ d

theorem fac_pos (d : ℕ) : 0 < fac d := by unfold fac; positivity

theorem one_le_fac (d : ℕ) : 1 ≤ fac d := by
  unfold fac
  have : (0 : ℚ) ≤ (3 / 10) ^ d := by positivity
  linarith

/-- Cross-multiplied monotonicity of the ratios `f(j+1)/f(j)`. -/
theorem fac_cross {j j' : ℕ} (h : j ≤ j') : fac j' * fac (j + 1) ≤ fac (j' + 1) * fac j := by
  unfold fac
  have hq : (3 / 10 : ℚ) ^ j' ≤ (3 / 10) ^ j := pow_le_pow_of_le_one (by norm_num) (by norm_num) h
  have e : (1 + 7 / 3 * (3 / 10 : ℚ) ^ (j' + 1)) * (1 + 7 / 3 * (3 / 10) ^ j) -
      (1 + 7 / 3 * (3 / 10 : ℚ) ^ j') * (1 + 7 / 3 * (3 / 10) ^ (j + 1)) =
      49 / 30 * ((3 / 10) ^ j - (3 / 10) ^ j') := by ring
  nlinarith

/-- `f(a + m) f(a)^m ≥ f(a) f(a+1)^m`. -/
theorem fac_up (a m : ℕ) : fac a * fac (a + 1) ^ m ≤ fac (a + m) * fac a ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hc := fac_cross (show a ≤ a + m by omega)
    have h1 : 0 ≤ fac (a + 1) := (fac_pos _).le
    have h2 : 0 ≤ fac a ^ m := pow_nonneg (fac_pos _).le m
    calc fac a * fac (a + 1) ^ (m + 1) = fac (a + 1) * (fac a * fac (a + 1) ^ m) := by ring
      _ ≤ fac (a + 1) * (fac (a + m) * fac a ^ m) := mul_le_mul_of_nonneg_left ih h1
      _ = (fac (a + m) * fac (a + 1)) * fac a ^ m := by ring
      _ ≤ (fac (a + m + 1) * fac a) * fac a ^ m := mul_le_mul_of_nonneg_right hc h2
      _ = fac (a + (m + 1)) * fac a ^ (m + 1) := by rw [← add_assoc]; ring

/-- `f(a - m) f(a+1)^m ≥ f(a)^(m+1)` for `m ≤ a`. -/
theorem fac_down (a m : ℕ) (hm : m ≤ a) : fac a ^ (m + 1) ≤ fac (a - m) * fac (a + 1) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have ih' := ih (by omega)
    have hc := fac_cross (show a - (m + 1) ≤ a by omega)
    have heq : a - (m + 1) + 1 = a - m := by omega
    rw [heq] at hc
    have h1 : 0 ≤ fac a := (fac_pos _).le
    have h2 : 0 ≤ fac (a + 1) ^ m := pow_nonneg (fac_pos _).le m
    calc fac a ^ (m + 1 + 1) = fac a * fac a ^ (m + 1) := by ring
      _ ≤ fac a * (fac (a - m) * fac (a + 1) ^ m) := mul_le_mul_of_nonneg_left ih' h1
      _ = (fac a * fac (a - m)) * fac (a + 1) ^ m := by ring
      _ ≤ (fac (a + 1) * fac (a - (m + 1))) * fac (a + 1) ^ m := mul_le_mul_of_nonneg_right hc h2
      _ = fac (a - (m + 1)) * fac (a + 1) ^ (m + 1) := by ring

/-- The supporting line in log scale: `f(d) r^a ≥ f(a) r^d`, with `r = f(a+1)/f(a)`. -/
theorem fac_support (a d : ℕ) :
    fac a * (fac (a + 1) / fac a) ^ d ≤ fac d * (fac (a + 1) / fac a) ^ a := by
  have hfa := fac_pos a
  have hfa1 := fac_pos (a + 1)
  set r := fac (a + 1) / fac a with hr
  have hr0 : 0 < r := div_pos hfa1 hfa
  rcases le_total a d with had | hda
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le had
    have h := fac_up a m
    -- `f(a) r^(a+m) ≤ f(a+m) r^a` ⇔ `f(a) r^m ≤ f(a+m)`
    have key : fac a * r ^ m ≤ fac (a + m) := by
      rw [hr, div_pow, ← mul_div_assoc, div_le_iff₀ (pow_pos hfa m)]
      exact h
    calc fac a * r ^ (a + m) = (fac a * r ^ m) * r ^ a := by ring
      _ ≤ fac (a + m) * r ^ a := mul_le_mul_of_nonneg_right key (pow_nonneg hr0.le a)
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hda
    have h := fac_down (d + m) m (by omega)
    rw [show d + m - m = d by omega] at h
    -- `f(d+m) ≤ f(d) r^m`
    have key : fac (d + m) ≤ fac d * r ^ m := by
      rw [hr, div_pow, ← mul_div_assoc, le_div_iff₀ (pow_pos hfa m)]
      calc fac (d + m) * fac (d + m) ^ m = fac (d + m) ^ (m + 1) := by ring
        _ ≤ _ := h
    calc fac (d + m) * r ^ d ≤ (fac d * r ^ m) * r ^ d :=
          mul_le_mul_of_nonneg_right key (pow_nonneg hr0.le d)
      _ = fac d * r ^ (d + m) := by ring

/-- **Balancing**: for degrees `d_i` (`i ∈ N`, `|N| = k`) with `∑ d_i = k a + s`, `s ≤ k`,
`∏ f(d_i) ≥ f(a)^(k-s) f(a+1)^s`. -/
theorem balance {ι : Type*} (N : Finset ι) (d : ι → ℕ) (a s : ℕ) (hs : s ≤ N.card)
    (hD : ∑ i ∈ N, d i = N.card * a + s) :
    fac a ^ (N.card - s) * fac (a + 1) ^ s ≤ ∏ i ∈ N, fac (d i) := by
  have hfa := fac_pos a
  have hfa1 := fac_pos (a + 1)
  set r := fac (a + 1) / fac a with hr
  have hr0 : 0 < r := div_pos hfa1 hfa
  have h1 : ∏ i ∈ N, (fac a * r ^ d i) ≤ ∏ i ∈ N, (fac (d i) * r ^ a) :=
    Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i _ => fac_support a (d i))
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const,
    Finset.prod_pow_eq_pow_sum, hD] at h1
  -- `h1 : f(a)^k r^(k a + s) ≤ (∏ f(d_i)) r^(a k)`
  have hpos : 0 < r ^ (N.card * a) := pow_pos hr0 _
  have h3 : fac a ^ N.card * r ^ s * r ^ (N.card * a) ≤
      (∏ i ∈ N, fac (d i)) * r ^ (N.card * a) := by
    calc fac a ^ N.card * r ^ s * r ^ (N.card * a) = fac a ^ N.card * r ^ (N.card * a + s) := by
          rw [pow_add]; ring
      _ ≤ _ := by rw [← pow_mul, mul_comm a] at h1; exact h1
  have h2 : fac a ^ N.card * r ^ s ≤ ∏ i ∈ N, fac (d i) := le_of_mul_le_mul_right h3 hpos
  have h4 : fac a ^ N.card * r ^ s = fac a ^ (N.card - s) * fac (a + 1) ^ s := by
    have hsplit : fac a ^ N.card = fac a ^ (N.card - s) * fac a ^ s := by
      rw [← pow_add, Nat.sub_add_cancel hs]
    rw [hsplit, hr, div_pow, mul_assoc, mul_comm (fac a ^ s), div_mul_cancel₀ _
      (pow_ne_zero s hfa.ne')]
  rw [← h4]
  exact h2

/-- Numerator of `f(a) = (3·10^a + 7·3^a) / (3·10^a)`. -/
def facNum (a : ℕ) : ℕ := 3 * 10 ^ a + 7 * 3 ^ a

/-- Denominator of `f(a) = (3·10^a + 7·3^a) / (3·10^a)`. -/
def facDen (a : ℕ) : ℕ := 3 * 10 ^ a

/-- `check3 k D`: the value of `N₃` at the balanced product `f(a)^(k-s) f(a+1)^s` (`a = D / k`,
`s = D % k`) is positive, as an inequality of natural numbers with denominators cleared. -/
def check3 (k D : ℕ) : Bool :=
  2499 * k * (facDen (D / k) ^ (k - D % k) * facDen (D / k + 1) ^ (D % k)) <
    (726 * k - 740) * (facNum (D / k) ^ (k - D % k) * facNum (D / k + 1) ^ (D % k)) +
      (1736 + 714 * D) * (facDen (D / k) ^ (k - D % k) * facDen (D / k + 1) ^ (D % k))

/-- `check5 k D`: the same for `N₅`. -/
def check5 (k D : ℕ) : Bool :=
  5880 * k * (facDen (D / k) ^ (k - D % k) * facDen (D / k + 1) ^ (D % k)) <
    (1567 * k - 1749) * (facNum (D / k) ^ (k - D % k) * facNum (D / k + 1) ^ (D % k)) +
      (5082 + 1680 * D) * (facDen (D / k) ^ (k - D % k) * facDen (D / k + 1) ^ (D % k))

/-- **The 181 finite `N₃` cases** (`2 ≤ k ≤ 12`, `714 D < 1773 k - 996`), checked by the kernel. -/
theorem check3_all : ∀ k < 13, ∀ D < 29, 2 ≤ k → 714 * D < 1773 * k - 996 → check3 k D = true := by
  decide +kernel

/-- **The 247 finite `N₅` cases** (`2 ≤ k ≤ 14`, `1680 D < 4313 k - 3333`), checked by the
kernel. -/
theorem check5_all : ∀ k < 15, ∀ D < 34, 2 ≤ k → 1680 * D < 4313 * k - 3333 →
    check5 k D = true := by
  decide +kernel

/-- The two finite ranges have exactly `181` and `247` pairs `(k, D)` (the counts asserted by the
independent numerical check). -/
theorem card_cases : ((Finset.range 13 ×ˢ Finset.range 29).filter
      (fun p : ℕ × ℕ => 2 ≤ p.1 ∧ 714 * p.2 < 1773 * p.1 - 996)).card = 181 ∧
    ((Finset.range 15 ×ˢ Finset.range 34).filter
      (fun p : ℕ × ℕ => 2 ≤ p.1 ∧ 1680 * p.2 < 4313 * p.1 - 3333)).card = 247 := by
  decide +kernel

/-- `f(a)` as a quotient of natural numbers. -/
theorem fac_eq (a : ℕ) : fac a = (facNum a : ℚ) / facDen a := by
  unfold fac facNum facDen
  push_cast
  rw [div_pow]
  field_simp

/-- The balanced product as a quotient of the integers used by `check3`/`check5`. -/
theorem balprod_eq (a s m : ℕ) :
    fac a ^ m * fac (a + 1) ^ s =
      ((facNum a ^ m * facNum (a + 1) ^ s : ℕ) : ℚ) /
        ((facDen a ^ m * facDen (a + 1) ^ s : ℕ) : ℚ) := by
  rw [fac_eq, fac_eq, div_pow, div_pow]
  push_cast
  rw [div_mul_div_comm]

theorem facDen_pos (a : ℕ) : 0 < facDen a := by unfold facDen; positivity

/-- A passed `check3` gives the rational inequality for the balanced product. -/
theorem check3_sound {k D : ℕ} (hk : 2 ≤ k) (h : check3 k D = true) :
    0 < (726 * (k : ℚ) - 740) * (fac (D / k) ^ (k - D % k) * fac (D / k + 1) ^ (D % k)) +
      1736 - 2499 * k + 714 * D := by
  unfold check3 at h
  rw [decide_eq_true_iff] at h
  set num := facNum (D / k) ^ (k - D % k) * facNum (D / k + 1) ^ (D % k)
  set den := facDen (D / k) ^ (k - D % k) * facDen (D / k + 1) ^ (D % k)
  have hden : 0 < den := Nat.mul_pos (pow_pos (facDen_pos _) _) (pow_pos (facDen_pos _) _)
  have h740 : 740 ≤ 726 * k := by omega
  have hq : (2499 * k * den : ℚ) < (726 * k - 740 : ℚ) * num + (1736 + 714 * D) * den := by
    have := h
    have hc : ((726 * k - 740 : ℕ) : ℚ) = 726 * (k : ℚ) - 740 := by
      rw [Nat.cast_sub h740]; push_cast; ring
    rw [← hc]
    exact_mod_cast this
  rw [balprod_eq]
  have hdq : (0 : ℚ) < den := by exact_mod_cast hden
  have key : (726 * (k : ℚ) - 740) * ((num : ℚ) / den) + 1736 - 2499 * k + 714 * D =
      ((726 * (k : ℚ) - 740) * num + (1736 + 714 * D) * den - 2499 * k * den) / den := by
    field_simp
    ring
  rw [key]
  apply div_pos _ hdq
  linarith

/-- A passed `check5` gives the rational inequality for the balanced product. -/
theorem check5_sound {k D : ℕ} (hk : 2 ≤ k) (h : check5 k D = true) :
    0 < (1567 * (k : ℚ) - 1749) * (fac (D / k) ^ (k - D % k) * fac (D / k + 1) ^ (D % k)) +
      5082 - 5880 * k + 1680 * D := by
  unfold check5 at h
  rw [decide_eq_true_iff] at h
  set num := facNum (D / k) ^ (k - D % k) * facNum (D / k + 1) ^ (D % k)
  set den := facDen (D / k) ^ (k - D % k) * facDen (D / k + 1) ^ (D % k)
  have hden : 0 < den := Nat.mul_pos (pow_pos (facDen_pos _) _) (pow_pos (facDen_pos _) _)
  have h1749 : 1749 ≤ 1567 * k := by omega
  have hq : (5880 * k * den : ℚ) < (1567 * k - 1749 : ℚ) * num + (5082 + 1680 * D) * den := by
    have := h
    have hc : ((1567 * k - 1749 : ℕ) : ℚ) = 1567 * (k : ℚ) - 1749 := by
      rw [Nat.cast_sub h1749]; push_cast; ring
    rw [← hc]
    exact_mod_cast this
  rw [balprod_eq]
  have hdq : (0 : ℚ) < den := by exact_mod_cast hden
  have key : (1567 * (k : ℚ) - 1749) * ((num : ℚ) / den) + 5082 - 5880 * k + 1680 * D =
      ((1567 * (k : ℚ) - 1749) * num + (5082 + 1680 * D) * den - 5880 * k * den) / den := by
    field_simp
    ring
  rw [key]
  apply div_pos _ hdq
  linarith

/-- The affine minorant `(3/10)^d ≥ (837 - 189 d)/10000` (equality at `d = 3, 4`). -/
theorem pow_ge_affine (d : ℕ) : (837 - 189 * (d : ℚ)) / 10000 ≤ (3 / 10) ^ d := by
  rcases Nat.lt_or_ge d 5 with h | h
  · interval_cases d <;> norm_num
  · have h1 : (5 : ℚ) ≤ d := by exact_mod_cast h
    have h2 : (0 : ℚ) ≤ (3 / 10) ^ d := by positivity
    have h3 : (837 - 189 * (d : ℚ)) / 10000 ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg _ (by norm_num)
      linarith
    linarith

theorem one_le_prod_fac {ι : Type*} (N : Finset ι) (d : ι → ℕ) : 1 ≤ ∏ i ∈ N, fac (d i) := by
  calc (1 : ℚ) = ∏ _i ∈ N, (1 : ℚ) := by simp
    _ ≤ ∏ i ∈ N, fac (d i) :=
      Finset.prod_le_prod₀ (fun _ _ => zero_le_one) (fun i _ => one_le_fac (d i))

/-- `∏ (1 + λ ρ^{d_i}) ≥ 1 + λ ∑ ρ^{d_i}`. -/
theorem prod_fac_ge_sum {ι : Type*} [DecidableEq ι] (N : Finset ι) (d : ι → ℕ) :
    1 + 7 / 3 * ∑ i ∈ N, (3 / 10 : ℚ) ^ d i ≤ ∏ i ∈ N, fac (d i) := by
  induction N using Finset.induction_on with
  | empty => simp
  | insert j N hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj]
    have h1 : (0 : ℚ) ≤ (3 / 10) ^ d j := by positivity
    have h2 : (0 : ℚ) ≤ ∑ i ∈ N, (3 / 10 : ℚ) ^ d i := Finset.sum_nonneg fun i _ => by positivity
    have h3 : 0 ≤ fac (d j) := (fac_pos _).le
    have h4 := mul_le_mul_of_nonneg_left ih h3
    unfold fac at h4 ⊢
    nlinarith [mul_nonneg h1 h2]

/-- The affine lower bound `∏ f(d_i) ≥ 1 + (1953 k - 441 D)/10000`. -/
theorem prod_fac_ge_affine {ι : Type*} [DecidableEq ι] (N : Finset ι) (d : ι → ℕ) :
    1 + (1953 * (N.card : ℚ) - 441 * ∑ i ∈ N, (d i : ℚ)) / 10000 ≤ ∏ i ∈ N, fac (d i) := by
  have h1 := prod_fac_ge_sum N d
  have h2 : ∑ i ∈ N, (837 - 189 * (d i : ℚ)) / 10000 ≤ ∑ i ∈ N, (3 / 10 : ℚ) ^ d i :=
    Finset.sum_le_sum fun i _ => pow_ge_affine (d i)
  have h3 : ∑ i ∈ N, (837 - 189 * (d i : ℚ)) / 10000 =
      (837 * (N.card : ℚ) - 189 * ∑ i ∈ N, (d i : ℚ)) / 10000 := by
    rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring
  rw [h3] at h2
  linarith

/-- **`N₃ ≥ 0` for every `k ≥ 2`** (ceiling proof, App. R3, (R4); the three regimes: `P ≥ 1`, the affine
minorant for `k ≥ 13`, and the 181 balanced finite cases for `k ≤ 12`). -/
theorem N3_nonneg {ι : Type*} [DecidableEq ι] (N : Finset ι) (d : ι → ℕ) (hk : 2 ≤ N.card) :
    0 ≤ (726 * (N.card : ℚ) - 740) * ∏ i ∈ N, fac (d i) + 1736 - 2499 * N.card +
      714 * ∑ i ∈ N, (d i : ℚ) := by
  set k := N.card with hkdef
  set D := ∑ i ∈ N, d i with hDdef
  have hDq : ∑ i ∈ N, (d i : ℚ) = (D : ℚ) := by rw [hDdef]; push_cast; rfl
  rw [hDq]
  set P := ∏ i ∈ N, fac (d i) with hP
  have hkq : (2 : ℚ) ≤ k := by exact_mod_cast hk
  have hc : (0 : ℚ) < 726 * k - 740 := by linarith
  have hP1 : 1 ≤ P := one_le_prod_fac N d
  by_cases h1 : 1773 * k ≤ 714 * D + 996
  · have h1q : (1773 : ℚ) * k ≤ 714 * D + 996 := by exact_mod_cast h1
    nlinarith [mul_le_mul_of_nonneg_left hP1 hc.le]
  · push_neg at h1
    have h1q : (714 : ℚ) * D + 997 ≤ 1773 * k := by exact_mod_cast h1
    by_cases h2 : 13 ≤ k
    · have h2q : (13 : ℚ) ≤ k := by exact_mod_cast h2
      have hPa := prod_fac_ge_affine N d
      rw [← hkdef, hDq] at hPa
      have hDq0 : (0 : ℚ) ≤ D := Nat.cast_nonneg D
      have hmain := mul_le_mul_of_nonneg_left hPa hc.le
      -- `E(k, D) ≥ 0` with `E = 1417878k² − 19175220k + 9960000 + (7466340 − 320166k)D`
      have hE : 0 ≤ 1417878 * (k : ℚ) ^ 2 - 19175220 * k + 9960000 +
          (7466340 - 320166 * k) * D := by
        by_cases h3 : k ≤ 23
        · have h3q : (k : ℚ) ≤ 23 := by exact_mod_cast h3
          nlinarith [mul_nonneg hDq0 (show (0 : ℚ) ≤ 7466340 - 320166 * k by linarith),
            mul_nonneg (show (0 : ℚ) ≤ k - 13 by linarith)
              (show (0 : ℚ) ≤ 1417878 * k - 742806 by linarith)]
        · push_neg at h3
          have h3q : (24 : ℚ) ≤ k := by exact_mod_cast h3
          nlinarith [mul_nonneg (show (0 : ℚ) ≤ 320166 * k - 7466340 by linarith)
              (show (0 : ℚ) ≤ 1773 * k - 997 - 714 * D by linarith),
            mul_nonneg (show (0 : ℚ) ≤ k - 24 by linarith) (show (0 : ℚ) ≤ k by linarith)]
      nlinarith
    · push_neg at h2
      have hD29 : D < 29 := by omega
      have hck := check3_all k (by omega) D hD29 hk (by omega)
      have hpos := check3_sound hk hck
      have hbal := balance N d (D / k) (D % k) (Nat.mod_lt D (by omega)).le
        (by rw [← hDdef, ← hkdef]; exact (Nat.div_add_mod D k).symm)
      rw [← hkdef] at hbal
      nlinarith [mul_le_mul_of_nonneg_left hbal hc.le]

/-- **`N₅ ≥ 0` for every `k ≥ 2`** (ceiling proof, App. R3, (R5); regimes `P ≥ 1`, affine for `k ≥ 15`,
and the 247 balanced finite cases for `k ≤ 14`). -/
theorem N5_nonneg {ι : Type*} [DecidableEq ι] (N : Finset ι) (d : ι → ℕ) (hk : 2 ≤ N.card) :
    0 ≤ (1567 * (N.card : ℚ) - 1749) * ∏ i ∈ N, fac (d i) + 5082 - 5880 * N.card +
      1680 * ∑ i ∈ N, (d i : ℚ) := by
  set k := N.card with hkdef
  set D := ∑ i ∈ N, d i with hDdef
  have hDq : ∑ i ∈ N, (d i : ℚ) = (D : ℚ) := by rw [hDdef]; push_cast; rfl
  rw [hDq]
  set P := ∏ i ∈ N, fac (d i) with hP
  have hkq : (2 : ℚ) ≤ k := by exact_mod_cast hk
  have hc : (0 : ℚ) < 1567 * k - 1749 := by linarith
  have hP1 : 1 ≤ P := one_le_prod_fac N d
  by_cases h1 : 4313 * k ≤ 1680 * D + 3333
  · have h1q : (4313 : ℚ) * k ≤ 1680 * D + 3333 := by exact_mod_cast h1
    nlinarith [mul_le_mul_of_nonneg_left hP1 hc.le]
  · push_neg at h1
    have h1q : (1680 : ℚ) * D + 3334 ≤ 4313 * k := by exact_mod_cast h1
    by_cases h2 : 15 ≤ k
    · have h2q : (15 : ℚ) ≤ k := by exact_mod_cast h2
      have hPa := prod_fac_ge_affine N d
      rw [← hkdef, hDq] at hPa
      have hDq0 : (0 : ℚ) ≤ D := Nat.cast_nonneg D
      have hmain := mul_le_mul_of_nonneg_left hPa hc.le
      have hE : 0 ≤ 3060351 * (k : ℚ) ^ 2 - 46545797 * k + 33330000 +
          (17571309 - 691047 * k) * D := by
        by_cases h3 : k ≤ 25
        · have h3q : (k : ℚ) ≤ 25 := by exact_mod_cast h3
          nlinarith [mul_nonneg hDq0 (show (0 : ℚ) ≤ 17571309 - 691047 * k by linarith),
            mul_nonneg (show (0 : ℚ) ≤ k - 15 by linarith)
              (show (0 : ℚ) ≤ 3060351 * k - 637532 by linarith)]
        · push_neg at h3
          have h3q : (26 : ℚ) ≤ k := by exact_mod_cast h3
          nlinarith [mul_nonneg (show (0 : ℚ) ≤ 691047 * k - 17571309 by linarith)
              (show (0 : ℚ) ≤ 4313 * k - 3334 - 1680 * D by linarith),
            mul_nonneg (show (0 : ℚ) ≤ k - 26 by linarith) (show (0 : ℚ) ≤ k by linarith)]
      nlinarith
    · push_neg at h2
      have hD34 : D < 34 := by omega
      have hck := check5_all k (by omega) D hD34 hk (by omega)
      have hpos := check5_sound hk hck
      have hbal := balance N d (D / k) (D % k) (Nat.mod_lt D (by omega)).le
        (by rw [← hDdef, ← hkdef]; exact (Nat.div_add_mod D k).symm)
      rw [← hkdef] at hbal
      nlinarith [mul_le_mul_of_nonneg_left hbal hc.le]

end Occupation
end Erdos993Lean
