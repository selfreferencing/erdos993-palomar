module

public import Erdos993Lean.Analytic.V213.SmallForestAffineIdentity
public import Mathlib.Tactic.LinearCombination

/-!

Signed Pascal increments, the actual quadratic bracket, and a discrete
positive-superlevel argument. No endpoint catalogue or finite record is used.
The parameter b in GBracket corresponds to the paper's index b+1.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.SmallForest

/-- Monotonicity on a finite interval from its adjacent steps. -/
theorem interval_le_of_steps (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b)
    (hs : ∀ i, a ≤ i → i < b → f i ≤ f (i + 1)) : f a ≤ f b := by
  induction b generalizing a with
  | zero =>
      have ha : a = 0 := by omega
      subst a
      exact le_rfl
  | succ b ih =>
      by_cases he : a = b + 1
      · subst a
        exact le_rfl
      have ha : a ≤ b := by omega
      have hfirst : f a ≤ f b := ih ha (fun i hai hib => hs i hai (by omega))
      exact hfirst.trans (hs b ha (by omega))

theorem exists_positive_step (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b)
    (hf : f a < f b) : ∃ i, a ≤ i ∧ i < b ∧ f i < f (i + 1) := by
  classical
  by_contra hn
  push_neg at hn
  have hm := interval_le_of_steps (fun i => -f i) hab (by
    intro i hai hib
    have hh := hn i hai hib
    linarith)
  linarith

theorem exists_negative_step (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b)
    (hf : f b < f a) : ∃ i, a ≤ i ∧ i < b ∧ f (i + 1) < f i := by
  classical
  by_contra hn
  push_neg at hn
  have hm := interval_le_of_steps f hab (by
    intro i hai hib
    exact hn i hai hib)
  linarith

/-- Positive increments on one interval force every positive weak superlevel
set to be an interval, provided the initial value is nonpositive. -/
theorem positive_superlevel_of_positive_steps_interval (f : ℕ → ℝ)
    (hzero : f 0 ≤ 0)
    (hsteps : ∀ a b c : ℕ, a ≤ b → b ≤ c →
      f a < f (a + 1) → f c < f (c + 1) → f b < f (b + 1))
    {q : ℝ} (hq : 0 < q) {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c)
    (ha : q ≤ f a) (hc : q ≤ f c) : q ≤ f b := by
  by_contra hn
  have hb : f b < q := lt_of_not_ge hn
  obtain ⟨i, _, hia, hi⟩ := exists_positive_step f (Nat.zero_le a) (by linarith)
  obtain ⟨j, haj, hjb, hj⟩ := exists_negative_step f hab (by linarith)
  obtain ⟨k, hbk, _, hk⟩ := exists_positive_step f hbc (by linarith)
  have hmid := hsteps i j k (by omega) (by omega) hi hk
  linarith

/-- Pascal's identity with zero-extended signed lower index. -/
theorem binom_pascal (m : ℕ) (j : ℤ) :
    binom (m + 1) j = binom m j + binom m (j - 1) := by
  by_cases hj : 0 ≤ j
  · by_cases hz : j = 0
    · subst j
      simp [binom]
    · have hjm : 0 ≤ j - 1 := by omega
      have hn : j.toNat = (j - 1).toNat + 1 := by omega
      simp only [binom, if_pos hj, if_pos hjm]
      rw [hn, Nat.choose_succ_succ']
      push_cast
      ring
  · have hjm : ¬0 ≤ j - 1 := by omega
    simp only [binom, if_neg hj, if_neg hjm, zero_add]

theorem G_increment (w : ℝ) (j : ℤ) (m : ℕ) :
    G w j (m + 1) - G w j m = G w (j - 1) m := by
  have hj : j - 1 + 1 = j := by omega
  simp only [G, binom_pascal, hj]
  ring

theorem binom_zero_above (m : ℕ) (j : ℤ) (hj : (m : ℤ) < j) :
    binom m j = 0 := by
  have hz : 0 ≤ j := by omega
  have hm : m < j.toNat := by omega
  simp only [binom, if_pos hz, Nat.choose_eq_zero_of_lt hm, Nat.cast_zero]

theorem G_zero_above_support (w : ℝ) (j m : ℕ) (hj : m + 1 < j) :
    G w (j : ℤ) m = 0 := by
  unfold G
  rw [binom_zero_above m (j : ℤ) (by omega),
    binom_zero_above m ((j : ℤ) - 1) (by omega),
    binom_zero_above m ((j : ℤ) + 1) (by omega)]
  ring

theorem G_zero_index (w : ℝ) (m : ℕ) : G w 0 m = 1 - (1 - w) * m := by
  simp [G, binom]

theorem G_succ_nat (w : ℝ) (b m : ℕ) :
    G w ((b + 1 : ℕ) : ℤ) m = (m.choose (b + 1) : ℝ) -
      w * (m.choose b : ℝ) - (1 - w) * (m.choose (b + 2) : ℝ) := by
  have hm : ((b + 1 : ℕ) : ℤ) - 1 = (b : ℤ) := by omega
  have hp : ((b + 1 : ℕ) : ℤ) + 1 = ((b + 2 : ℕ) : ℤ) := by omega
  simp only [G, hm, hp, binom_nat]

noncomputable def GBracket (w : ℝ) (b : ℕ) (x : ℝ) : ℝ :=
  (x - b) * (b + 2) - w * (b + 1) * (b + 2) -
    (1 - w) * (x - b) * (x - b - 1)

private theorem choose_adjacent_real (m b : ℕ) (hbm : b ≤ m) :
    (m.choose (b + 1) : ℝ) * ((b : ℝ) + 1) =
      (m.choose b : ℝ) * ((m : ℝ) - b) := by
  have h := Nat.choose_succ_right_eq m b
  have hr : (m.choose (b + 1) : ℝ) * ((b : ℝ) + 1) =
      (m.choose b : ℝ) * ((m - b : ℕ) : ℝ) := by exact_mod_cast h
  simpa only [Nat.cast_sub hbm] using hr

/-- Cleared form of the printed quadratic factor; m=b is included explicitly. -/
theorem G_cleared_quadratic (w : ℝ) (b m : ℕ) (hbm : b ≤ m) :
    ((b : ℝ) + 1) * ((b : ℝ) + 2) * G w ((b + 1 : ℕ) : ℤ) m =
      (m.choose b : ℝ) * GBracket w b m := by
  rw [G_succ_nat]
  by_cases he : m = b
  · subst m
    rw [Nat.choose_self, Nat.choose_eq_zero_of_lt (by omega : b < b + 1),
      Nat.choose_eq_zero_of_lt (by omega : b < b + 2)]
    simp only [Nat.cast_one, Nat.cast_zero]
    unfold GBracket
    ring
  · have hbm' : b + 1 ≤ m := by omega
    have h1 := choose_adjacent_real m b hbm
    have h2 := choose_adjacent_real m (b + 1) hbm'
    push_cast at h2
    unfold GBracket
    linear_combination
      (((b : ℝ) + 2) - (1 - w) * ((m : ℝ) - b - 1)) * h1 -
        ((b : ℝ) + 1) * (1 - w) * h2

theorem G_pos_iff_bracket_pos (w : ℝ) (b m : ℕ) (hbm : b ≤ m) :
    0 < G w ((b + 1 : ℕ) : ℤ) m ↔ 0 < GBracket w b m := by
  have hleft : 0 < ((b : ℝ) + 1) * ((b : ℝ) + 2) := by positivity
  have hchoose : 0 < (m.choose b : ℝ) := by exact_mod_cast Nat.choose_pos hbm
  have he := G_cleared_quadratic w b m hbm
  constructor
  · intro h
    have hp := mul_pos hleft h
    rw [he] at hp
    exact (mul_pos_iff_of_pos_left hchoose).mp hp
  · intro h
    have hp := mul_pos hchoose h
    rw [← he] at hp
    exact (mul_pos_iff_of_pos_left hleft).mp hp

/-- The quadratic's positive set is an interval; no roots or rounding needed. -/
theorem GBracket_positive_interval (w : ℝ) (b : ℕ) (hw : w ≤ 1)
    {x y z : ℝ} (hxy : x ≤ y) (hyz : y ≤ z)
    (hx : 0 < GBracket w b x) (hz : 0 < GBracket w b z) :
    0 < GBracket w b y := by
  by_cases hleft : x = y
  · simpa only [← hleft] using hx
  by_cases hright : y = z
  · simpa only [hright] using hz
  have hxy' : x < y := lt_of_le_of_ne hxy hleft
  have hyz' : y < z := lt_of_le_of_ne hyz hright
  have hxz : 0 < z - x := by linarith
  have he : (z - x) * GBracket w b y =
      (z - y) * GBracket w b x + (y - x) * GBracket w b z +
        (1 - w) * (z - x) * (y - x) * (z - y) := by
    unfold GBracket
    ring
  have hp : 0 < (z - y) * GBracket w b x := mul_pos (by linarith) hx
  have hq : 0 ≤ (y - x) * GBracket w b z :=
    mul_nonneg (by linarith) (le_of_lt hz)
  have hc : 0 ≤ (1 - w) * (z - x) * (y - x) * (z - y) :=
    mul_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.mpr hw) (le_of_lt hxz))
      (sub_nonneg.mpr hxy)) (sub_nonneg.mpr hyz)
  have hm : 0 < (z - x) * GBracket w b y := by linarith
  exact (mul_pos_iff_of_pos_left hxz).mp hm

theorem G_positive_interval (w : ℝ) (hw : w ≤ 1) (j : ℕ)
    {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c)
    (ha : 0 < G w (j : ℤ) a) (hc : 0 < G w (j : ℤ) c) :
    0 < G w (j : ℤ) b := by
  cases j with
  | zero =>
      simp only [Nat.cast_zero] at ha hc ⊢
      rw [G_zero_index] at ha hc ⊢
      have hbcR : (b : ℝ) ≤ c := by exact_mod_cast hbc
      have hp : 0 ≤ (1 - w) * ((c : ℝ) - b) := mul_nonneg (by linarith) (by linarith)
      nlinarith
  | succ j =>
      have hja : j ≤ a := by
        by_contra hn
        have he := G_zero_above_support w (j + 1) a (by omega)
        rw [he] at ha
        exact (lt_irrefl 0) ha
      have hjb : j ≤ b := by omega
      have hjc : j ≤ c := by omega
      apply (G_pos_iff_bracket_pos w j b hjb).mpr
      exact GBracket_positive_interval w j hw
        (by exact_mod_cast hab) (by exact_mod_cast hbc)
        ((G_pos_iff_bracket_pos w j a hja).mp ha)
        ((G_pos_iff_bracket_pos w j c hjc).mp hc)

theorem G_initial_nonpos (w : ℝ) (hw : 0 ≤ w) (j : ℕ) (hj : 1 ≤ j) :
    G w (j : ℤ) 0 ≤ 0 := by
  by_cases he : j = 1
  · subst j
    rw [G_succ_nat w 0 0]
    norm_num
    exact hw
  · have hz := G_zero_above_support w j 0 (by omega)
    rw [hz]

theorem G_positive_superlevel_interval (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (j : ℕ) (hj : 1 ≤ j) {q : ℝ} (hq : 0 < q)
    {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c)
    (ha : q ≤ G w (j : ℤ) a) (hc : q ≤ G w (j : ℤ) c) :
    q ≤ G w (j : ℤ) b := by
  have hind : (j : ℤ) - 1 = ((j - 1 : ℕ) : ℤ) := by omega
  apply positive_superlevel_of_positive_steps_interval (fun m => G w (j : ℤ) m)
    (G_initial_nonpos w hw0 j hj) _ hq hab hbc ha hc
  intro i n k hin hnk hi hk
  have hi' : 0 < G w ((j - 1 : ℕ) : ℤ) i := by
    rw [← hind, ← G_increment]
    linarith
  have hk' : 0 < G w ((j - 1 : ℕ) : ℤ) k := by
    rw [← hind, ← G_increment]
    linarith
  have hn := G_positive_interval w hw1 (j - 1) hin hnk hi' hk'
  rw [← hind, ← G_increment] at hn
  linarith

/-- Strict positive superlevels follow by using the smaller endpoint value
as the weak level. The weak theorem above is the supporting-line interface. -/
theorem G_strict_positive_superlevel_interval (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (j : ℕ) (hj : 1 ≤ j) {q : ℝ} (hq : 0 < q)
    {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c)
    (ha : q < G w (j : ℤ) a) (hc : q < G w (j : ℤ) c) :
    q < G w (j : ℤ) b := by
  have hm : q < min (G w (j : ℤ) a) (G w (j : ℤ) c) := lt_min ha hc
  have hb := G_positive_superlevel_interval w hw0 hw1 j hj (hq.trans hm)
    hab hbc (min_le_left _ _) (min_le_right _ _)
  exact hm.trans_le hb

end Erdos993Lean.Analytic.V213.SmallForest

#check Erdos993Lean.Analytic.V213.SmallForest.interval_le_of_steps
#print axioms Erdos993Lean.Analytic.V213.SmallForest.interval_le_of_steps
#check Erdos993Lean.Analytic.V213.SmallForest.exists_positive_step
#print axioms Erdos993Lean.Analytic.V213.SmallForest.exists_positive_step
#check Erdos993Lean.Analytic.V213.SmallForest.exists_negative_step
#print axioms Erdos993Lean.Analytic.V213.SmallForest.exists_negative_step
#check Erdos993Lean.Analytic.V213.SmallForest.positive_superlevel_of_positive_steps_interval
#print axioms Erdos993Lean.Analytic.V213.SmallForest.positive_superlevel_of_positive_steps_interval
#check Erdos993Lean.Analytic.V213.SmallForest.binom_pascal
#print axioms Erdos993Lean.Analytic.V213.SmallForest.binom_pascal
#check Erdos993Lean.Analytic.V213.SmallForest.G_increment
#print axioms Erdos993Lean.Analytic.V213.SmallForest.G_increment
#check Erdos993Lean.Analytic.V213.SmallForest.binom_zero_above
#print axioms Erdos993Lean.Analytic.V213.SmallForest.binom_zero_above
#check Erdos993Lean.Analytic.V213.SmallForest.G_zero_above_support
#print axioms Erdos993Lean.Analytic.V213.SmallForest.G_zero_above_support
#check Erdos993Lean.Analytic.V213.SmallForest.G_zero_index
#print axioms Erdos993Lean.Analytic.V213.SmallForest.G_zero_index
#check Erdos993Lean.Analytic.V213.SmallForest.G_succ_nat
#print axioms Erdos993Lean.Analytic.V213.SmallForest.G_succ_nat
#check Erdos993Lean.Analytic.V213.SmallForest.G_cleared_quadratic
#print axioms Erdos993Lean.Analytic.V213.SmallForest.G_cleared_quadratic
#check Erdos993Lean.Analytic.V213.SmallForest.G_pos_iff_bracket_pos
#print axioms Erdos993Lean.Analytic.V213.SmallForest.G_pos_iff_bracket_pos
#check Erdos993Lean.Analytic.V213.SmallForest.GBracket_positive_interval
#print axioms Erdos993Lean.Analytic.V213.SmallForest.GBracket_positive_interval
#check Erdos993Lean.Analytic.V213.SmallForest.G_positive_interval
#print axioms Erdos993Lean.Analytic.V213.SmallForest.G_positive_interval
#check Erdos993Lean.Analytic.V213.SmallForest.G_initial_nonpos
#print axioms Erdos993Lean.Analytic.V213.SmallForest.G_initial_nonpos
#check Erdos993Lean.Analytic.V213.SmallForest.G_positive_superlevel_interval
#print axioms Erdos993Lean.Analytic.V213.SmallForest.G_positive_superlevel_interval
#check Erdos993Lean.Analytic.V213.SmallForest.G_strict_positive_superlevel_interval
#print axioms Erdos993Lean.Analytic.V213.SmallForest.G_strict_positive_superlevel_interval
