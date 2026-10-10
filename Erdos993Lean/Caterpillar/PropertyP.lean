module

public import Mathlib

/-!
# Property P and the letters S, L, E

This file formalizes the algebraic core of the caterpillar theorem.



Sequences are integer sequences indexed by `ℤ` (finitely supported, zero at negative indices);
`shift a` is multiplication by `x`.  For a rooted graph `(G, r)` the pair `(Z, X)` is
`Z = I(G)`, `X = I(G - r)`.

The residual objects are
* `D a k = a_k² - a_{k-1} a_{k+1}` (log-concavity defect),
* `W a b k = 2 a_k b_k - a_{k-1} b_{k+1} - a_{k+1} b_{k-1}` (weak synchronisation),
* `K a k = a_k a_{k-1} - a_{k+1} a_{k-2}` (`= W a (shift a) k`).

Property `P Z X`: both supports are intervals starting at `0`, `Z 0 = X 0`, and the six sequences
`Z - X`, `X + x X - Z`, `D Z`, `D X`, `W Z X`, `W Z (x X)` are nonnegative.

The letters (on pairs `(Z, X)`):
* `S`: `(Z + x X, Z)` — a new root adjacent to the old root;
* `L`: `(Z + x X, (1 + x) X)` — a pendant leaf at the root;
* `E`: `((1 + x) Z + x X, (1 + 2x) X)` — a pendant two-vertex path at the root.

Main theorem: each letter preserves `P` (`P.S`, `P.L`, `P.E`), on the whole algebraic domain.
-/

@[expose] public section

namespace Erdos993Lean.PropertyP

/-- Integer sequences indexed by the integers. -/
abbrev ZSeq := ℤ → ℤ

/-- Multiplication by `x`: `(shift a) k = a (k - 1)`. -/
def shift (a : ZSeq) : ZSeq := fun k => a (k - 1)

/-- Log-concavity defect `D(a)_k = a_k² - a_{k-1} a_{k+1}`. -/
def D (a : ZSeq) (k : ℤ) : ℤ := a k * a k - a (k - 1) * a (k + 1)

/-- Weak synchronisation `W(a,b)_k = 2 a_k b_k - a_{k-1} b_{k+1} - a_{k+1} b_{k-1}`. -/
def W (a b : ZSeq) (k : ℤ) : ℤ := 2 * (a k * b k) - a (k - 1) * b (k + 1) - a (k + 1) * b (k - 1)

/-- Shifted self-synchronisation `K(a)_k = a_k a_{k-1} - a_{k+1} a_{k-2}`. -/
def K (a : ZSeq) (k : ℤ) : ℤ := a k * a (k - 1) - a (k + 1) * a (k - 2)

/-- `a` is positive exactly on `[0, d]` and zero elsewhere. -/
structure IntervalSupport (a : ZSeq) (d : ℕ) : Prop where
  pos : ∀ k : ℤ, 0 ≤ k → k ≤ d → 0 < a k
  zero_neg : ∀ k : ℤ, k < 0 → a k = 0
  zero_gt : ∀ k : ℤ, (d : ℤ) < k → a k = 0

/-- The invariant `P(Z, X)` of the caterpillar theorem. -/
structure P (Z X : ZSeq) : Prop where
  suppX : ∃ d : ℕ, IntervalSupport X d
  suppZ : ∃ e : ℕ, IntervalSupport Z e
  const : Z 0 = X 0
  R : ∀ k, 0 ≤ Z k - X k
  U : ∀ k, 0 ≤ X k + X (k - 1) - Z k
  DZ : ∀ k, 0 ≤ D Z k
  DX : ∀ k, 0 ≤ D X k
  W0 : ∀ k, 0 ≤ W Z X k
  W1 : ∀ k, 0 ≤ W Z (shift X) k

/-- First component of the letters `S` and `L`: `Z + x X`. -/
def addShift (Z X : ZSeq) : ZSeq := fun k => Z k + X (k - 1)

/-- Second component of `L`: `(1 + x) X`. -/
def onePlusX (X : ZSeq) : ZSeq := fun k => X k + X (k - 1)

/-- First component of `E`: `(1 + x) Z + x X`. -/
def eZ (Z X : ZSeq) : ZSeq := fun k => Z k + Z (k - 1) + X (k - 1)

/-- Second component of `E`: `(1 + 2x) X`. -/
def eX (X : ZSeq) : ZSeq := fun k => X k + 2 * X (k - 1)

/-! ## Helper lemmas -/

/-- An interval-supported sequence is nonnegative everywhere. -/
theorem IntervalSupport.nonneg {a : ZSeq} {d : ℕ} (h : IntervalSupport a d) (k : ℤ) :
    0 ≤ a k := by
  by_cases h0 : k < 0
  · rw [h.zero_neg k h0]
  by_cases h1 : (d : ℤ) < k
  · rw [h.zero_gt k h1]
  exact le_of_lt (h.pos k (by omega) (by omega))

/-- Where an interval-supported sequence is not positive, the index lies outside `[0, d]`. -/
theorem IntervalSupport.out_of_not_pos {a : ZSeq} {d : ℕ} (h : IntervalSupport a d) {k : ℤ}
    (hk : ¬ 0 < a k) : k < 0 ∨ (d : ℤ) < k := by
  by_contra hc
  push_neg at hc
  exact hk (h.pos k hc.1 hc.2)

/-- Dividing a weighted inequality by a positive weight: from `0 < c` and `c * w = s ≥ 0`,
`w ≥ 0`. -/
theorem nonneg_of_weighted {c w s : ℤ} (hc : 0 < c) (h : c * w = s) (hs : 0 ≤ s) : 0 ≤ w :=
  (mul_nonneg_iff_of_pos_left hc).mp (by rw [h]; exact hs)

/-- Lemma 1 as an identity: `a_k K(a)_k = a_{k-1} D(a)_k + a_{k+1} D(a)_{k-1}`. -/
theorem K_identity (a : ZSeq) (k : ℤ) :
    a k * K a k = a (k - 1) * D a k + a (k + 1) * D a (k - 1) := by
  simp only [K, D]
  ring_nf

/-- Lemma 1 (shifted self-synchronisation): a log-concave sequence with interval support has
`K a ≥ 0` everywhere. -/
theorem K_nonneg {a : ZSeq} {d : ℕ} (ha : IntervalSupport a d) (hD : ∀ k, 0 ≤ D a k) (k : ℤ) :
    0 ≤ K a k := by
  have hn := ha.nonneg
  by_cases hk0 : k < 0
  · simp only [K]
    rw [ha.zero_neg k hk0, ha.zero_neg (k - 2) (by omega)]
    simp
  by_cases hk1 : (d : ℤ) < k
  · simp only [K]
    rw [ha.zero_gt k hk1, ha.zero_gt (k + 1) (by omega)]
    simp
  have hpos : 0 < a k := ha.pos k (by omega) (by omega)
  refine nonneg_of_weighted hpos (K_identity a k) ?_
  have := hn (k - 1); have := hn (k + 1); have := hD k; have := hD (k - 1)
  positivity

/-! ## Degree facts and supports -/

/-- Degree facts: `d ≤ e ≤ d + 1`. -/
theorem P.deg {Z X : ZSeq} (h : P Z X) {d e : ℕ} (hX : IntervalSupport X d)
    (hZ : IntervalSupport Z e) : d ≤ e ∧ e ≤ d + 1 := by
  constructor
  · by_contra hlt
    push_neg at hlt
    have h1 := hX.pos d (Nat.cast_nonneg d) le_rfl
    have h2 := hZ.zero_gt d (by exact_mod_cast hlt)
    have h3 := h.R d
    linarith
  · by_contra hlt
    push_neg at hlt
    have h1 := hZ.pos e (Nat.cast_nonneg e) le_rfl
    have h2 := hX.zero_gt e (by omega)
    have h3 := hX.zero_gt (e - 1) (by omega)
    have h4 := h.U e
    linarith

/-- `U` at `k - 1`, with the index normalised. -/
theorem P.U_pred {Z X : ZSeq} (h : P Z X) (k : ℤ) : 0 ≤ X (k - 1) + X (k - 2) - Z (k - 1) := by
  have := h.U (k - 1)
  rwa [show k - 1 - 1 = k - 2 by ring] at this

/-- Support of `Z + x X`. -/
theorem supp_addShift {Z X : ZSeq} {d e : ℕ} (hZ : IntervalSupport Z e)
    (hX : IntervalSupport X d) (hed : e ≤ d + 1) : IntervalSupport (addShift Z X) (d + 1) := by
  have hXn := hX.nonneg
  have hZn := hZ.nonneg
  refine ⟨fun k hk0 hk1 => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · simp only [addShift]
    rcases eq_or_lt_of_le hk0 with h0 | h0
    · subst h0
      have := hZ.pos 0 le_rfl (Nat.cast_nonneg e)
      have := hXn (0 - 1)
      linarith
    · have := hX.pos (k - 1) (by omega) (by omega)
      have := hZn k
      linarith
  · simp only [addShift]
    rw [hZ.zero_neg k hk, hX.zero_neg (k - 1) (by omega)]
    simp
  · simp only [addShift]
    rw [hZ.zero_gt k (by omega), hX.zero_gt (k - 1) (by omega)]
    simp

/-- Support of `(1 + x) Z + x X`. -/
theorem supp_eZ {Z X : ZSeq} {d e : ℕ} (hZ : IntervalSupport Z e)
    (hX : IntervalSupport X d) (hde : d ≤ e) : IntervalSupport (eZ Z X) (e + 1) := by
  have hXn := hX.nonneg
  have hZn := hZ.nonneg
  refine ⟨fun k hk0 hk1 => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · simp only [eZ]
    rcases eq_or_lt_of_le hk0 with h0 | h0
    · subst h0
      have := hZ.pos 0 le_rfl (Nat.cast_nonneg e)
      have := hZn (0 - 1)
      have := hXn (0 - 1)
      linarith
    · have := hZ.pos (k - 1) (by omega) (by omega)
      have := hZn k
      have := hXn (k - 1)
      linarith
  · simp only [eZ]
    rw [hZ.zero_neg k hk, hZ.zero_neg (k - 1) (by omega), hX.zero_neg (k - 1) (by omega)]
    simp
  · simp only [eZ]
    rw [hZ.zero_gt k (by omega), hZ.zero_gt (k - 1) (by omega), hX.zero_gt (k - 1) (by omega)]
    simp

/-- Support of `(1 + 2x) X`. -/
theorem supp_eX {X : ZSeq} {d : ℕ} (hX : IntervalSupport X d) : IntervalSupport (eX X) (d + 1) := by
  have hXn := hX.nonneg
  refine ⟨fun k hk0 hk1 => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · simp only [eX]
    rcases eq_or_lt_of_le hk0 with h0 | h0
    · subst h0
      have := hX.pos 0 le_rfl (Nat.cast_nonneg d)
      have := hXn (0 - 1)
      linarith
    · have := hX.pos (k - 1) (by omega) (by omega)
      have := hXn k
      linarith
  · simp only [eX]
    rw [hX.zero_neg k hk, hX.zero_neg (k - 1) (by omega)]
    simp
  · simp only [eX]
    rw [hX.zero_gt k (by omega), hX.zero_gt (k - 1) (by omega)]
    simp

/-! ## Exact identities -/

/-- `D(Z + x X)_k = D(Z)_k + D(X)_{k-1} + W(Z, x X)_k` (letters `S`, `L`). -/
theorem D_addShift (Z X : ZSeq) (k : ℤ) :
    D (addShift Z X) k = D Z k + D X (k - 1) + W Z (shift X) k := by
  simp only [D, W, shift, addShift]
  ring_nf

/-- Letter `S`: `W(Z + x X, Z)_k = 2 D(Z)_k + W(Z, x X)_k`. -/
theorem W_S0 (Z X : ZSeq) (k : ℤ) :
    W (addShift Z X) Z k = 2 * D Z k + W Z (shift X) k := by
  simp only [D, W, shift, addShift]
  ring_nf

/-- Letter `S`: `W(Z + x X, x Z)_k = K(Z)_k + W(Z, X)_{k-1}`. -/
theorem W_S1 (Z X : ZSeq) (k : ℤ) :
    W (addShift Z X) (shift Z) k = K Z k + W Z X (k - 1) := by
  simp only [W, K, shift, addShift]
  ring_nf

/-- Letter `L`: `D((1 + x) X)_k = D(X)_k + D(X)_{k-1} + K(X)_k`. -/
theorem D_onePlusX (X : ZSeq) (k : ℤ) :
    D (onePlusX X) k = D X k + D X (k - 1) + K X k := by
  simp only [D, K, onePlusX]
  ring_nf

/-- Letter `L`: `W(Z + x X, (1 + x) X)_k = W(Z,X)_k + W(Z, x X)_k + K(X)_k + 2 D(X)_{k-1}`. -/
theorem W_L0 (Z X : ZSeq) (k : ℤ) :
    W (addShift Z X) (onePlusX X) k = W Z X k + W Z (shift X) k + K X k + 2 * D X (k - 1) := by
  simp only [D, W, K, shift, addShift, onePlusX]
  ring_nf

/-- Letter `L`, weighted identity for `W(Z + x X, x (1 + x) X)`. -/
theorem W_L1_weighted (Z X : ZSeq) (k : ℤ) :
    X (k - 1) * W (addShift Z X) (shift (onePlusX X)) k =
      (X (k - 1) + X (k - 2)) * W Z (shift X) k
        + (X (k - 1) + (X (k - 1) + X (k - 2) - Z (k - 1))) * D X (k - 1)
        + (Z (k + 1) + X k) * D X (k - 2) := by
  simp only [D, W, shift, addShift, onePlusX]
  ring_nf

/-- Letter `L`, `W(Z + x X, x (1 + x) X)` expanded with normalised indices. -/
theorem W_L1_expand (Z X : ZSeq) (k : ℤ) :
    W (addShift Z X) (shift (onePlusX X)) k =
      2 * ((Z k + X (k - 1)) * (X (k - 1) + X (k - 2)))
        - (Z (k - 1) + X (k - 2)) * (X k + X (k - 1))
        - (Z (k + 1) + X k) * (X (k - 2) + X (k - 3)) := by
  simp only [W, shift, addShift, onePlusX]
  ring_nf

/-- Letter `E`: `D((1 + x) Z + x X)_k`. -/
theorem D_eZ (Z X : ZSeq) (k : ℤ) :
    D (eZ Z X) k = D Z k + D Z (k - 1) + D X (k - 1) + W Z (shift X) k + K Z k
      + W Z X (k - 1) := by
  simp only [D, W, K, shift, eZ]
  ring_nf

/-- Letter `E`: `D((1 + 2x) X)_k = D(X)_k + 4 D(X)_{k-1} + 2 K(X)_k`. -/
theorem D_eX (X : ZSeq) (k : ℤ) :
    D (eX X) k = D X k + 4 * D X (k - 1) + 2 * K X k := by
  simp only [D, K, eX]
  ring_nf

/-- Letter `E`, weighted identity for `W((1 + x) Z + x X, (1 + 2x) X)`. -/
theorem W_E0_weighted (Z X : ZSeq) (k : ℤ) :
    X (k - 1) * W (eZ Z X) (eX X) k =
      (Z (k - 2) + X (k - 2)) * D X k
        + (3 * X (k - 1) + (X k + X (k - 1) - Z k)) * D X (k - 1)
        + (X k + 2 * X (k - 1)) * W Z X (k - 1) + X (k - 1) * W Z X k
        + 2 * X (k - 1) * W Z (shift X) k := by
  simp only [D, W, shift, eZ, eX]
  ring_nf

/-- Letter `E`, `W((1 + x) Z + x X, (1 + 2x) X)` expanded with normalised indices. -/
theorem W_E0_expand (Z X : ZSeq) (k : ℤ) :
    W (eZ Z X) (eX X) k =
      2 * ((Z k + Z (k - 1) + X (k - 1)) * (X k + 2 * X (k - 1)))
        - (Z (k - 1) + Z (k - 2) + X (k - 2)) * (X (k + 1) + 2 * X k)
        - (Z (k + 1) + Z k + X k) * (X (k - 1) + 2 * X (k - 2)) := by
  simp only [W, eZ, eX]
  ring_nf

/-- Letter `E`, weighted identity for `W((1 + x) Z + x X, x (1 + 2x) X)`. -/
theorem W_E1_weighted (Z X : ZSeq) (k : ℤ) :
    X (k - 1) * W (eZ Z X) (shift (eX X)) k =
      (X (k - 1) + 2 * X (k - 2)) * W Z (shift X) k + X (k - 1) * W Z X (k - 1)
        + 2 * X (k - 1) * W Z (shift X) (k - 1)
        + 2 * (X (k - 1) + X (k - 2) - Z (k - 1)) * D X (k - 1)
        + 2 * (Z (k + 1) + X k) * D X (k - 2) := by
  simp only [D, W, shift, eZ, eX]
  ring_nf

/-- Letter `E`, `W((1 + x) Z + x X, x (1 + 2x) X)` expanded with normalised indices. -/
theorem W_E1_expand (Z X : ZSeq) (k : ℤ) :
    W (eZ Z X) (shift (eX X)) k =
      2 * ((Z k + Z (k - 1) + X (k - 1)) * (X (k - 1) + 2 * X (k - 2)))
        - (Z (k - 1) + Z (k - 2) + X (k - 2)) * (X k + 2 * X (k - 1))
        - (Z (k + 1) + Z k + X k) * (X (k - 2) + 2 * X (k - 3)) := by
  simp only [W, shift, eZ, eX]
  ring_nf

/-! ## The letters preserve `P` -/

/-- Letter `S` preserves `P`. -/
theorem P.S {Z X : ZSeq} (h : P Z X) : P (addShift Z X) Z := by
  obtain ⟨d, hX⟩ := h.suppX
  obtain ⟨e, hZ⟩ := h.suppZ
  obtain ⟨-, hed⟩ := h.deg hX hZ
  have hXn := hX.nonneg
  have hKZ := K_nonneg hZ h.DZ
  refine ⟨⟨e, hZ⟩, ⟨d + 1, supp_addShift hZ hX hed⟩, ?_, fun k => ?_, fun k => ?_,
    fun k => ?_, h.DZ, fun k => ?_, fun k => ?_⟩
  · have := hX.zero_neg (0 - 1) (by norm_num)
    simp only [addShift]
    linarith
  · simp only [addShift]
    have := hXn (k - 1)
    linarith
  · simp only [addShift]
    have := h.R (k - 1)
    linarith
  · rw [D_addShift]
    have := h.DZ k; have := h.DX (k - 1); have := h.W1 k
    linarith
  · rw [W_S0]
    have := h.DZ k; have := h.W1 k
    linarith
  · rw [W_S1]
    have := hKZ k; have := h.W0 (k - 1)
    linarith

/-- Letter `L` preserves `P`. -/
theorem P.L {Z X : ZSeq} (h : P Z X) : P (addShift Z X) (onePlusX X) := by
  obtain ⟨d, hX⟩ := h.suppX
  obtain ⟨e, hZ⟩ := h.suppZ
  obtain ⟨-, hed⟩ := h.deg hX hZ
  have hXn := hX.nonneg
  have hZn := hZ.nonneg
  have hKX := K_nonneg hX h.DX
  refine ⟨⟨d + 1, supp_addShift hX hX (by omega)⟩, ⟨d + 1, supp_addShift hZ hX hed⟩, ?_,
    fun k => ?_, fun k => ?_, fun k => ?_, fun k => ?_, fun k => ?_, fun k => ?_⟩
  · simp only [addShift, onePlusX]
    rw [h.const]
  · simp only [addShift, onePlusX]
    have := h.R k
    linarith
  · simp only [addShift, onePlusX]
    have := h.U k; have := hXn (k - 1 - 1)
    linarith
  · rw [D_addShift]
    have := h.DZ k; have := h.DX (k - 1); have := h.W1 k
    linarith
  · rw [D_onePlusX]
    have := h.DX k; have := h.DX (k - 1); have := hKX k
    linarith
  · rw [W_L0]
    have := h.W0 k; have := h.W1 k; have := hKX k; have := h.DX (k - 1)
    linarith
  · by_cases hk : 0 < X (k - 1)
    · refine nonneg_of_weighted hk (W_L1_weighted Z X k) ?_
      have := hXn (k - 1); have := hXn (k - 2); have := hXn k; have := hZn (k + 1)
      have := h.W1 k; have := h.DX (k - 1); have := h.DX (k - 2); have := h.U_pred k
      positivity
    · rw [W_L1_expand]
      rcases hX.out_of_not_pos hk with hk' | hk'
      · simp only [hX.zero_neg (k - 1) hk', hX.zero_neg (k - 2) (by omega),
          hX.zero_neg (k - 3) (by omega), hZ.zero_neg (k - 1) (by omega)]
        simp
      · simp only [hX.zero_gt (k - 1) hk', hX.zero_gt k (by omega), hZ.zero_gt k (by omega),
          hZ.zero_gt (k + 1) (by omega)]
        simp

/-- Letter `E` preserves `P`. -/
theorem P.E {Z X : ZSeq} (h : P Z X) : P (eZ Z X) (eX X) := by
  obtain ⟨d, hX⟩ := h.suppX
  obtain ⟨e, hZ⟩ := h.suppZ
  obtain ⟨hde, hed⟩ := h.deg hX hZ
  have hXn := hX.nonneg
  have hZn := hZ.nonneg
  have hKX := K_nonneg hX h.DX
  have hKZ := K_nonneg hZ h.DZ
  refine ⟨⟨d + 1, supp_eX hX⟩, ⟨e + 1, supp_eZ hZ hX hde⟩, ?_,
    fun k => ?_, fun k => ?_, fun k => ?_, fun k => ?_, fun k => ?_, fun k => ?_⟩
  · have h1 := hX.zero_neg (0 - 1) (by norm_num)
    have h2 := hZ.zero_neg (0 - 1) (by norm_num)
    simp only [eZ, eX]
    rw [h1, h2, h.const]
    ring
  · simp only [eZ, eX]
    have := h.R k; have := h.R (k - 1)
    linarith
  · simp only [eZ, eX]
    have := h.U k; have := h.U (k - 1); have := hXn (k - 1 - 1)
    linarith
  · rw [D_eZ]
    have := h.DZ k; have := h.DZ (k - 1); have := h.DX (k - 1); have := h.W1 k
    have := hKZ k; have := h.W0 (k - 1)
    linarith
  · rw [D_eX]
    have := h.DX k; have := h.DX (k - 1); have := hKX k
    linarith
  · by_cases hk : 0 < X (k - 1)
    · refine nonneg_of_weighted hk (W_E0_weighted Z X k) ?_
      have := hXn (k - 1); have := hXn (k - 2); have := hXn k; have := hZn (k - 2)
      have := h.W0 k; have := h.W0 (k - 1); have := h.W1 k
      have := h.DX k; have := h.DX (k - 1); have := h.U k
      positivity
    · rw [W_E0_expand]
      rcases hX.out_of_not_pos hk with hk' | hk'
      · have := hZn k; have := hXn k
        simp only [hX.zero_neg (k - 1) hk', hX.zero_neg (k - 2) (by omega),
          hZ.zero_neg (k - 1) (by omega), hZ.zero_neg (k - 2) (by omega)]
        simp only [add_zero, mul_zero, zero_mul, sub_zero]
        positivity
      · simp only [hX.zero_gt (k - 1) hk', hX.zero_gt k (by omega), hX.zero_gt (k + 1) (by omega),
          hZ.zero_gt k (by omega), hZ.zero_gt (k + 1) (by omega)]
        simp
  · by_cases hk : 0 < X (k - 1)
    · refine nonneg_of_weighted hk (W_E1_weighted Z X k) ?_
      have := hXn (k - 1); have := hXn (k - 2); have := hXn k; have := hZn (k + 1)
      have := h.W0 (k - 1); have := h.W1 k; have := h.W1 (k - 1)
      have := h.DX (k - 1); have := h.DX (k - 2); have := h.U_pred k
      positivity
    · rw [W_E1_expand]
      rcases hX.out_of_not_pos hk with hk' | hk'
      · simp only [hX.zero_neg (k - 1) hk', hX.zero_neg (k - 2) (by omega),
          hX.zero_neg (k - 3) (by omega), hZ.zero_neg (k - 1) (by omega),
          hZ.zero_neg (k - 2) (by omega)]
        simp
      · have := hZn (k - 1); have := hXn (k - 2)
        simp only [hX.zero_gt (k - 1) hk', hX.zero_gt k (by omega), hZ.zero_gt k (by omega),
          hZ.zero_gt (k + 1) (by omega)]
        simp only [add_zero, zero_add, mul_zero, zero_mul, sub_zero]
        positivity

/-- The single vertex, rooted at itself: `Z = 1 + x`, `X = 1`, satisfies `P`. -/
theorem P.single :
    P (fun k => if k = 0 ∨ k = 1 then 1 else 0) (fun k => if k = 0 then 1 else 0) := by
  refine ⟨⟨0, fun k hk0 hk1 => ?_, fun k hk => ?_, fun k hk => ?_⟩,
    ⟨1, fun k hk0 hk1 => ?_, fun k hk => ?_, fun k hk => ?_⟩, by simp,
    fun k => ?_, fun k => ?_, fun k => ?_, fun k => ?_, fun k => ?_, fun k => ?_⟩ <;>
  (try simp only [D, W, shift]) <;>
  split_ifs <;> omega

end Erdos993Lean.PropertyP
