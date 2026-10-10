module

public import Mathlib
public import Erdos993Lean.Sequences

/-!
# Log-concavity is preserved by convolution (Hoggar 1974)

The Cauchy product of two finitely supported log-concave sequences of natural numbers with no
internal zeros is log-concave and has no internal zeros.  This is a classical theorem
(S. G. Hoggar, J. Combin. Theory Ser. B 16 (1974) 248–254); the package uses it for forests
(the independence polynomial of a disjoint union is the product of the components' polynomials).

The proof is the Toeplitz / 2×2 Cauchy–Binet argument.


This file proves the log-concavity statement `logConcave_cauchyProduct`.  Finite support is not
needed for it (every coefficient of the product is a finite sum); the hypotheses are kept in the
statement for the package's interface.

## Structure (all internal material lives in `Erdos993Lean.Hoggar`)

* `Hoggar.TN2 a`: every 2×2 minor of the lower-triangular Toeplitz matrix `(a (u - r))_{u, r}`
  is nonnegative.
* `Hoggar.TN2_conv`: TN2 is closed under convolution, by the finite 2×2 Cauchy–Binet identity
  `Hoggar.minorConvCauchyBinet_all`.
* `Hoggar.tn2_of_logConcave`: a log-concave `ℕ`-sequence with no internal zeros is TN2 (as an
  integer sequence), via the cross inequality `a i * a (i + d + e) ≤ a (i + d) * a (i + e)`.
* `Hoggar.TN2.logConcave`: the `(0, 1) × (k + 1, k + 2)` minor is the log-concavity defect.
-/

@[expose] public section

namespace Erdos993Lean

/-- The Cauchy product (convolution) of two sequences. -/
def cauchyProduct (a b : ℕ → ℕ) : ℕ → ℕ :=
  fun k => ∑ i ∈ Finset.range (k + 1), a i * b (k - i)

namespace Hoggar

/-! ### Toeplitz minors and the 2×2 Cauchy–Binet identity

The definitions and lemmas `subAt`, `TN2`, `conv`, `subAt_conv_as_sum_u`,
`subAt_conv_as_sum_bound`, `cb2xN_cross_expand`, `cauchyBinet2xN`, `minorConvCauchyBinet_all`,
`TN2_mul`, `toeplitz_TN2_to_logConcave`, with the Cauchy–Binet hypothesis of `TN2_mul`
discharged internally. -/

/-- Integer-valued sequences. -/
abbrev Seq := ℕ → ℤ

/-- Toeplitz entry: `subAt a u r = a (u - r)` if `r ≤ u`, else `0`. -/
def subAt (a : Seq) (u r : ℕ) : ℤ := if r ≤ u then a (u - r) else 0

/-- All 2×2 minors of the lower-triangular Toeplitz matrix `(subAt a u r)_{u, r}` are
nonnegative (rows `u < v`, columns `r < s`). -/
def TN2 (a : Seq) : Prop :=
  ∀ r s u v : ℕ, r < s → u < v →
    0 ≤ subAt a u r * subAt a v s - subAt a u s * subAt a v r

/-- Convolution of integer sequences. -/
def conv (a b : Seq) : Seq :=
  fun k => ∑ i ∈ Finset.range (k + 1), a i * subAt b k i

lemma conv_coeff (a b : Seq) (k : ℕ) :
    conv a b k = ∑ i ∈ Finset.range (k + 1), a i * subAt b k i := by
  rfl

lemma subAt_eq_coeff_of_le (a : Seq) (u r : ℕ) (hru : r ≤ u) :
    subAt a u r = a (u - r) := by
  simp [subAt, hru]

lemma subAt_eq_zero_of_lt (a : Seq) (u r : ℕ) (hur : u < r) :
    subAt a u r = 0 := by
  simp [subAt, Nat.not_le.mpr hur]

/-- The finite 2×2 Cauchy–Binet identity for the Toeplitz minors of a convolution. -/
def MinorConvCauchyBinet (a b : Seq) : Prop :=
  ∀ r s u v : ℕ,
    subAt (conv a b) u r * subAt (conv a b) v s -
      subAt (conv a b) u s * subAt (conv a b) v r
      =
    ∑ p ∈ Finset.range (u + v + 2), ∑ q ∈ Finset.range (u + v + 2),
      (if p < q then
        (subAt a p r * subAt a q s - subAt a p s * subAt a q r) *
        (subAt b u p * subAt b v q - subAt b u q * subAt b v p)
       else 0)

lemma subAt_conv_as_sum_u (a b : Seq) (u r : ℕ) :
    subAt (conv a b) u r =
      ∑ p ∈ Finset.range (u + 1), subAt a p r * subAt b u p := by
  by_cases hru : r ≤ u
  · rw [subAt_eq_coeff_of_le (a := conv a b) (u := u) (r := r) hru]
    rw [conv_coeff]
    have hsplit := Finset.sum_range_add
      (f := fun p => subAt a p r * subAt b u p) r (u + 1 - r)
    have hr_add : r + (u + 1 - r) = u + 1 := by
      exact Nat.add_sub_of_le (Nat.le_trans hru (Nat.le_succ u))
    rw [hr_add] at hsplit
    rw [hsplit]
    have hleft_zero :
        ∑ x ∈ Finset.range r, subAt a x r * subAt b u x = 0 := by
      refine Finset.sum_eq_zero ?_
      intro x hx
      have hxr : x < r := Finset.mem_range.mp hx
      have hsub : subAt a x r = 0 := subAt_eq_zero_of_lt (a := a) (u := x) (r := r) hxr
      simp [hsub]
    rw [hleft_zero, zero_add]
    have hlen : u + 1 - r = u - r + 1 := by omega
    rw [hlen]
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hi_le : i ≤ u - r := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hri_le_u : r + i ≤ u := by
      calc
        r + i ≤ r + (u - r) := Nat.add_le_add_left hi_le r
        _ = u := Nat.add_sub_of_le hru
    have hri_ge_r : r ≤ r + i := Nat.le_add_right r i
    have hsubA : subAt a (r + i) r = a i := by
      rw [subAt_eq_coeff_of_le (a := a) (u := r + i) (r := r) hri_ge_r]
      simp
    have hsubB : subAt b u (r + i) = subAt b (u - r) i := by
      rw [subAt_eq_coeff_of_le (a := b) (u := u) (r := r + i) hri_le_u]
      rw [subAt_eq_coeff_of_le (a := b) (u := u - r) (r := i) hi_le]
      have : u - (r + i) = (u - r) - i := by
        omega
      simp [this]
    simp [hsubA, hsubB]
  · have hur : u < r := Nat.lt_of_not_ge hru
    have hL : subAt (conv a b) u r = 0 :=
      subAt_eq_zero_of_lt (a := conv a b) (u := u) (r := r) hur
    rw [hL]
    symm
    refine Finset.sum_eq_zero ?_
    intro p hp
    have hp_le : p ≤ u := Nat.le_of_lt_succ (Finset.mem_range.mp hp)
    have hp_lt_r : p < r := lt_of_le_of_lt hp_le hur
    have hAp : subAt a p r = 0 := subAt_eq_zero_of_lt (a := a) (u := p) (r := r) hp_lt_r
    simp [hAp]

lemma subAt_conv_as_sum_bound (a b : Seq) (u r N : ℕ) (huN : u + 1 ≤ N) :
    subAt (conv a b) u r =
      ∑ p ∈ Finset.range N, subAt a p r * subAt b u p := by
  let f : ℕ → ℤ := fun p => subAt a p r * subAt b u p
  have hbase : subAt (conv a b) u r = ∑ p ∈ Finset.range (u + 1), f p := by
    simpa [f] using subAt_conv_as_sum_u a b u r
  have hsplit :
      ∑ p ∈ Finset.range N, f p =
        (∑ p ∈ Finset.range (u + 1), f p) +
        (∑ t ∈ Finset.range (N - (u + 1)), f (u + 1 + t)) := by
    have h := Finset.sum_range_add (f := f) (u + 1) (N - (u + 1))
    have hN : (u + 1) + (N - (u + 1)) = N := Nat.add_sub_of_le huN
    rw [hN] at h
    exact h
  have htail_zero : ∑ t ∈ Finset.range (N - (u + 1)), f (u + 1 + t) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro t ht
    have hu_lt : u < u + 1 + t := by omega
    have hBzero : subAt b u (u + 1 + t) = 0 :=
      subAt_eq_zero_of_lt (a := b) (u := u) (r := u + 1 + t) hu_lt
    simp [f, hBzero]
  have hsumN : ∑ p ∈ Finset.range N, f p = ∑ p ∈ Finset.range (u + 1), f p := by
    rw [hsplit, htail_zero, add_zero]
  exact hbase.trans hsumN.symm

lemma cb2xN_cross_expand
    (n : ℕ) (x y u v : ℕ → ℤ) :
    (∑ p ∈ Finset.range n, x p * u p) * (y n * v n) +
      (x n * u n) * (∑ q ∈ Finset.range n, y q * v q) -
      (∑ p ∈ Finset.range n, y p * u p) * (x n * v n) -
      (y n * u n) * (∑ q ∈ Finset.range n, x q * v q)
    =
    ∑ p ∈ Finset.range n,
      (x p * y n - y p * x n) * (u p * v n - u n * v p) := by
  calc
    (∑ p ∈ Finset.range n, x p * u p) * (y n * v n) +
        (x n * u n) * (∑ q ∈ Finset.range n, y q * v q) -
        (∑ p ∈ Finset.range n, y p * u p) * (x n * v n) -
        (y n * u n) * (∑ q ∈ Finset.range n, x q * v q)
      =
        (∑ p ∈ Finset.range n,
          ((x p * u p) * (y n * v n) + (x n * u n) * (y p * v p) -
            (y p * u p) * (x n * v n) - (y n * u n) * (x p * v p))) := by
          simp [Finset.mul_sum, Finset.sum_mul, Finset.sum_add_distrib,
            sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    _ = ∑ p ∈ Finset.range n,
          (x p * y n - y p * x n) * (u p * v n - u n * v p) := by
          refine Finset.sum_congr rfl ?_
          intro p hp
          ring

/-- The 2×n Cauchy–Binet identity, written with an explicit `p < q` guard. -/
lemma cauchyBinet2xN
    (n : ℕ)
    (x y u v : ℕ → ℤ) :
    (∑ p ∈ Finset.range n, x p * u p) *
        (∑ q ∈ Finset.range n, y q * v q) -
      (∑ p ∈ Finset.range n, y p * u p) *
        (∑ q ∈ Finset.range n, x q * v q)
    =
    ∑ p ∈ Finset.range n, ∑ q ∈ Finset.range n,
      (if p < q then
        (x p * y q - y p * x q) * (u p * v q - u q * v p)
       else (0 : ℤ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      let XU : ℤ := ∑ p ∈ Finset.range n, x p * u p
      let YV : ℤ := ∑ q ∈ Finset.range n, y q * v q
      let YU : ℤ := ∑ p ∈ Finset.range n, y p * u p
      let XV : ℤ := ∑ q ∈ Finset.range n, x q * v q
      let Cross : ℤ := ∑ p ∈ Finset.range n,
        (x p * y n - y p * x n) * (u p * v n - u n * v p)

      have hIH : XU * YV - YU * XV =
          ∑ p ∈ Finset.range n, ∑ q ∈ Finset.range n,
            (if p < q then
              (x p * y q - y p * x q) * (u p * v q - u q * v p)
             else (0 : ℤ)) := by
        simpa [XU, YV, YU, XV] using ih

      have hRHSsplit :
          (∑ p ∈ Finset.range (n + 1), ∑ q ∈ Finset.range (n + 1),
              (if p < q then
                (x p * y q - y p * x q) * (u p * v q - u q * v p)
               else (0 : ℤ)))
          =
          (∑ p ∈ Finset.range n, ∑ q ∈ Finset.range n,
              (if p < q then
                (x p * y q - y p * x q) * (u p * v q - u q * v p)
               else (0 : ℤ)))
          + Cross := by
        rw [Finset.sum_range_succ]
        have hpn :
            ∑ q ∈ Finset.range (n + 1),
              (if n < q then
                (x n * y q - y n * x q) * (u n * v q - u q * v n)
               else (0 : ℤ)) = 0 := by
          refine Finset.sum_eq_zero ?_
          intro q hq
          have hq_le : q ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hq)
          have hnot : ¬ n < q := not_lt_of_ge hq_le
          simp [hnot]
        rw [hpn, add_zero]
        have hinner :
            ∀ p ∈ Finset.range n,
              (∑ q ∈ Finset.range (n + 1),
                  (if p < q then (x p * y q - y p * x q) * (u p * v q - u q * v p)
                    else (0 : ℤ)))
                =
              (∑ q ∈ Finset.range n,
                  (if p < q then (x p * y q - y p * x q) * (u p * v q - u q * v p)
                    else (0 : ℤ)))
                + (x p * y n - y p * x n) * (u p * v n - u n * v p) := by
          intro p hp
          rw [Finset.sum_range_succ]
          have hp_lt_n : p < n := Finset.mem_range.mp hp
          simp [hp_lt_n]
        refine (Finset.sum_congr rfl hinner).trans ?_
        simp [Cross, Finset.sum_add_distrib]

      have hCross :
          XU * (y n * v n) + (x n * u n) * YV - YU * (x n * v n) - (y n * u n) * XV
            = Cross := by
        simpa [XU, YV, YU, XV, Cross] using cb2xN_cross_expand n x y u v

      calc
        (∑ p ∈ Finset.range (n + 1), x p * u p) *
            (∑ q ∈ Finset.range (n + 1), y q * v q) -
          (∑ p ∈ Finset.range (n + 1), y p * u p) *
            (∑ q ∈ Finset.range (n + 1), x q * v q)
            =
          (XU * YV - YU * XV) +
            (XU * (y n * v n) + (x n * u n) * YV - YU * (x n * v n) - (y n * u n) * XV) := by
              simp [XU, YV, YU, XV, Finset.sum_range_succ]
              ring
        _ = (XU * YV - YU * XV) + Cross := by rw [hCross]
        _ =
          (∑ p ∈ Finset.range n, ∑ q ∈ Finset.range n,
              (if p < q then
                (x p * y q - y p * x q) * (u p * v q - u q * v p)
               else (0 : ℤ))) + Cross := by rw [hIH]
        _ =
          (∑ p ∈ Finset.range (n + 1), ∑ q ∈ Finset.range (n + 1),
              (if p < q then
                (x p * y q - y p * x q) * (u p * v q - u q * v p)
               else (0 : ℤ))) := by
              exact hRHSsplit.symm

theorem minorConvCauchyBinet_all (a b : Seq) : MinorConvCauchyBinet a b := by
  intro r s u v
  let N : ℕ := u + v + 2
  have huN : u + 1 ≤ N := by
    dsimp [N]
    omega
  have hvN : v + 1 ≤ N := by
    dsimp [N]
    omega
  have hur : subAt (conv a b) u r =
      ∑ p ∈ Finset.range N, subAt a p r * subAt b u p :=
    subAt_conv_as_sum_bound a b u r N huN
  have hvs : subAt (conv a b) v s =
      ∑ p ∈ Finset.range N, subAt a p s * subAt b v p :=
    subAt_conv_as_sum_bound a b v s N hvN
  have hus : subAt (conv a b) u s =
      ∑ p ∈ Finset.range N, subAt a p s * subAt b u p :=
    subAt_conv_as_sum_bound a b u s N huN
  have hvr : subAt (conv a b) v r =
      ∑ p ∈ Finset.range N, subAt a p r * subAt b v p :=
    subAt_conv_as_sum_bound a b v r N hvN
  rw [hur, hvs, hus, hvr]
  simpa [N] using
    cauchyBinet2xN N
      (fun p => subAt a p r)
      (fun p => subAt a p s)
      (fun p => subAt b u p)
      (fun p => subAt b v p)

/-- TN2 is closed under convolution. -/
theorem TN2_conv (a b : Seq) (ha : TN2 a) (hb : TN2 b) : TN2 (conv a b) := by
  intro r s u v hrs huv
  have hsum := minorConvCauchyBinet_all a b r s u v
  have hnonneg :
      0 ≤
        ∑ p ∈ Finset.range (u + v + 2), ∑ q ∈ Finset.range (u + v + 2),
          (if p < q then
            (subAt a p r * subAt a q s - subAt a p s * subAt a q r) *
            (subAt b u p * subAt b v q - subAt b u q * subAt b v p)
           else 0) := by
    refine Finset.sum_nonneg ?_
    intro p hp
    refine Finset.sum_nonneg ?_
    intro q hq
    by_cases hpq : p < q
    · have hA : 0 ≤ subAt a p r * subAt a q s - subAt a p s * subAt a q r :=
        ha r s p q hrs hpq
      have hB : 0 ≤ subAt b u p * subAt b v q - subAt b u q * subAt b v p :=
        hb p q u v hpq huv
      simpa [hpq] using mul_nonneg hA hB
    · simp [hpq]
  linarith [hsum, hnonneg]

/-- The `(0, 1) × (k + 1, k + 2)` Toeplitz minor of a TN2 sequence is its log-concavity defect
at `k + 1` (`toeplitz_TN2_to_logConcave` in `CoreTN2.lean`). -/
lemma TN2.logConcave {c : Seq} (hc : TN2 c) (k : ℕ) :
    c k * c (k + 2) ≤ c (k + 1) * c (k + 1) := by
  have h := hc 0 1 (k + 1) (k + 2) Nat.zero_lt_one (Nat.lt_succ_self _)
  simp [subAt] at h
  linarith

/-! ### Log-concavity with no internal zeros implies TN2

A two-step argument (adjacent cross terms, then the cross gap),
proved directly for `ℕ`-valued sequences. -/

section Bridge

variable {a : ℕ → ℕ}

/-- Adjacent cross inequality: `a i * a (i + e + 1) ≤ a (i + 1) * a (i + e)`. -/
lemma adj_cross (hlc : LogConcave a) (hnz : NoInternalZeros a) (i : ℕ) :
    ∀ e, a i * a (i + e + 1) ≤ a (i + 1) * a (i + e) := by
  intro e
  induction e with
  | zero => simp [Nat.mul_comm]
  | succ e ih =>
    have e1 : i + (e + 1) + 1 = i + e + 2 := by omega
    have e2 : i + (e + 1) = i + e + 1 := by omega
    rw [e1, e2]
    by_cases h0 : a i = 0
    · simp [h0]
    by_cases h1 : a (i + e + 2) = 0
    · simp [h1]
    have hpos : 0 < a (i + e + 1) :=
      Nat.pos_of_ne_zero (hnz i (i + e + 1) (i + e + 2) (by omega) (by omega) h0 h1)
    have hlc' : a (i + e) * a (i + e + 2) ≤ a (i + e + 1) * a (i + e + 1) := hlc (i + e)
    refine Nat.le_of_mul_le_mul_left ?_ hpos
    calc a (i + e + 1) * (a i * a (i + e + 2))
        = (a i * a (i + e + 1)) * a (i + e + 2) := by ring
      _ ≤ (a (i + 1) * a (i + e)) * a (i + e + 2) := Nat.mul_le_mul_right _ ih
      _ = a (i + 1) * (a (i + e) * a (i + e + 2)) := by ring
      _ ≤ a (i + 1) * (a (i + e + 1) * a (i + e + 1)) := Nat.mul_le_mul_left _ hlc'
      _ = a (i + e + 1) * (a (i + 1) * a (i + e + 1)) := by ring

/-- Cross inequality: `a i * a (i + d + e) ≤ a (i + d) * a (i + e)`. -/
lemma cross (hlc : LogConcave a) (hnz : NoInternalZeros a) (i e : ℕ) :
    ∀ d, a i * a (i + d + e) ≤ a (i + d) * a (i + e) := by
  intro d
  induction d with
  | zero => simp
  | succ d ih =>
    have e1 : i + (d + 1) + e = i + d + e + 1 := by omega
    have e2 : i + (d + 1) = i + d + 1 := by omega
    rw [e1, e2]
    by_cases h0 : a i = 0
    · simp [h0]
    by_cases h1 : a (i + d + e + 1) = 0
    · simp [h1]
    have hA : 0 < a (i + d) :=
      Nat.pos_of_ne_zero (hnz i (i + d) (i + d + e + 1) (by omega) (by omega) h0 h1)
    have hB : 0 < a (i + d + e) :=
      Nat.pos_of_ne_zero (hnz i (i + d + e) (i + d + e + 1) (by omega) (by omega) h0 h1)
    have hadj : a (i + d) * a (i + d + e + 1) ≤ a (i + d + 1) * a (i + d + e) :=
      adj_cross hlc hnz (i + d) e
    refine Nat.le_of_mul_le_mul_left ?_ (Nat.mul_pos hA hB)
    calc a (i + d) * a (i + d + e) * (a i * a (i + d + e + 1))
        = (a i * a (i + d + e)) * (a (i + d) * a (i + d + e + 1)) := by ring
      _ ≤ (a (i + d) * a (i + e)) * (a (i + d + 1) * a (i + d + e)) := Nat.mul_le_mul ih hadj
      _ = a (i + d) * a (i + d + e) * (a (i + d + 1) * a (i + e)) := by ring

lemma subAt_cast_nonneg (u r : ℕ) : 0 ≤ subAt (fun k => (a k : ℤ)) u r := by
  unfold subAt
  split_ifs <;> positivity

/-- A log-concave `ℕ`-sequence with no internal zeros is TN2 (as an integer sequence). -/
theorem tn2_of_logConcave (hlc : LogConcave a) (hnz : NoInternalZeros a) :
    TN2 (fun k => (a k : ℤ)) := by
  intro r s u v hrs huv
  by_cases hsu : s ≤ u
  · have hru : r ≤ u := by omega
    have hsv : s ≤ v := by omega
    have hrv : r ≤ v := by omega
    rw [subAt_eq_coeff_of_le _ _ _ hru, subAt_eq_coeff_of_le _ _ _ hsv,
      subAt_eq_coeff_of_le _ _ _ hsu, subAt_eq_coeff_of_le _ _ _ hrv]
    have h := cross hlc hnz (u - s) (v - u) (s - r)
    have e1 : u - s + (s - r) + (v - u) = v - r := by omega
    have e2 : u - s + (s - r) = u - r := by omega
    have e3 : u - s + (v - u) = v - s := by omega
    rw [e1, e2, e3] at h
    have h' : ((a (u - s) : ℤ) * (a (v - r) : ℤ)) ≤ (a (u - r) : ℤ) * (a (v - s) : ℤ) := by
      exact_mod_cast h
    linarith
  · have hus : u < s := by omega
    rw [subAt_eq_zero_of_lt _ _ _ hus, zero_mul, sub_zero]
    exact mul_nonneg (subAt_cast_nonneg u r) (subAt_cast_nonneg v s)

end Bridge

/-- The integer convolution of the casts is the cast of the Cauchy product. -/
lemma conv_cast (a b : ℕ → ℕ) (k : ℕ) :
    conv (fun n => (a n : ℤ)) (fun n => (b n : ℤ)) k = (cauchyProduct a b k : ℤ) := by
  unfold conv cauchyProduct
  push_cast
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  rw [subAt_eq_coeff_of_le _ _ _ hik]

end Hoggar

-- Finite support is not used by the proof (see the module docstring).
set_option linter.unusedVariables false in
/-- Hoggar's theorem: log-concavity (with no internal zeros) is preserved by convolution. -/
theorem logConcave_cauchyProduct {a b : ℕ → ℕ} (ha : LogConcave a) (hb : LogConcave b)
    (hna : NoInternalZeros a) (hnb : NoInternalZeros b)
    (hfa : FinitelySupported a) (hfb : FinitelySupported b) :
    LogConcave (cauchyProduct a b) := by
  intro k
  have h := (Hoggar.TN2_conv _ _ (Hoggar.tn2_of_logConcave ha hna)
    (Hoggar.tn2_of_logConcave hb hnb)).logConcave k
  simp only [Hoggar.conv_cast] at h
  exact_mod_cast h

end Erdos993Lean
