module

public import Erdos993Lean.Analytic.V22.Analysis.GaussianCalculus
public import Erdos993Lean.Analytic.V22.Analysis.SymmetricUpper

/-!
# Version 2.2 of the manuscript: the lower local binomial shape

Source: the frozen version 5 of the note,
SHA256 `c08dbf5837e1fce232f4871dffbade9fa8197bd01e9d8c77fbd8c921e35e4415`,
Lemma 4.1. The tilt identity retains every integer index,
including the two exterior zero tails. The positive lower bound is only
asserted on the original support `0<=J<=N`.

Consumer: Lemmas 4.2/4.3 and the three-range minorants. Gaussian calculus
owns the common I/Psi functions and their analytic domain theorems.
No forest/process data is reconstructed from these scalar shape bounds.

-/

@[expose] public section

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Set Erdos993Lean.Analytic.NoValley

private theorem binomial_tilt_probability_factor {N j : ℕ} (hj : j ≤ N)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ((1 + r) / 2) ^ j * (1 - (1 + r) / 2) ^ (N - j) =
      (1 - r ^ 2) ^ ((N : ℝ) / 2) *
        Real.exp (2 * Erdos993Lean.Analytic.V22.artanh r * ((j : ℝ) - (N : ℝ) / 2)) *
        ((1 / 2 : ℝ) ^ j * (1 - (1 / 2 : ℝ)) ^ (N - j)) := by
  have hp : 0 < 1 + r := by linarith
  have hm : 0 < 1 - r := by linarith
  have hvar : 0 < 1 - r ^ 2 := by nlinarith
  have hcomp : 1 - (1 + r) / 2 = (1 - r) / 2 := by ring
  have hvarlog : Real.log (1 - r ^ 2) = Real.log (1 + r) + Real.log (1 - r) := by
    rw [← Real.log_mul hp.ne' hm.ne']
    congr 1
    ring
  rw [hcomp]
  apply Real.log_injOn_pos (by simp only [Set.mem_Ioi]; positivity) (by simp only [Set.mem_Ioi]; positivity)
  simp (disch := positivity) only [Real.log_mul, Real.log_pow, Real.log_div,
    Real.log_rpow, Real.log_exp]
  rw [hvarlog]
  unfold Erdos993Lean.Analytic.V22.artanh
  rw [Real.log_div hp.ne' hm.ne']
  rw [Nat.cast_sub hj]
  have hhalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num)]
    simp
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, hhalf, Real.log_one]
  norm_num
  ring

/-- Lemma 4.1, first claim, for every integer index with both exterior tails. -/
theorem binomial_tilt_identity {N : ℕ} (_hN : 2 ≤ N)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (J : ℤ) :
    binom N ((1 + r) / 2) J =
      (1 - r ^ 2) ^ ((N : ℝ) / 2) *
        Real.exp (2 * Erdos993Lean.Analytic.V22.artanh r * ((J : ℝ) - (N : ℝ) / 2)) *
        binom N (1 / 2) J := by
  by_cases hJ0 : J < 0
  · rw [binom_of_neg (q := (1 + r) / 2) hJ0, binom_of_neg (q := 1 / 2) hJ0]
    simp
  by_cases hJN : (N : ℤ) < J
  · rw [binom_of_gt (q := (1 + r) / 2) hJN, binom_of_gt (q := 1 / 2) hJN]
    simp
  lift J to ℕ using (by omega : 0 ≤ J)
  have hJ : J ≤ N := by omega
  rw [binom_natCast_of_le ((1 + r) / 2) hJ, binom_natCast_of_le (1 / 2) hJ]
  push_cast
  calc
    (N.choose J : ℝ) * ((1 + r) / 2) ^ J * (1 - (1 + r) / 2) ^ (N - J) =
        (N.choose J : ℝ) *
          (((1 + r) / 2) ^ J * (1 - (1 + r) / 2) ^ (N - J)) := by ring
    _ = (N.choose J : ℝ) *
        ((1 - r ^ 2) ^ ((N : ℝ) / 2) *
          Real.exp (2 * Erdos993Lean.Analytic.V22.artanh r * ((J : ℝ) - (N : ℝ) / 2)) *
          ((1 / 2 : ℝ) ^ J * (1 - (1 / 2 : ℝ)) ^ (N - J))) := by
      rw [binomial_tilt_probability_factor hJ hr0 hr1]
    _ = (1 - r ^ 2) ^ ((N : ℝ) / 2) *
        Real.exp (2 * Erdos993Lean.Analytic.V22.artanh r * ((J : ℝ) - (N : ℝ) / 2)) *
        ((N.choose J : ℝ) * (1 / 2 : ℝ) ^ J * (1 - (1 / 2 : ℝ)) ^ (N - J)) := by ring

/-- Source Section 4: `c_N`, including the odd-row entropy correction. -/
noncomputable def interiorCentralPrefactor (N : ℕ) : ℝ :=
  if N % 2 = 0 then centralMass (N / 2)
  else centralMass ((N + 1) / 2) *
    Real.exp (((N : ℝ) + 1) * sharedKLI (1 / ((N : ℝ) + 1)))

theorem interiorCentralPrefactor_pos (N : ℕ) : 0 < interiorCentralPrefactor N := by
  unfold interiorCentralPrefactor
  split_ifs
  · exact centralMass_pos _
  · exact mul_pos (centralMass_pos _) (Real.exp_pos _)

theorem interiorCentralPrefactor_even (m : ℕ) :
    interiorCentralPrefactor (2 * m) = centralMass m := by
  unfold interiorCentralPrefactor
  rw [if_pos (by omega : (2 * m) % 2 = 0)]
  rw [show (2 * m) / 2 = m by omega]

theorem interiorCentralPrefactor_odd (m : ℕ) :
    interiorCentralPrefactor (2 * m + 1) = centralMass (m + 1) *
      Real.exp ((((2 * m + 1 : ℕ) : ℝ) + 1) *
        sharedKLI (1 / (((2 * m + 1 : ℕ) : ℝ) + 1))) := by
  unfold interiorCentralPrefactor
  rw [if_neg (by omega : (2 * m + 1) % 2 ≠ 0)]
  rw [show (2 * m + 1 + 1) / 2 = m + 1 by omega]

/-- The midpoint/Hermite--Hadamard comparison used in Lemma 4.1.
Its proof integrates the symmetric derivative by monotonicity, avoiding a
change to the original artanh domain or any extra final analytic premise. -/
theorem interior_artanh_midpoint_bound {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : b < 1) :
    (b - a) * Erdos993Lean.Analytic.V22.artanh ((a + b) / 2) ≤
      sharedKLI b - sharedKLI a := by
  let m : ℝ := (a + b) / 2
  let t : ℝ := (b - a) / 2
  have ht0 : 0 ≤ t := by dsimp [t]; linarith
  let g : ℝ → ℝ := fun x => sharedKLI (m + x) - sharedKLI (m - x) -
    (2 * x) * Erdos993Lean.Analytic.V22.artanh m
  have hpoints (x : ℝ) (hx : x ∈ Icc 0 t) :
      0 ≤ m - x ∧ m - x < 1 ∧ 0 ≤ m + x ∧ m + x < 1 := by
    dsimp [m, t] at *
    constructor
    · linarith [hx.2]
    constructor
    · linarith [hx.1]
    constructor
    · linarith [hx.1]
    · linarith [hx.2]
  have hd : ∀ x ∈ Icc (0 : ℝ) t, HasDerivAt g
      (Erdos993Lean.Analytic.V22.artanh (m + x) +
        Erdos993Lean.Analytic.V22.artanh (m - x) -
        2 * Erdos993Lean.Analytic.V22.artanh m) x := by
    intro x hx
    obtain ⟨hl0, hl1, hr0, hr1⟩ := hpoints x hx
    convert (((hasDerivAt_sharedKLI (by linarith : -1 < m + x) hr1).comp x
      ((hasDerivAt_id x).const_add m)).sub
      ((hasDerivAt_sharedKLI (by linarith : -1 < m - x) hl1).comp x
        ((hasDerivAt_id x).const_sub m))).sub
      ((hasDerivAt_id x).const_mul (2 * Erdos993Lean.Analytic.V22.artanh m)) using 1
    · ext y
      dsimp [g, Function.comp_def]
      ring
    · simp only [id_eq, mul_one, mul_neg_one]
      ring
  have hnonneg (x : ℝ) (hx : x ∈ Icc 0 t) :
      0 ≤ Erdos993Lean.Analytic.V22.artanh (m + x) +
        Erdos993Lean.Analytic.V22.artanh (m - x) -
        2 * Erdos993Lean.Analytic.V22.artanh m := by
    obtain ⟨hl0, hl1, hr0, hr1⟩ := hpoints x hx
    have hc := sharedArtanh_convex.2 ⟨hl0, hl1⟩ ⟨hr0, hr1⟩
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
    have hmid : (1 / 2 : ℝ) * (m - x) + (1 / 2 : ℝ) * (m + x) = m := by ring
    simp only [smul_eq_mul, hmid] at hc
    linarith
  have hcont : ContinuousOn g (Icc 0 t) :=
    fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have hmono : MonotoneOn g (Icc 0 t) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 t) hcont
      (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt)
      (fun x hx => hnonneg x (interior_subset hx))
  have he := hmono ⟨le_rfl, ht0⟩ ⟨ht0, le_rfl⟩ ht0
  have hg0 : g 0 = 0 := by simp [g]
  have hgt : g t = sharedKLI b - sharedKLI a -
      (b - a) * Erdos993Lean.Analytic.V22.artanh m := by
    dsimp [g]
    rw [show m + t = b by dsimp [m, t]; ring,
      show m - t = a by dsimp [m, t]; ring,
      show 2 * t = b - a by dsimp [t]; ring]
  rw [hg0, hgt] at he
  exact sub_nonneg.mp he

/-- Lemma 4.1's symmetric coordinate `x=2d/(N+1)`. -/
noncomputable def interiorSymmetricCoordinate (N : ℕ) (J : ℤ) : ℝ :=
  (2 * (J : ℝ) - (N : ℝ)) / ((N : ℝ) + 1)

/-- A supported integer has its entropy coordinate strictly inside `(-1,1)`. -/
theorem interiorSymmetricCoordinate_domain {N : ℕ} {J : ℤ}
    (hJ0 : 0 ≤ J) (hJN : J ≤ (N : ℤ)) :
    -1 < interiorSymmetricCoordinate N J ∧ interiorSymmetricCoordinate N J < 1 := by
  have hden : 0 < (N : ℝ) + 1 := by positivity
  have hj0 : 0 ≤ (J : ℝ) := by exact_mod_cast hJ0
  have hjN : (J : ℝ) ≤ (N : ℝ) := by exact_mod_cast hJN
  unfold interiorSymmetricCoordinate
  constructor
  · apply (lt_div_iff₀ hden).2
    linarith
  · apply (div_lt_one hden).2
    linarith

/-- The midpoint comparison for one actual supported right-half binomial step. -/
theorem interior_symmetric_step_lower {N k : ℕ} (hc : (N : ℝ) ≤ 2 * k)
    (hk : k + 1 ≤ N) :
    Real.exp (-((N : ℝ) + 1) *
      (sharedKLI (interiorSymmetricCoordinate N ((k + 1 : ℕ) : ℤ)) -
        sharedKLI (interiorSymmetricCoordinate N (k : ℤ)))) ≤
      ((N : ℝ) - k) / ((k : ℝ) + 1) := by
  let a : ℝ := interiorSymmetricCoordinate N (k : ℤ)
  let b : ℝ := interiorSymmetricCoordinate N ((k + 1 : ℕ) : ℤ)
  let mid : ℝ := (a + b) / 2
  have hden : 0 < (N : ℝ) + 1 := by positivity
  have hkr : (k : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hk
  have hnum : 0 < (N : ℝ) - k := by linarith
  have ha0 : 0 ≤ a := by
    dsimp [a, interiorSymmetricCoordinate]
    push_cast
    exact div_nonneg (by linarith) hden.le
  have hab : a ≤ b := by
    dsimp [a, b, interiorSymmetricCoordinate]
    push_cast
    apply div_le_div_of_nonneg_right (by linarith) hden.le
  have hb1 : b < 1 := by
    dsimp [b, interiorSymmetricCoordinate]
    push_cast
    apply (div_lt_one hden).2
    linarith
  have hm0 : 0 ≤ mid := by dsimp [mid]; linarith
  have hm1 : mid < 1 := by dsimp [mid]; linarith
  have hwidth : ((N : ℝ) + 1) * (b - a) = 2 := by
    dsimp [a, b, interiorSymmetricCoordinate]
    push_cast
    field_simp [hden.ne']
    ring
  have hi := mul_le_mul_of_nonneg_left (interior_artanh_midpoint_bound ha0 hab hb1) hden.le
  rw [← mul_assoc, hwidth] at hi
  have hplus : (1 + mid) * ((N : ℝ) + 1) = 2 * ((k : ℝ) + 1) := by
    dsimp [mid, a, b, interiorSymmetricCoordinate]
    push_cast
    field_simp [hden.ne'] <;> ring
  have hminus : (1 - mid) * ((N : ℝ) + 1) = 2 * ((N : ℝ) - k) := by
    dsimp [mid, a, b, interiorSymmetricCoordinate]
    push_cast
    field_simp [hden.ne'] <;> ring
  have hratio : ((N : ℝ) - k) / ((k : ℝ) + 1) = (1 - mid) / (1 + mid) := by
    apply (div_eq_div_iff (show (k : ℝ) + 1 ≠ 0 by positivity)
      (show 1 + mid ≠ 0 by linarith)).2
    apply mul_right_cancel₀ hden.ne'
    calc
      ((N : ℝ) - k) * (1 + mid) * ((N : ℝ) + 1) =
          ((N : ℝ) - k) * ((1 + mid) * ((N : ℝ) + 1)) := by ring
      _ = ((N : ℝ) - k) * (2 * ((k : ℝ) + 1)) := by rw [hplus]
      _ = ((1 - mid) * ((N : ℝ) + 1)) * ((k : ℝ) + 1) := by rw [hminus]; ring
      _ = (1 - mid) * ((k : ℝ) + 1) * ((N : ℝ) + 1) := by ring
  have hlog : Real.log (((N : ℝ) - k) / ((k : ℝ) + 1)) =
      -2 * Erdos993Lean.Analytic.V22.artanh mid := by
    rw [hratio, Real.log_div (ne_of_gt (by linarith : 0 < 1 - mid))
      (ne_of_gt (by linarith : 0 < 1 + mid))]
    unfold Erdos993Lean.Analytic.V22.artanh
    rw [Real.log_div (ne_of_gt (by linarith : 0 < 1 + mid))
      (ne_of_gt (by linarith : 0 < 1 - mid))]
    ring
  have hexp : Real.exp (-2 * Erdos993Lean.Analytic.V22.artanh mid) =
      ((N : ℝ) - k) / ((k : ℝ) + 1) := by
    rw [← hlog, Real.exp_log (div_pos hnum (by positivity : 0 < (k : ℝ) + 1))]
  rw [← hexp]
  apply Real.exp_le_exp.mpr
  change -((N : ℝ) + 1) * (sharedKLI b - sharedKLI a) ≤
    -2 * Erdos993Lean.Analytic.V22.artanh mid
  linarith

/-- The lower local shape along an actual right half-row. The base atom and
each supported successor are retained; the final source theorem discharges
the base/half-row choice by parity and reflection. -/
theorem binom_half_right_local_lower {N c : ℕ} (hN : 2 ≤ N)
    (hc : (N : ℝ) ≤ 2 * c) (d : ℕ) : c + d ≤ N →
    binom N (1 / 2) (c : ℤ) *
      Real.exp (((N : ℝ) + 1) *
        (sharedKLI (interiorSymmetricCoordinate N (c : ℤ)) -
          sharedKLI (interiorSymmetricCoordinate N ((c + d : ℕ) : ℤ)))) ≤
      binom N (1 / 2) ((c + d : ℕ) : ℤ) := by
  induction d with
  | zero => intro _; simp
  | succ d ih =>
    intro hsupport
    have hsupport0 : c + d ≤ N := by omega
    have ih0 := ih hsupport0
    have hk : c + d + 1 ≤ N := by omega
    have hchalf : (N : ℝ) ≤ 2 * ((c + d : ℕ) : ℝ) := by
      push_cast
      have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
      linarith
    have hstepbound := interior_symmetric_step_lower hchalf hk
    have hstep : binom N (1 / 2) ((c + (d + 1) : ℕ) : ℤ) =
        binom N (1 / 2) ((c + d : ℕ) : ℤ) *
          (((N : ℝ) - ((c + d : ℕ) : ℝ)) / (((c + d : ℕ) : ℝ) + 1)) := by
      have h := binom_half_adjacent (by omega : 1 ≤ N) ((c + d : ℕ) : ℤ)
      have hj : ((c + d : ℕ) : ℤ) + 1 = ((c + (d + 1) : ℕ) : ℤ) := by omega
      rw [hj] at h
      push_cast at h
      rw [← mul_div_assoc]
      apply (eq_div_iff (by positivity : ((c + d : ℕ) : ℝ) + 1 ≠ 0)).2
      simp only [Nat.cast_add, Nat.cast_one, Int.cast_natCast, add_assoc] at h ⊢
      linear_combination h
    have hnext : ((c + d + 1 : ℕ) : ℤ) = ((c + (d + 1) : ℕ) : ℤ) := by omega
    rw [hnext] at hstepbound
    calc
      binom N (1 / 2) (c : ℤ) *
          Real.exp (((N : ℝ) + 1) *
            (sharedKLI (interiorSymmetricCoordinate N (c : ℤ)) -
              sharedKLI (interiorSymmetricCoordinate N ((c + (d + 1) : ℕ) : ℤ)))) =
          (binom N (1 / 2) (c : ℤ) *
            Real.exp (((N : ℝ) + 1) *
              (sharedKLI (interiorSymmetricCoordinate N (c : ℤ)) -
                sharedKLI (interiorSymmetricCoordinate N ((c + d : ℕ) : ℤ))))) *
            Real.exp (-((N : ℝ) + 1) *
              (sharedKLI (interiorSymmetricCoordinate N ((c + (d + 1) : ℕ) : ℤ)) -
                sharedKLI (interiorSymmetricCoordinate N ((c + d : ℕ) : ℤ)))) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 1
        congr 1
        ring
      _ ≤ binom N (1 / 2) ((c + d : ℕ) : ℤ) *
          Real.exp (-((N : ℝ) + 1) *
            (sharedKLI (interiorSymmetricCoordinate N ((c + (d + 1) : ℕ) : ℤ)) -
              sharedKLI (interiorSymmetricCoordinate N ((c + d : ℕ) : ℤ)))) :=
        mul_le_mul_of_nonneg_right ih0 (Real.exp_pos _).le
      _ ≤ binom N (1 / 2) ((c + d : ℕ) : ℤ) *
          (((N : ℝ) - ((c + d : ℕ) : ℝ)) / (((c + d : ℕ) : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hstepbound (binom_nonneg (by norm_num) (by norm_num) _)
      _ = binom N (1 / 2) ((c + (d + 1) : ℕ) : ℤ) := hstep.symm

/-- The supported right-half symmetric bound, with the exact even/odd c_N. -/
theorem symmetric_binomial_local_lower_right {N : ℕ} (hN : 2 ≤ N) (J : ℤ)
    (hhalf : (N : ℝ) / 2 ≤ (J : ℝ)) (hJN : J ≤ (N : ℤ)) :
    interiorCentralPrefactor N *
      Real.exp (-((N : ℝ) + 1) * sharedKLI (interiorSymmetricCoordinate N J)) ≤
      binom N (1 / 2) J := by
  by_cases heven : N % 2 = 0
  · obtain ⟨m, hform⟩ : ∃ m : ℕ, N = 2 * m := ⟨N / 2, by omega⟩
    subst N
    have hj : (m : ℤ) ≤ J := by
      have hjr : (m : ℝ) ≤ (J : ℝ) := by push_cast at hhalf; linarith
      exact_mod_cast hjr
    obtain ⟨d, hJ⟩ : ∃ d : ℕ, J = ((m + d : ℕ) : ℤ) :=
      ⟨(J - (m : ℤ)).toNat, by omega⟩
    subst J
    have ht := binom_half_right_local_lower (N := 2 * m) (c := m) (by omega)
      (by push_cast; linarith) d (by omega : m + d ≤ 2 * m)
    have hcenter : interiorSymmetricCoordinate (2 * m) (m : ℤ) = 0 := by
      unfold interiorSymmetricCoordinate
      push_cast
      ring
    rw [binom_half_even_center, hcenter, sharedKLI_zero, zero_sub] at ht
    simpa only [interiorCentralPrefactor_even, neg_mul, mul_neg] using ht
  · obtain ⟨m, hform⟩ : ∃ m : ℕ, N = 2 * m + 1 := ⟨N / 2, by omega⟩
    subst N
    have hj2 : 2 * (m : ℤ) + 1 ≤ 2 * J := by
      have hjr : 2 * (m : ℝ) + 1 ≤ 2 * (J : ℝ) := by push_cast at hhalf; linarith
      exact_mod_cast hjr
    have hj : (m : ℤ) + 1 ≤ J := by omega
    obtain ⟨d, hJ⟩ : ∃ d : ℕ, J = ((m + 1 + d : ℕ) : ℤ) :=
      ⟨(J - ((m : ℤ) + 1)).toNat, by omega⟩
    subst J
    have ht := binom_half_right_local_lower (N := 2 * m + 1) (c := m + 1) (by omega)
      (by push_cast; linarith) d (by omega : m + 1 + d ≤ 2 * m + 1)
    have hcenter : interiorSymmetricCoordinate (2 * m + 1) ((m + 1 : ℕ) : ℤ) =
        1 / (((2 * m + 1 : ℕ) : ℝ) + 1) := by
      unfold interiorSymmetricCoordinate
      push_cast
      congr 1
      ring
    rw [binom_half_odd_center, hcenter] at ht
    calc
      interiorCentralPrefactor (2 * m + 1) *
          Real.exp (-(((2 * m + 1 : ℕ) : ℝ) + 1) *
            sharedKLI (interiorSymmetricCoordinate (2 * m + 1) ((m + 1 + d : ℕ) : ℤ))) =
          centralMass (m + 1) *
            Real.exp ((((2 * m + 1 : ℕ) : ℝ) + 1) *
              (sharedKLI (1 / (((2 * m + 1 : ℕ) : ℝ) + 1)) -
                sharedKLI (interiorSymmetricCoordinate (2 * m + 1) ((m + 1 + d : ℕ) : ℤ)))) := by
        rw [interiorCentralPrefactor_odd, mul_assoc, ← Real.exp_add]
        congr 1
        congr 1
        ring
      _ ≤ binom (2 * m + 1) (1 / 2) ((m + 1 + d : ℕ) : ℤ) := ht

/-- Lemma 4.1's symmetric-row precursor. Its positive lower bound has exactly
the original support assumptions, and retains reflection of the actual atom. -/
theorem symmetric_binomial_local_lower {N : ℕ} (hN : 2 ≤ N) (J : ℤ)
    (hJ0 : 0 ≤ J) (hJN : J ≤ (N : ℤ)) :
    interiorCentralPrefactor N *
      Real.exp (-((N : ℝ) + 1) * sharedKLI (interiorSymmetricCoordinate N J)) ≤
      binom N (1 / 2) J := by
  by_cases hhalf : (N : ℝ) / 2 ≤ (J : ℝ)
  · exact symmetric_binomial_local_lower_right hN J hhalf hJN
  · have href : (N : ℝ) / 2 ≤ (((N : ℤ) - J : ℤ) : ℝ) := by
      push_cast
      linarith
    have h := symmetric_binomial_local_lower_right hN ((N : ℤ) - J) href (by omega)
    rw [binom_half_reflect] at h
    have hcoord : interiorSymmetricCoordinate N ((N : ℤ) - J) =
        -interiorSymmetricCoordinate N J := by
      unfold interiorSymmetricCoordinate
      push_cast
      ring
    obtain ⟨hxL, hxR⟩ := interiorSymmetricCoordinate_domain hJ0 hJN
    rw [hcoord, sharedKLI_even hxL hxR] at h
    exact h

/-- Section 4's exact z coordinate. -/
noncomputable def interiorTiltCoordinate (r : ℝ) (N : ℕ) (J : ℤ) : ℝ :=
  interiorSymmetricCoordinate N J - r

/-- The entropy coordinate is exactly `2*(J-J_m)/(N+1)`. -/
theorem interiorTiltCoordinate_eq (r : ℝ) (N : ℕ) (J : ℤ) :
    interiorTiltCoordinate r N J =
      2 * ((J : ℝ) - (((1 + r) / 2) * ((N : ℝ) + 1) - 1 / 2)) / ((N : ℝ) + 1) := by
  unfold interiorTiltCoordinate interiorSymmetricCoordinate
  field_simp [ne_of_gt (by positivity : 0 < (N : ℝ) + 1)]
  ring

/-- The exact tilt/entropy cancellation in the proof of Lemma 4.1. -/
theorem interior_tilt_entropy_balance {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (N : ℕ) (J : ℤ) :
    (1 - r ^ 2) ^ ((N : ℝ) / 2) *
        Real.exp (2 * Erdos993Lean.Analytic.V22.artanh r * ((J : ℝ) - (N : ℝ) / 2)) *
        Real.exp (-((N : ℝ) + 1) * sharedKLI (interiorSymmetricCoordinate N J)) =
      (Real.sqrt (1 - r ^ 2))⁻¹ *
        Real.exp (-((N : ℝ) + 1) * sharedKLPsi r (interiorTiltCoordinate r N J)) := by
  have hvar : 0 < 1 - r ^ 2 := by nlinarith
  have hden : 0 < (N : ℝ) + 1 := by positivity
  apply Real.log_injOn_pos (by simp only [Set.mem_Ioi]; positivity) (by simp only [Set.mem_Ioi]; positivity)
  simp (disch := positivity) only [Real.log_mul, Real.log_rpow, Real.log_exp,
    Real.log_inv, Real.log_sqrt]
  unfold sharedKLPsi interiorTiltCoordinate
  rw [show r + (interiorSymmetricCoordinate N J - r) =
      interiorSymmetricCoordinate N J by ring]
  rw [show sharedKLI r = r * Erdos993Lean.Analytic.V22.artanh r +
      Real.log (1 - r ^ 2) / 2 by rfl]
  unfold interiorSymmetricCoordinate
  field_simp [hden.ne']
  ring

/-- Lemma 4.1, the exact lower local shape. The final assumptions are solely
N>=2, 0<=r<1 and supported integer J, with q=(1+r)/2. -/
theorem binomial_local_lower {N : ℕ} (hN : 2 ≤ N)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (J : ℤ)
    (hJ0 : 0 ≤ J) (hJN : J ≤ (N : ℤ)) :
    interiorCentralPrefactor N / Real.sqrt (1 - r ^ 2) *
      Real.exp (-((N : ℝ) + 1) * sharedKLPsi r (interiorTiltCoordinate r N J)) ≤
      binom N ((1 + r) / 2) J := by
  have hvar : 0 < 1 - r ^ 2 := by nlinarith
  have hb := symmetric_binomial_local_lower hN J hJ0 hJN
  have htpos : 0 < (1 - r ^ 2) ^ ((N : ℝ) / 2) *
      Real.exp (2 * Erdos993Lean.Analytic.V22.artanh r * ((J : ℝ) - (N : ℝ) / 2)) := by
    positivity
  have hm := mul_le_mul_of_nonneg_left hb htpos.le
  have hbalance := interior_tilt_entropy_balance hr0 hr1 N J
  calc
    interiorCentralPrefactor N / Real.sqrt (1 - r ^ 2) *
        Real.exp (-((N : ℝ) + 1) * sharedKLPsi r (interiorTiltCoordinate r N J)) =
        interiorCentralPrefactor N * ((Real.sqrt (1 - r ^ 2))⁻¹ *
          Real.exp (-((N : ℝ) + 1) * sharedKLPsi r (interiorTiltCoordinate r N J))) := by ring
    _ = interiorCentralPrefactor N *
        ((1 - r ^ 2) ^ ((N : ℝ) / 2) *
          Real.exp (2 * Erdos993Lean.Analytic.V22.artanh r * ((J : ℝ) - (N : ℝ) / 2)) *
          Real.exp (-((N : ℝ) + 1) * sharedKLI (interiorSymmetricCoordinate N J))) := by
      rw [hbalance]
    _ = ((1 - r ^ 2) ^ ((N : ℝ) / 2) *
          Real.exp (2 * Erdos993Lean.Analytic.V22.artanh r * ((J : ℝ) - (N : ℝ) / 2))) *
        (interiorCentralPrefactor N *
          Real.exp (-((N : ℝ) + 1) * sharedKLI (interiorSymmetricCoordinate N J))) := by ring
    _ ≤ ((1 - r ^ 2) ^ ((N : ℝ) / 2) *
          Real.exp (2 * Erdos993Lean.Analytic.V22.artanh r * ((J : ℝ) - (N : ℝ) / 2))) *
        binom N (1 / 2) J := hm
    _ = binom N ((1 + r) / 2) J := (binomial_tilt_identity hN hr0 hr1 J).symm

end Erdos993Lean.Analytic.V22.Analysis

/-! Defining-module declaration and axiom audit. -/

#check Erdos993Lean.Analytic.V22.Analysis.binomial_tilt_probability_factor
#print axioms Erdos993Lean.Analytic.V22.Analysis.binomial_tilt_probability_factor
#check Erdos993Lean.Analytic.V22.Analysis.binomial_tilt_identity
#print axioms Erdos993Lean.Analytic.V22.Analysis.binomial_tilt_identity
#check Erdos993Lean.Analytic.V22.Analysis.interiorCentralPrefactor
#print axioms Erdos993Lean.Analytic.V22.Analysis.interiorCentralPrefactor
#check Erdos993Lean.Analytic.V22.Analysis.interiorCentralPrefactor_pos
#print axioms Erdos993Lean.Analytic.V22.Analysis.interiorCentralPrefactor_pos
#check Erdos993Lean.Analytic.V22.Analysis.interiorCentralPrefactor_even
#print axioms Erdos993Lean.Analytic.V22.Analysis.interiorCentralPrefactor_even
#check Erdos993Lean.Analytic.V22.Analysis.interiorCentralPrefactor_odd
#print axioms Erdos993Lean.Analytic.V22.Analysis.interiorCentralPrefactor_odd
#check Erdos993Lean.Analytic.V22.Analysis.interior_artanh_midpoint_bound
#print axioms Erdos993Lean.Analytic.V22.Analysis.interior_artanh_midpoint_bound
#check Erdos993Lean.Analytic.V22.Analysis.interiorSymmetricCoordinate
#print axioms Erdos993Lean.Analytic.V22.Analysis.interiorSymmetricCoordinate
#check Erdos993Lean.Analytic.V22.Analysis.interiorSymmetricCoordinate_domain
#print axioms Erdos993Lean.Analytic.V22.Analysis.interiorSymmetricCoordinate_domain
#check Erdos993Lean.Analytic.V22.Analysis.interior_symmetric_step_lower
#print axioms Erdos993Lean.Analytic.V22.Analysis.interior_symmetric_step_lower
#check Erdos993Lean.Analytic.V22.Analysis.binom_half_right_local_lower
#print axioms Erdos993Lean.Analytic.V22.Analysis.binom_half_right_local_lower
#check Erdos993Lean.Analytic.V22.Analysis.symmetric_binomial_local_lower_right
#print axioms Erdos993Lean.Analytic.V22.Analysis.symmetric_binomial_local_lower_right
#check Erdos993Lean.Analytic.V22.Analysis.symmetric_binomial_local_lower
#print axioms Erdos993Lean.Analytic.V22.Analysis.symmetric_binomial_local_lower
#check Erdos993Lean.Analytic.V22.Analysis.interiorTiltCoordinate
#print axioms Erdos993Lean.Analytic.V22.Analysis.interiorTiltCoordinate
#check Erdos993Lean.Analytic.V22.Analysis.interiorTiltCoordinate_eq
#print axioms Erdos993Lean.Analytic.V22.Analysis.interiorTiltCoordinate_eq
#check Erdos993Lean.Analytic.V22.Analysis.interior_tilt_entropy_balance
#print axioms Erdos993Lean.Analytic.V22.Analysis.interior_tilt_entropy_balance
#check Erdos993Lean.Analytic.V22.Analysis.binomial_local_lower
#print axioms Erdos993Lean.Analytic.V22.Analysis.binomial_local_lower
