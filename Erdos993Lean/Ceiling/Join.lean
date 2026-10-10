module

public import Mathlib
public import Erdos993Lean.Ceiling.HardCore

/-!
# The join: R221's window from the activity-indexed form R221A

The ceiling theorem R221 is proved from an analytic statement indexed by the
activity (R221A: curvature at every integer within distance 1 of the hard-core mean `μ_F(λ)`,
`λ ∈ [1/3, 7/3]`) and four combinatorial boundary lemmas that move it to the window of ranks
`⌈n/4⌉ ≤ k ≤ h_B` (the ceiling proof,
Appendix R).  This file proves three of the four in Lean:

* **B2** (`Join.hardCoreMean_mul_le`, `Join.hardCoreMean_one_third_le`): `μ_F(t)(1 + t) ≤ n t` for
  every activity `t ≥ 0`, hence `μ_F(1/3) ≤ n/4`.  Proof: local LYM for the down-closed family of
  independent sets (Mathlib's `Finset.card_mul_le_card_shadow_mul`) gives
  `(k + 1) i_{k+1} ≤ (n − k) i_k`; sum against `t^(k+1)`.
* **B7** (`Join.hB_le`): the first mode of `B_F = (1 + 2x)^ν (1 + x)^(n − 2ν)` is at most
  `⌈W⌉ = ⌈(3n − 2ν)/6⌉`, `W = n/2 − ν/3`.  Proof (`Join.bc_succ_le`): for
  `f = (1 + 2x)^ν (1 + x)^m` the Euler identity `(ν + m) f = x f' + ν f_A + m f_B`
  (`f_A = f/(1 + 2x)`, `f_B = f/(1 + x)`) gives
  `6(ν + m − k) b_k − (2ν + 3m) b_{k+1} = 2ν (b^A_k − b^A_{k+1}) + 3m (b^B_k − b^B_{k+1})`, and
  induction on `ν + m` shows `b_{k+1} ≤ b_k` whenever `6k ≥ 4ν + 3m` (six times the mean).  This
  is the half of Darroch's mode theorem (1964) that the ceiling needs, proved directly.
* **B8** (`Join.exists_activity_near`): every rank `k` with `⌈n/4⌉ ≤ k ≤ h_B` lies within
  distance less than 1 of `μ_F(t)` for some `t ∈ [1/3, 7/3]`: by the intermediate value theorem
  if `k ≤ μ_F(7/3)` (with B2 at the left end), and with `t = 7/3` otherwise, because
  `k ≤ h_B ≤ ⌈W⌉ < W + 1 ≤ μ_F(7/3) + 1` (B7 and B5).  This is the corrected form of the join
  ("within distance less than one", not "equal to the mean").

The fourth lemma, **B5** (occupation at `7/3`, `OccupationAt73`), is a hypothesis here.

**Result.** `ceiling_of_R221A : R221A → OccupationAt73 → CeilingStatement 8400000`, standard
axioms.  With B5 formalized, the ceiling in Lean rests on R221A alone, the statement that the
computer-assisted analytic proof certifies.  `ceiling_of_R221Window`
(`Ceiling/Tail.lean`) remains available with the window itself as the hypothesis.
-/

@[expose] public section

namespace Erdos993Lean

open Finset Polynomial

namespace Join

/-- Coefficients of `(1 + 2x)^ν (1 + x)^m`. -/
noncomputable def bc (ν m k : ℕ) : ℕ := (((1 + 2 * X : ℕ[X]) ^ ν) * (1 + X) ^ m).coeff k

/-- The Euler-operator identity `(ν + m) f = x f' + ν (1+2x)^(ν-1)(1+x)^m + m (1+2x)^ν (1+x)^(m-1)`
for `f = (1 + 2x)^ν (1 + x)^m`. -/
theorem euler_identity (ν m : ℕ) :
    ((ν + m : ℕ) : ℕ[X]) * ((1 + 2 * X) ^ ν * (1 + X) ^ m) =
      X * derivative ((1 + 2 * X : ℕ[X]) ^ ν * (1 + X) ^ m) +
        (ν : ℕ[X]) * ((1 + 2 * X) ^ (ν - 1) * (1 + X) ^ m) +
        (m : ℕ[X]) * ((1 + 2 * X) ^ ν * (1 + X) ^ (m - 1)) := by
  rw [derivative_mul, derivative_pow, derivative_pow]
  have h1 : derivative (1 + 2 * X : ℕ[X]) = 2 := by
    rw [derivative_add, derivative_one, zero_add, derivative_mul, derivative_X]
    simp
  have h2 : derivative (1 + X : ℕ[X]) = 1 := by
    rw [derivative_add, derivative_one, zero_add, derivative_X]
  rw [h1, h2]
  rcases ν with _ | ν <;> rcases m with _ | m
  · simp
  · simp only [Nat.cast_zero, map_zero, zero_mul, pow_zero, one_mul, zero_add, Nat.add_sub_cancel,
      pow_succ, map_natCast]
    push_cast
    ring
  · simp only [Nat.cast_zero, map_zero, zero_mul, pow_zero, mul_one, add_zero, Nat.add_sub_cancel,
      pow_succ, map_natCast]
    push_cast
    ring
  · simp only [Nat.add_sub_cancel, pow_succ, map_natCast]
    push_cast
    ring

theorem coeff_natCast_mul' (n : ℕ) (p : ℕ[X]) (k : ℕ) : ((n : ℕ[X]) * p).coeff k = n * p.coeff k := by
  rw [← map_natCast (C : ℕ →+* ℕ[X]) n, coeff_C_mul]
  simp

theorem coeff_X_mul_derivative (p : ℕ[X]) (k : ℕ) : (X * derivative p).coeff k = k * p.coeff k := by
  rcases k with _ | k
  · simp
  · rw [coeff_X_mul, coeff_derivative]
    simp only [Nat.cast_id]
    ring

/-- The coefficient form: `(ν + m) b_k = k b_k + ν b^A_k + m b^B_k`. -/
theorem bc_euler (ν m k : ℕ) :
    (ν + m) * bc ν m k = k * bc ν m k + ν * bc (ν - 1) m k + m * bc ν (m - 1) k := by
  have h := congrArg (fun p : ℕ[X] => p.coeff k) (euler_identity ν m)
  simp only [coeff_add, coeff_natCast_mul', coeff_X_mul_derivative] at h
  unfold bc
  exact h

theorem coeff_one_add_two_X_mul (p : ℕ[X]) (k : ℕ) :
    ((1 + 2 * X) * p).coeff (k + 1) = p.coeff (k + 1) + 2 * p.coeff k := by
  have h : (1 + 2 * X : ℕ[X]) * p = p + ((2 : ℕ) : ℕ[X]) * (X * p) := by push_cast; ring
  rw [h, coeff_add, coeff_natCast_mul', coeff_X_mul]

theorem coeff_one_add_X_mul (p : ℕ[X]) (k : ℕ) :
    ((1 + X) * p).coeff (k + 1) = p.coeff (k + 1) + p.coeff k := by
  have h : (1 + X : ℕ[X]) * p = p + X * p := by ring
  rw [h, coeff_add, coeff_X_mul]

theorem bc_succ_left (ν m k : ℕ) : bc (ν + 1) m (k + 1) = bc ν m (k + 1) + 2 * bc ν m k := by
  unfold bc
  rw [pow_succ', mul_assoc, coeff_one_add_two_X_mul]

theorem bc_succ_right (ν m k : ℕ) : bc ν (m + 1) (k + 1) = bc ν m (k + 1) + bc ν m k := by
  unfold bc
  have h : ((1 + 2 * X : ℕ[X]) ^ ν) * (1 + X) ^ (m + 1) = (1 + X) * ((1 + 2 * X) ^ ν * (1 + X) ^ m) := by
    ring
  rw [h, coeff_one_add_X_mul]

theorem bc_zero_zero (k : ℕ) : bc 0 0 (k + 1) = 0 := by
  unfold bc
  simp [Polynomial.coeff_one]

/-- **Mean–mode bound for `B_F` (lemma B7, integer form).**  The coefficients of
`(1 + 2x)^ν (1 + x)^m` are nonincreasing from every index `k ≥ 2ν/3 + m/2` (the mean of the
normalized row) on. -/
theorem bc_succ_le (ν m k : ℕ) (hk : 4 * ν + 3 * m ≤ 6 * k) : bc ν m (k + 1) ≤ bc ν m k := by
  induction h : ν + m using Nat.strong_induction_on generalizing ν m k with
  | _ N ih =>
  have hA : ν * bc ν m (k + 1) = ν * (bc (ν - 1) m (k + 1) + 2 * bc (ν - 1) m k) := by
    rcases ν with _ | ν
    · simp
    · rw [bc_succ_left]; rfl
  have hB : m * bc ν m (k + 1) = m * (bc ν (m - 1) (k + 1) + bc ν (m - 1) k) := by
    rcases m with _ | m
    · simp
    · rw [bc_succ_right]; rfl
  have hIA : ν * bc (ν - 1) m (k + 1) ≤ ν * bc (ν - 1) m k := by
    rcases ν with _ | ν
    · simp
    · exact Nat.mul_le_mul_left _ (ih (ν + m) (by omega) ν m k (by omega) rfl)
  have hIB : m * bc ν (m - 1) (k + 1) ≤ m * bc ν (m - 1) k := by
    rcases m with _ | m
    · simp
    · exact Nat.mul_le_mul_left _ (ih (ν + m) (by omega) ν m k (by omega) rfl)
  have he := bc_euler ν m k
  have hmul : 6 * (ν + m) * bc ν m k ≤ (2 * ν + 3 * m + 6 * k) * bc ν m k :=
    Nat.mul_le_mul_right _ (by omega)
  rcases Nat.eq_zero_or_pos (2 * ν + 3 * m) with h0 | hpos
  · obtain ⟨rfl, rfl⟩ : ν = 0 ∧ m = 0 := by omega
    rw [bc_zero_zero]
    exact Nat.zero_le _
  · apply Nat.le_of_mul_le_mul_left _ hpos
    nlinarith

/-- A sequence that is nonincreasing from index `c` on has its first mode at most `c`. -/
theorem firstMode_le_of_antitone_from {b : ℕ → ℕ} {c : ℕ} (h : ∀ j, c ≤ j → b (j + 1) ≤ b j) :
    firstMode b ≤ c := by
  classical
  have hdec : ∀ i, b (c + i) ≤ b c := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => exact (h (c + i) (by omega)).trans ih
  obtain ⟨m0, hm0, hmax⟩ := (Finset.range (c + 1)).exists_max_image b ⟨0, by simp⟩
  have hall : ∀ j, b j ≤ b m0 := by
    intro j
    by_cases hj : j ≤ c
    · exact hmax j (by simp; omega)
    · obtain ⟨i, rfl⟩ : ∃ i, j = c + i := ⟨j - c, by omega⟩
      exact (hdec i).trans (hmax c (by simp))
  have hex : ∃ m, ∀ j, b j ≤ b m := ⟨m0, hall⟩
  unfold firstMode
  rw [dif_pos hex]
  simp only [Finset.mem_range] at hm0
  exact (Nat.find_min' hex hall).trans (by omega)

/-- A matching has at most `n / 2` edges: `2 ν ≤ n`. -/
theorem two_mul_matchingNumber_le {n : ℕ} (G : SimpleGraph (Fin n)) :
    2 * matchingNumber G ≤ n := by
  classical
  obtain ⟨M, hM, hMcard, hMfin, hMdisj⟩ := Ceiling.matchingNumber_mem G
  rw [← hMcard, Set.ncard_eq_toFinset_card M hMfin]
  have hcard : ∀ e ∈ hMfin.toFinset, e.toFinset.card = 2 := by
    intro e he
    rw [Set.Finite.mem_toFinset] at he
    exact Sym2.card_toFinset_of_not_isDiag e (G.not_isDiag_of_mem_edgeSet (hM he))
  have hdisj : (hMfin.toFinset : Set (Sym2 (Fin n))).PairwiseDisjoint (fun e => e.toFinset) := by
    intro e he f hf hef
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at he hf
    rw [Function.onFun, Finset.disjoint_left]
    intro v hve hvf
    rw [Sym2.mem_toFinset] at hve hvf
    exact hMdisj he hf hef v hve hvf
  have h1 := Finset.card_biUnion hdisj
  rw [Finset.sum_congr rfl hcard, Finset.sum_const, smul_eq_mul] at h1
  have h2 : (hMfin.toFinset.biUnion (fun e => e.toFinset)).card ≤ n := by
    calc _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_univ _
      _ = n := by simp
  omega

/-- **Lemma B7 (ceiling proof, Appendix R4):** `h_B ≤ ⌈W⌉` with `W = n/2 − ν/3`, in the integer form
`h_B ≤ ⌈(3n − 2ν)/6⌉`. -/
theorem hB_le (F : FiniteForest) : hB F ≤ (3 * F.n - 2 * matchingNumber F.graph + 5) / 6 := by
  apply firstMode_le_of_antitone_from
  intro j hj
  have h2 := two_mul_matchingNumber_le F.graph
  exact bc_succ_le _ _ _ (by omega)

/-! ## B2: the marginal bound `μ_F(λ) ≤ nλ/(1+λ)` -/

/-- Local LYM for independent sets: `(k+1) i_{k+1} ≤ (n − k) i_k` in any graph on `n` vertices
(each independent `(k+1)`-set has `k+1` independent `k`-subsets; each independent `k`-set has at
most `n − k` one-vertex extensions). -/
theorem succ_mul_card_indepSetFinset_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    (k + 1) * (G.indepSetFinset (k + 1)).card ≤
      (Fintype.card V - k) * (G.indepSetFinset k).card := by
  have hsized : ((G.indepSetFinset (k + 1) : Finset (Finset V)) : Set (Finset V)).Sized (k + 1) := by
    intro s hs
    rw [Finset.mem_coe, SimpleGraph.mem_indepSetFinset_iff] at hs
    exact hs.card_eq
  have hlym := Finset.card_mul_le_card_shadow_mul hsized
  have hsh : (G.indepSetFinset (k + 1)).shadow ⊆ G.indepSetFinset k := by
    intro t ht
    rw [Finset.mem_shadow_iff] at ht
    obtain ⟨s, hs, a, ha, rfl⟩ := ht
    rw [SimpleGraph.mem_indepSetFinset_iff] at hs ⊢
    refine ⟨?_, ?_⟩
    · exact hs.isIndepSet.mono (by simp)
    · rw [Finset.card_erase_of_mem ha, hs.card_eq]
      rfl
  have h1 := Finset.card_le_card hsh
  have h2 : Fintype.card V - (k + 1) + 1 ≤ Fintype.card V - k + 1 := by omega
  calc (k + 1) * (G.indepSetFinset (k + 1)).card
      = (G.indepSetFinset (k + 1)).card * (k + 1) := by ring
    _ ≤ ((G.indepSetFinset (k + 1)).shadow).card * (Fintype.card V - (k + 1) + 1) := hlym
    _ ≤ (G.indepSetFinset k).card * (Fintype.card V - k) := by
        rcases Nat.lt_or_ge k (Fintype.card V) with hk | hk
        · have : Fintype.card V - (k + 1) + 1 = Fintype.card V - k := by omega
          rw [this]
          exact Nat.mul_le_mul_right _ h1
        · have : Fintype.card V - (k + 1) + 1 = 1 := by omega
          rw [this, mul_one]
          -- no independent `(k+1)`-set when `k ≥ n`, so the shadow is empty
          have hempty : G.indepSetFinset (k + 1) = ∅ := by
            rw [Finset.eq_empty_iff_forall_notMem]
            intro s hs
            rw [SimpleGraph.mem_indepSetFinset_iff] at hs
            have := Finset.card_le_univ s
            rw [hs.card_eq] at this
            omega
          rw [hempty, Finset.shadow_empty, Finset.card_empty]
          exact Nat.zero_le _
    _ = (Fintype.card V - k) * (G.indepSetFinset k).card := by ring

theorem succ_mul_independenceCount_le (F : FiniteForest) (k : ℕ) :
    (k + 1) * independenceCount F (k + 1) ≤ (F.n - k) * independenceCount F k := by
  classical
  have h := succ_mul_card_indepSetFinset_le F.graph k
  rw [Fintype.card_fin] at h
  unfold independenceCount
  convert h using 3

theorem independenceCount_zero (F : FiniteForest) : independenceCount F 0 = 1 := by
  classical
  unfold independenceCount
  rw [Finset.card_eq_one]
  refine ⟨∅, ?_⟩
  ext s
  rw [Finset.mem_singleton]
  constructor
  · intro hs
    rw [SimpleGraph.mem_indepSetFinset_iff] at hs
    exact Finset.card_eq_zero.mp hs.card_eq
  · rintro rfl
    rw [SimpleGraph.mem_indepSetFinset_iff]
    exact ⟨by simp, by simp⟩

theorem one_le_partitionFn (F : FiniteForest) {t : ℝ} (ht : 0 ≤ t) : 1 ≤ partitionFn F t := by
  unfold partitionFn
  rw [Finset.sum_range_succ']
  simp only [pow_zero, mul_one, independenceCount_zero, Nat.cast_one]
  have : 0 ≤ ∑ k ∈ range F.n, (independenceCount F (k + 1) : ℝ) * t ^ (k + 1) :=
    Finset.sum_nonneg fun k _ => by positivity
  linarith

/-- **Lemma B2 (ceiling proof, Appendix R1):** `μ_F(t) (1 + t) ≤ n t` for every activity `t ≥ 0`, i.e.
`μ_F(t) ≤ nt/(1+t)` (marginal occupation at most `t/(1+t)` per vertex). -/
theorem hardCoreMean_mul_le (F : FiniteForest) {t : ℝ} (ht : 0 ≤ t) :
    hardCoreMean F t * (1 + t) ≤ F.n * t := by
  have hZ := one_le_partitionFn F ht
  set S0 := partitionFn F t with hS0
  set S1 := ∑ k ∈ range (F.n + 1), (k : ℝ) * (independenceCount F k : ℝ) * t ^ k with hS1
  -- `S1 ≤ t (n S0 − S1)`
  have key : S1 ≤ t * (F.n * S0 - S1) := by
    have e1 : S1 = ∑ k ∈ range F.n, ((k + 1 : ℕ) : ℝ) * (independenceCount F (k + 1) : ℝ) *
        t ^ (k + 1) := by
      rw [hS1, Finset.sum_range_succ']
      simp
    have e2 : t * (F.n * S0 - S1) =
        ∑ k ∈ range F.n, ((F.n - k : ℕ) : ℝ) * (independenceCount F k : ℝ) * t ^ (k + 1) := by
      rw [hS0, hS1, partitionFn, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum,
        Finset.sum_range_succ]
      have hlast : t * (↑F.n * ((independenceCount F F.n : ℝ) * t ^ F.n) -
          (F.n : ℝ) * (independenceCount F F.n : ℝ) * t ^ F.n) = 0 := by ring
      rw [hlast, add_zero]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      rw [Nat.cast_sub hk.le]
      ring
    rw [e2, e1]
    refine Finset.sum_le_sum fun k hk => ?_
    have hc := succ_mul_independenceCount_le F k
    have hc' : ((k + 1 : ℕ) : ℝ) * (independenceCount F (k + 1) : ℝ) ≤
        ((F.n - k : ℕ) : ℝ) * (independenceCount F k : ℝ) := by
      exact_mod_cast hc
    exact mul_le_mul_of_nonneg_right hc' (by positivity)
  have hmean : hardCoreMean F t = S1 / S0 := rfl
  rw [hmean, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
  nlinarith

/-- `μ_F(1/3) ≤ n/4`. -/
theorem hardCoreMean_one_third_le (F : FiniteForest) : hardCoreMean F (1 / 3) ≤ F.n / 4 := by
  have h := hardCoreMean_mul_le F (t := 1 / 3) (by norm_num)
  linarith

/-! ## B8: the join -/

theorem continuousOn_hardCoreMean (F : FiniteForest) :
    ContinuousOn (hardCoreMean F) (Set.Ici 0) := by
  have hnum : Continuous fun t : ℝ =>
      ∑ k ∈ range (F.n + 1), (k : ℝ) * (independenceCount F k : ℝ) * t ^ k := by
    fun_prop
  have hden : Continuous (partitionFn F) := by
    unfold partitionFn
    fun_prop
  exact hnum.continuousOn.div hden.continuousOn fun t ht =>
    (lt_of_lt_of_le one_pos (one_le_partitionFn F ht)).ne'

/-- **Lemma B8 (the join; ceiling proof, §10, in its corrected form):** every window rank lies within
distance less than one of the hard-core mean at some activity in `[1/3, 7/3]`.  Uses B2 (proved
above), B7 (`Join.hB_le`, proved above) and the occupation bound B5 (`OccupationAt73`). -/
theorem exists_activity_near (hocc : OccupationAt73) (F : FiniteForest) (k : ℕ)
    (hk1 : (F.n + 3) / 4 ≤ k) (hk2 : k ≤ hB F) :
    ∃ t : ℝ, 1 / 3 ≤ t ∧ t ≤ 7 / 3 ∧ |(k : ℝ) - hardCoreMean F t| < 1 := by
  by_cases hkμ : (k : ℝ) ≤ hardCoreMean F (7 / 3)
  · have hn4 : (F.n : ℝ) ≤ 4 * k := by exact_mod_cast (by omega : F.n ≤ 4 * k)
    have hlow : hardCoreMean F (1 / 3) ≤ k := by
      have := hardCoreMean_one_third_le F
      linarith
    have hcont : ContinuousOn (hardCoreMean F) (Set.Icc (1 / 3) (7 / 3)) :=
      (continuousOn_hardCoreMean F).mono fun t ht => le_trans (by norm_num) ht.1
    obtain ⟨t, ⟨ht1, ht2⟩, hteq⟩ :=
      intermediate_value_Icc (by norm_num : (1 / 3 : ℝ) ≤ 7 / 3) hcont ⟨hlow, hkμ⟩
    exact ⟨t, ht1, ht2, by rw [hteq, sub_self, abs_zero]; norm_num⟩
  · push_neg at hkμ
    refine ⟨7 / 3, by norm_num, le_refl _, ?_⟩
    have hB7 := hB_le F
    have h2 := two_mul_matchingNumber_le F.graph
    have hk6 : 6 * k + 2 * matchingNumber F.graph ≤ 3 * F.n + 5 := by omega
    have hk6R : (6 * k + 2 * matchingNumber F.graph : ℝ) ≤ 3 * F.n + 5 := by exact_mod_cast hk6
    have hocc' := hocc F
    have hcc : (0 : ℝ) ≤ (numComponents F : ℝ) / 7 := by positivity
    unfold matchingEnvelopeMean at hocc'
    rw [abs_lt]
    constructor <;> linarith

end Join

open Join

/-- **R221's window from R221A and B5.**  The join lemmas B2, B7, B8 are proved in Lean
(`Join.hardCoreMean_one_third_le`, `Join.hB_le`, `Join.exists_activity_near`). -/
theorem r221Window_of_R221A (hA : R221A) (hocc : OccupationAt73) : R221Window := by
  intro F hn k hk1 hk2
  have hk_pos : 1 ≤ k := by omega
  obtain ⟨t, ht1, ht2, hclose⟩ := exists_activity_near hocc F k hk1 hk2
  obtain ⟨h1, h2, h3, hcurv⟩ := hA F hn t ht1 ht2 k hk_pos hclose
  refine ⟨h1, h2, h3, ?_⟩
  have hexp : 1 ≤ Real.exp (1 / (1650 * (F.n : ℝ))) := Real.one_le_exp (by positivity)
  have hP : (0 : ℝ) ≤ (independenceCount F (k - 1) : ℝ) * (independenceCount F (k + 1) : ℝ) := by
    positivity
  have hlt : ((independenceCount F (k - 1) * independenceCount F (k + 1) : ℕ) : ℝ) <
      ((independenceCount F k * independenceCount F k : ℕ) : ℝ) := by
    push_cast
    nlinarith
  exact_mod_cast hlt

/-- **The ceiling from R221A and the occupation bound B5.**  Every forest with at least
8,400,000 vertices has a unimodal independence sequence, given R221A (the analytic,
computer-assisted input) and B5 (`OccupationAt73`, a combinatorial paper proof). -/
theorem ceiling_of_R221A (hA : R221A) (hocc : OccupationAt73) : CeilingStatement 8400000 :=
  ceiling_of_R221Window (r221Window_of_R221A hA hocc)

end Erdos993Lean
