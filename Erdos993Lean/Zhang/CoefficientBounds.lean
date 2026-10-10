module

public import Mathlib
public import Erdos993Lean.IndependencePoly
public import Erdos993Lean.Ceiling.Statement
public import Erdos993Lean.Zhang.Konig
public import Erdos993Lean.Zhang.Decomposition

/-!
# Zhang's finite part, 3: the path lower bound and the matching upper bound (Lemma 2.2)

Source: T. Zhang, *Exact Certificates for Unimodality of Forest Independence Polynomials*
(v1.1, 26 Sep 2026), Lemma 2.2: for every forest of order `n`, independence number `a` and
`v = n − a`,
* (6) `C(n − r + 1, r) ≤ c_r` for all `r ≥ 0` (the path on `n` vertices has the fewest
  independent `r`-sets), and
* (7) `I_F(z) ≤coeff (1 + z)^(a − v) (1 + 2z)^v`.

Binomial convention: the paper's `C(n − r + 1, r)` (zero unless `0 ≤ r ≤ n − r + 1`) is written
`(n + 1 - r).choose r` with natural subtraction; the two agree for every `r` (for `r > n + 1` both
vanish).

Main results:
* `indepCount_succ_erase`: `c_{r+1}(s) = c_{r+1}(s − v) + c_r(s − N[v])` (coefficient form of the
  package's `indepPoly_erase_add`).
* `choose_le_indepCount` (**(6), Finset form**), `choose_le_card_indepSetFinset`,
  `choose_le_independenceCount` (for `FiniteForest`).
* `envelope_identity`: `Σ_{J ⊆ Y} x^|J| (1 + x)^(a − |J|) = (1 + x)^(a − v) (1 + 2x)^v` for
  `|Y| = v ≤ a`.
* `indepCount_le_envelope` (**(7), Finset form**, for a maximum independent `I ⊆ s`),
  `card_indepSetFinset_le_envelope` (**(7)**, `v` = the matching number, by König),
  `independenceCount_le_bRow` (the same bound as `c_r ≤ b_r`, the package's row
  `B_F = (1 + 2x)^ν (1 + x)^(n − 2ν)`).

Grade: PROVED IN LEAN (complete proofs, standard axioms only).
-/

@[expose] public section

namespace Erdos993Lean
namespace Zhang

open Finset Polynomial

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### The one-vertex recurrence for counts -/

/-- `c_{r+1}(s) = c_{r+1}(s − v) + c_r(s − N[v])` for `v ∈ s`. -/
theorem indepCount_succ_erase {s : Finset V} {v : V} (hv : v ∈ s) (r : ℕ) :
    indepCount G s (r + 1) =
      indepCount G (s.erase v) (r + 1) + indepCount G (outsideClosedNbhd G s v) r := by
  have h := congrArg (fun p => Polynomial.coeff p (r + 1)) (indepPoly_erase_add G hv)
  simp only [Polynomial.coeff_add, Polynomial.coeff_X_mul, indepPoly_coeff] at h
  exact_mod_cast h

/-- For an isolated vertex `x` of `G[s]`, `s − N[x] = s − x`. -/
theorem outsideClosedNbhd_of_isolated {s : Finset V} {x : V} (hxn : nbrsIn G s x = ∅) :
    outsideClosedNbhd G s x = s.filter (fun w => w ≠ x) := by
  ext w
  simp only [outsideClosedNbhd, Finset.mem_filter]
  constructor
  · rintro ⟨hw, hne, -⟩
    exact ⟨hw, hne⟩
  · rintro ⟨hw, hne⟩
    refine ⟨hw, hne, fun hadj => ?_⟩
    have hmem : w ∈ nbrsIn G s x := mem_nbrsIn.mpr ⟨hw, hadj⟩
    rw [hxn] at hmem
    exact Finset.notMem_empty w hmem

/-- For a pendant vertex `ℓ` of `G[s]` with neighbour `a`, `s − N[ℓ] = s − ℓ − a`. -/
theorem outsideClosedNbhd_of_pendant {s : Finset V} {ℓ a : V} (hn : nbrsIn G s ℓ = {a}) :
    outsideClosedNbhd G s ℓ = (s.erase ℓ).erase a := by
  have ha : a ∈ nbrsIn G s ℓ := by
    rw [hn]
    exact Finset.mem_singleton_self a
  ext w
  simp only [outsideClosedNbhd, Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨hw, hne, hnadj⟩
    refine ⟨fun hwa => hnadj ?_, hne, hw⟩
    rw [hwa]
    exact (mem_nbrsIn.mp ha).2
  · rintro ⟨hwa, hne, hw⟩
    refine ⟨hw, hne, fun hadj => ?_⟩
    have hmem : w ∈ nbrsIn G s ℓ := mem_nbrsIn.mpr ⟨hw, hadj⟩
    rw [hn, Finset.mem_singleton] at hmem
    exact hwa hmem

/-! ### (6): the path lower bound -/

/-- **Zhang, Lemma 2.2 (6), Finset form**: for every finite vertex set `s` of an acyclic graph,
`C(|s| − r + 1, r) ≤ c_r(G[s])` (induction by deleting an isolated vertex or a leaf; the paper's
proof). -/
theorem choose_le_indepCount (hG : G.IsAcyclic) (s : Finset V) (r : ℕ) :
    (s.card + 1 - r).choose r ≤ indepCount G s r := by
  induction s using Finset.strongInduction generalizing r with
  | H s ih =>
    rcases r with _ | k
    · rw [indepCount_zero, Nat.choose_zero_right]
    by_cases hiso : ∃ x ∈ s, nbrsIn G s x = ∅
    · obtain ⟨x, hx, hxn⟩ := hiso
      have hsx : s.filter (fun w => w ≠ x) = s.erase x := (Finset.filter_ne' s x)
      rw [indepCount_succ_erase hx, outsideClosedNbhd_of_isolated hxn, hsx]
      have h1 := ih _ (Finset.erase_ssubset hx) (k + 1)
      have h2 := ih _ (Finset.erase_ssubset hx) k
      have hc := Finset.card_erase_add_one hx
      have key : (s.card + 1 - (k + 1)).choose (k + 1) ≤
          ((s.erase x).card + 1 - (k + 1)).choose (k + 1) + ((s.erase x).card + 1 - k).choose k := by
        rcases Nat.lt_or_ge k s.card with hkn | hkn
        · have e1 : s.card + 1 - (k + 1) = ((s.erase x).card - k) + 1 := by omega
          have e2 : (s.erase x).card + 1 - (k + 1) = (s.erase x).card - k := by omega
          rw [e1, e2, Nat.choose_succ_succ', add_comm]
          exact Nat.add_le_add_left (Nat.choose_le_choose k (by omega)) _
        · have e1 : s.card + 1 - (k + 1) = 0 := by omega
          rw [e1, Nat.choose_zero_succ]
          exact Nat.zero_le _
      exact le_trans key (Nat.add_le_add h1 h2)
    · push_neg at hiso
      rcases s.eq_empty_or_nonempty with rfl | hne
      · simp
      · obtain ⟨v, hv, hΛ, -⟩ := Occupation.exists_leafStem hG hiso hne
        obtain ⟨ℓ, hℓ⟩ := hΛ
        obtain ⟨hℓN, hℓn⟩ := Occupation.mem_leavesAt.mp hℓ
        have hℓs : ℓ ∈ s := (mem_nbrsIn.mp hℓN).1
        have hvℓ : v ≠ ℓ := G.ne_of_adj (mem_nbrsIn.mp hℓN).2
        have hvE : v ∈ s.erase ℓ := Finset.mem_erase.mpr ⟨hvℓ, hv⟩
        rw [indepCount_succ_erase hℓs, outsideClosedNbhd_of_pendant hℓn]
        have h1 := ih _ (Finset.erase_ssubset hℓs) (k + 1)
        have h2 := ih _ ((Finset.erase_subset v _).trans_ssubset (Finset.erase_ssubset hℓs)) k
        have hc1 := Finset.card_erase_add_one hℓs
        have hc2 := Finset.card_erase_add_one hvE
        have key : (s.card + 1 - (k + 1)).choose (k + 1) ≤
            ((s.erase ℓ).card + 1 - (k + 1)).choose (k + 1) +
              (((s.erase ℓ).erase v).card + 1 - k).choose k := by
          rcases Nat.lt_or_ge k s.card with hkn | hkn
          · have e1 : s.card + 1 - (k + 1) = ((s.erase ℓ).card - k) + 1 := by omega
            have e2 : (s.erase ℓ).card + 1 - (k + 1) = (s.erase ℓ).card - k := by omega
            have e3 : ((s.erase ℓ).erase v).card + 1 - k = (s.erase ℓ).card - k := by omega
            rw [e1, e2, e3, Nat.choose_succ_succ', add_comm]
          · have e1 : s.card + 1 - (k + 1) = 0 := by omega
            rw [e1, Nat.choose_zero_succ]
            exact Nat.zero_le _
        exact le_trans key (Nat.add_le_add h1 h2)

/-- **Zhang, Lemma 2.2 (6)**: every forest on `n` vertices has at least `C(n − r + 1, r)`
independent `r`-sets. -/
theorem choose_le_card_indepSetFinset [Fintype V] (hG : G.IsAcyclic) (r : ℕ) :
    (Fintype.card V + 1 - r).choose r ≤ (G.indepSetFinset r).card := by
  have h := choose_le_indepCount hG (Finset.univ : Finset V) r
  rwa [indepCount_univ, Finset.card_univ] at h

/-- Lemma 2.2 (6) for the package's `FiniteForest`. -/
theorem choose_le_independenceCount (F : FiniteForest) (r : ℕ) :
    (F.n + 1 - r).choose r ≤ independenceCount F r := by
  classical
  have h := choose_le_card_indepSetFinset (G := F.graph) F.isForest r
  rw [Fintype.card_fin] at h
  unfold independenceCount
  convert h using 2

/-! ### (7): the matching upper bound -/

omit [DecidableEq V] in
/-- `Σ_{J ⊆ Y} x^|J| (1 + x)^(a − |J|) = (1 + x)^(a − v) (1 + 2x)^v` for `|Y| = v ≤ a`. -/
theorem envelope_identity (Y : Finset V) (a : ℕ) (hv : Y.card ≤ a) :
    ∑ J ∈ Y.powerset, (X : ℕ[X]) ^ J.card * (1 + X) ^ (a - J.card) =
      (1 + X) ^ (a - Y.card) * (1 + 2 * X) ^ Y.card := by
  have h1 : ∀ J ∈ Y.powerset, (X : ℕ[X]) ^ J.card * (1 + X) ^ (a - J.card) =
      (X ^ J.card * (1 + X) ^ (Y.card - J.card)) * (1 + X) ^ (a - Y.card) := by
    intro J hJ
    rw [Finset.mem_powerset] at hJ
    have hc := Finset.card_le_card hJ
    rw [mul_assoc, ← pow_add]
    congr 2
    omega
  rw [Finset.sum_congr rfl h1, ← Finset.sum_mul, Finset.sum_pow_mul_eq_add_pow, mul_comm]
  congr 2
  ring

omit [DecidableEq V] in
theorem coeff_envelope_sum (Y : Finset V) (a r : ℕ) :
    (∑ J ∈ Y.powerset, (X : ℕ[X]) ^ J.card * (1 + X) ^ (a - J.card)).coeff r =
      ∑ J ∈ Y.powerset, (if J.card ≤ r then (a - J.card).choose (r - J.card) else 0) := by
  rw [Polynomial.finset_sum_coeff]
  apply Finset.sum_congr rfl
  intro J _
  rw [Polynomial.coeff_X_pow_mul', Polynomial.coeff_one_add_X_pow, Nat.cast_id]

/-- `m(J) ≤ a − |J|`: for a maximum independent `I ⊆ s` and an independent `J ⊆ s \ I`,
`J ∪ (I \ N_I(J))` is independent, so `|J| + |I \ N_I(J)| ≤ α(G[s]) = |I|`. -/
theorem card_avail_add_card_le {s I J : Finset V} (hI : IsIndepFinset G I) (hIs : I ⊆ s)
    (hJ : J ⊆ s \ I) (hJi : IsIndepFinset G J) : J.card + (avail G I J).card ≤ alphaIn G s := by
  have hdisj : Disjoint J (avail G I J) := by
    rw [Finset.disjoint_left]
    intro x hxJ hxA
    exact (Finset.mem_sdiff.mp (hJ hxJ)).2 (avail_subset G I J hxA)
  have hind := isIndepFinset_union_avail hI hJi (subset_refl (avail G I J))
  have hsub : J ∪ avail G I J ⊆ s :=
    Finset.union_subset (hJ.trans Finset.sdiff_subset) ((avail_subset G I J).trans hIs)
  have hle := le_alphaIn hsub hind
  rwa [Finset.card_union_of_disjoint hdisj] at hle

/-- **Zhang, Lemma 2.2 (7), Finset form**: for an independent `I ⊆ s` of maximum size `a` and
`v = |s \ I| ≤ a`, `c_r ≤ [z^r] (1 + z)^(a − v) (1 + 2z)^v` (the paper's proof: `m ≤ a − j` in (2),
and at most `C(v, j)` sets `J` of size `j`). -/
theorem indepCount_le_envelope {s I : Finset V} (hI : IsIndepFinset G I) (hIs : I ⊆ s)
    (hmax : I.card = alphaIn G s) (hva : (s \ I).card ≤ I.card) (r : ℕ) :
    indepCount G s r ≤
      ((1 + X : ℕ[X]) ^ (I.card - (s \ I).card) * (1 + 2 * X) ^ (s \ I).card).coeff r := by
  rw [indepCount_decomposition hI hIs r, ← envelope_identity (s \ I) I.card hva,
    coeff_envelope_sum]
  calc ∑ J ∈ (s \ I).powerset.filter (IsIndepFinset G),
        (if J.card ≤ r then (avail G I J).card.choose (r - J.card) else 0)
      ≤ ∑ J ∈ (s \ I).powerset.filter (IsIndepFinset G),
        (if J.card ≤ r then (I.card - J.card).choose (r - J.card) else 0) := by
        apply Finset.sum_le_sum
        intro J hJ
        rw [Finset.mem_filter, Finset.mem_powerset] at hJ
        split_ifs
        · apply Nat.choose_le_choose
          have h := card_avail_add_card_le hI hIs hJ.1 hJ.2
          omega
        · exact le_rfl
    _ ≤ ∑ J ∈ (s \ I).powerset,
        (if J.card ≤ r then (I.card - J.card).choose (r - J.card) else 0) :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

section Fintype

variable [Fintype V]

/-- **Zhang, Lemma 2.2 (7)**: for a forest with independence number `a` and matching number `v`,
`I_F(z) ≤coeff (1 + z)^(a − v) (1 + 2z)^v`. -/
theorem card_indepSetFinset_le_envelope (hG : G.IsAcyclic) (r : ℕ) :
    (G.indepSetFinset r).card ≤
      ((1 + X : ℕ[X]) ^ (G.indepNum - matchingNumber G) *
        (1 + 2 * X) ^ matchingNumber G).coeff r := by
  obtain ⟨I, hI⟩ := G.exists_isNIndepSet_indepNum
  have hIi : IsIndepFinset G I :=
    fun v hv w hw hadj => hI.isIndepSet hv hw (G.ne_of_adj hadj) hadj
  have hIcard : I.card = G.indepNum := hI.card_eq
  have hmax : I.card = alphaIn G Finset.univ := by rw [alphaIn_univ, hIcard]
  have hY : (Finset.univ \ I).card = matchingNumber G := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ I), Finset.card_univ, hIcard,
      matchingNumber_eq_card_sub hG]
  have hva : (Finset.univ \ I).card ≤ I.card := by
    rw [hY, hIcard]
    exact matchingNumber_le_indepNum hG
  have h := indepCount_le_envelope hIi (Finset.subset_univ I) hmax hva r
  rwa [indepCount_univ, hY, hIcard] at h

end Fintype

/-- Lemma 2.2 (7) for the package's `FiniteForest`, as `c_r ≤ b_r` against the row
`B_F = (1 + 2x)^ν (1 + x)^(n − 2ν)` (`bRow`; note `a − ν = n − 2ν` by König). -/
theorem independenceCount_le_bRow (F : FiniteForest) (r : ℕ) :
    independenceCount F r ≤ bRow F.n (matchingNumber F.graph) r := by
  classical
  have h := card_indepSetFinset_le_envelope (G := F.graph) F.isForest r
  have hk := independenceNumber_add_matchingNumber F
  unfold independenceNumber at hk
  have he : F.graph.indepNum - matchingNumber F.graph = F.n - 2 * matchingNumber F.graph := by
    omega
  rw [he, mul_comm] at h
  unfold independenceCount bRow
  convert h using 2

end Zhang
end Erdos993Lean
