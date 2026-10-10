module

public import Mathlib
public import Erdos993Lean.IndependencePoly
public import Erdos993Lean.Zhang.Konig

/-!
# Zhang's finite part, 2: the decomposition relative to an independent set

Source: T. Zhang, *Exact Certificates for Unimodality of Forest Independence Polynomials*
(v1.1, 26 Sep 2026), Section 2.1, identities (2)–(5).

Fix an independent set `I` inside a finite vertex set `s` (for the paper: `s` = all vertices and
`I` a maximum independent set) and put `Y = s \ I`.  For `J ⊆ Y` let
`avail G I J = I \ N_I(J)` be the vertices of `I` with no neighbour in `J`.

Main results (all for an arbitrary independent `I ⊆ s`; maximality is used only where stated):
* `isIndep_iff_decomposition`, `decomposition_unique`: a subset `S ⊆ s` is independent iff
  `S = J ∪ K` with `J ⊆ Y` independent and `K ⊆ I \ N_I(J)`; the parts are `J = S \ I`,
  `K = S ∩ I`, so the decomposition is unique.
* `indepPoly_decomposition` (**(2)**): `I_{G[s]}(x) = Σ_J x^|J| (1 + x)^|I \ N_I(J)|`, over the
  independent `J ⊆ Y`.
* `indepCount_decomposition` (**(3), Finset form**):
  `c_r = Σ_J [|J| ≤ r] C(|I \ N_I(J)|, r − |J|)`.
* `tCount G s I j m` = `t_{j,m}`, and `indepCount_eq_sum_tCount` (**(3), grouped form**):
  `c_r = Σ_{j ≤ |Y|} Σ_{m ≤ |I|} t_{j,m} [j ≤ r] C(m, r − j)`.
* `tCount_zero` (`t_{0,m} = [m = |I|]`), `tCount_eq_zero_of_alphaIn_lt` (`t_{j,m} = 0` when
  `j + m > α(G[s])`), `sum_tCount` (`T_j = Σ_m t_{j,m}` is the number of independent `j`-subsets
  of `Y`), `sum_tCount_one` (`T_1 = |Y|`), `sum_tCount_le_choose` (`T_j ≤ C(|Y|, j)`): the basic
  constraints **(5)**.
* `indepCount_eq_paper` (**(3), the paper's display**): for a maximum independent `I`
  (`|I| = α(G[s]) = a`, `|Y| = v`), `c_r = C(a, r) + Σ_{j=1}^{v} Σ_{m=0}^{a−j} [j ≤ r] C(m, r−j) t_{j,m}`.

Grade: PROVED IN LEAN (complete proofs, standard axioms only).
-/

@[expose] public section

namespace Erdos993Lean
namespace Zhang

open Finset Polynomial

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### Available vertices -/

variable (G) in
/-- `I \ N_I(J)`: the vertices of `I` with no neighbour in `J` (Zhang's available vertices;
`m(J) = |avail G I J|`). -/
def avail (I J : Finset V) : Finset V :=
  I.filter (fun i => ∀ y ∈ J, ¬ G.Adj y i)

omit [DecidableEq V] in
theorem mem_avail {I J : Finset V} {i : V} :
    i ∈ avail G I J ↔ i ∈ I ∧ ∀ y ∈ J, ¬ G.Adj y i := by
  unfold avail
  exact Finset.mem_filter

omit [DecidableEq V] in
variable (G) in
theorem avail_subset (I J : Finset V) : avail G I J ⊆ I := Finset.filter_subset _ _

omit [DecidableEq V] in
variable (G) in
theorem avail_empty (I : Finset V) : avail G I ∅ = I := by
  ext i
  rw [mem_avail]
  simp

/-- `J ∪ K` is independent for an independent `J` and `K ⊆ I \ N_I(J)`, `I` independent. -/
theorem isIndepFinset_union_avail {I J K : Finset V} (hI : IsIndepFinset G I)
    (hJ : IsIndepFinset G J) (hK : K ⊆ avail G I J) : IsIndepFinset G (J ∪ K) := by
  classical
  intro a ha b hb hab
  rw [Finset.mem_union] at ha hb
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact hJ a ha b hb hab
  · exact (mem_avail.mp (hK hb)).2 a ha hab
  · exact (mem_avail.mp (hK ha)).2 b hb hab.symm
  · exact hI a (avail_subset G I J (hK ha)) b (avail_subset G I J (hK hb)) hab

/-- For an independent `S`, the part `S ∩ I` avoids the neighbourhood of the part `S \ I`. -/
theorem inter_subset_avail {I S : Finset V} (hS : IsIndepFinset G S) :
    S ∩ I ⊆ avail G I (S \ I) := by
  intro i hi
  rw [Finset.mem_inter] at hi
  rw [mem_avail]
  exact ⟨hi.2, fun y hy hyi => hS y (Finset.mem_sdiff.mp hy).1 i hi.1 hyi⟩

/-! ### The decomposition -/

/-- **The decomposition (Zhang, Section 2.1).**  Relative to an independent set `I ⊆ s`, a
subset `S` of `s` is independent iff `S = J ∪ K` with `J ⊆ s \ I` independent and
`K ⊆ I \ N_I(J)`. -/
theorem isIndep_iff_decomposition {s I S : Finset V} (hI : IsIndepFinset G I) (hIs : I ⊆ s) :
    (S ⊆ s ∧ IsIndepFinset G S) ↔
      ∃ J K, J ⊆ s \ I ∧ IsIndepFinset G J ∧ K ⊆ avail G I J ∧ S = J ∪ K := by
  constructor
  · rintro ⟨hSs, hS⟩
    refine ⟨S \ I, S ∩ I, Finset.sdiff_subset_sdiff hSs subset_rfl,
      isIndepFinset_mono hS Finset.sdiff_subset, inter_subset_avail hS, ?_⟩
    exact (Finset.sdiff_union_inter S I).symm
  · rintro ⟨J, K, hJ, hJi, hK, rfl⟩
    exact ⟨Finset.union_subset (hJ.trans Finset.sdiff_subset)
      ((hK.trans (avail_subset G I J)).trans hIs), isIndepFinset_union_avail hI hJi hK⟩

/-- **Uniqueness of the decomposition**: for `J ⊆ s \ I` and `K ⊆ I`, the parts of `J ∪ K` are
recovered as `(J ∪ K) \ I = J` and `(J ∪ K) ∩ I = K`. -/
theorem decomposition_unique {s I J K : Finset V} (hJ : J ⊆ s \ I) (hK : K ⊆ I) :
    (J ∪ K) \ I = J ∧ (J ∪ K) ∩ I = K := by
  have hJI : ∀ x ∈ J, x ∉ I := fun x hx => (Finset.mem_sdiff.mp (hJ hx)).2
  constructor
  · ext x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hx | hx, hxI⟩
      · exact hx
      · exact absurd (hK hx) hxI
    · intro hx
      exact ⟨Or.inl hx, hJI x hx⟩
  · ext x
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hx | hx, hxI⟩
      · exact absurd hxI (hJI x hx)
      · exact hx
    · intro hx
      exact ⟨Or.inr hx, hK hx⟩

omit [DecidableEq V] in
/-- `Σ_{K ⊆ A} x^|K| = (1 + x)^|A|`. -/
theorem sum_powerset_X_pow (A : Finset V) :
    ∑ K ∈ A.powerset, (X : ℤ[X]) ^ K.card = (1 + X) ^ A.card := by
  have h := Finset.sum_pow_mul_eq_add_pow (X : ℤ[X]) 1 A
  simp only [one_pow, mul_one] at h
  rw [h, add_comm]

/-- **Zhang (2)**: `I_{G[s]}(x) = Σ_J x^|J| (1 + x)^|I \ N_I(J)|`, the sum over the independent
subsets `J` of `s \ I`, for every independent `I ⊆ s`. -/
theorem indepPoly_decomposition {s I : Finset V} (hI : IsIndepFinset G I) (hIs : I ⊆ s) :
    indepPoly G s = ∑ J ∈ (s \ I).powerset.filter (IsIndepFinset G),
      X ^ J.card * (1 + X) ^ (avail G I J).card := by
  unfold indepPoly
  have hmaps : ∀ S ∈ s.powerset.filter (IsIndepFinset G),
      (fun S => S \ I) S ∈ (s \ I).powerset.filter (IsIndepFinset G) := by
    intro S hS
    rw [Finset.mem_filter, Finset.mem_powerset] at hS ⊢
    exact ⟨Finset.sdiff_subset_sdiff hS.1 subset_rfl, isIndepFinset_mono hS.2 Finset.sdiff_subset⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [Finset.mem_filter, Finset.mem_powerset] at hJ
  obtain ⟨hJs, hJi⟩ := hJ
  rw [← sum_powerset_X_pow, Finset.mul_sum]
  symm
  refine Finset.sum_nbij' (fun K => J ∪ K) (fun S => S ∩ I) ?_ ?_ ?_ ?_ ?_
  · intro K hK
    rw [Finset.mem_powerset] at hK
    have hKI : K ⊆ I := hK.trans (avail_subset G I J)
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨⟨Finset.union_subset (hJs.trans Finset.sdiff_subset) (hKI.trans hIs),
      isIndepFinset_union_avail hI hJi hK⟩, (decomposition_unique hJs hKI).1⟩
  · intro S hS
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_powerset] at hS
    obtain ⟨⟨_, hSi⟩, hSJ⟩ := hS
    rw [Finset.mem_powerset]
    have h := inter_subset_avail (I := I) hSi
    rw [hSJ] at h
    exact h
  · intro K hK
    rw [Finset.mem_powerset] at hK
    exact (decomposition_unique hJs (hK.trans (avail_subset G I J))).2
  · intro S hS
    rw [Finset.mem_filter, Finset.mem_filter] at hS
    rw [← hS.2]
    exact Finset.sdiff_union_inter S I
  · intro K hK
    rw [Finset.mem_powerset] at hK
    have hKI : K ⊆ I := hK.trans (avail_subset G I J)
    have hdisj : Disjoint J K := by
      rw [Finset.disjoint_left]
      intro x hxJ hxK
      exact (Finset.mem_sdiff.mp (hJs hxJ)).2 (hKI hxK)
    rw [Finset.card_union_of_disjoint hdisj, pow_add]

/-- **Zhang (3), Finset form**: `c_r = Σ_J [|J| ≤ r] C(|I \ N_I(J)|, r − |J|)`, the sum over the
independent subsets `J` of `s \ I`, for every independent `I ⊆ s`. -/
theorem indepCount_decomposition {s I : Finset V} (hI : IsIndepFinset G I) (hIs : I ⊆ s)
    (r : ℕ) :
    indepCount G s r = ∑ J ∈ (s \ I).powerset.filter (IsIndepFinset G),
      if J.card ≤ r then (avail G I J).card.choose (r - J.card) else 0 := by
  have h := congrArg (fun p => Polynomial.coeff p r) (indepPoly_decomposition hI hIs)
  simp only [indepPoly_coeff, Polynomial.finset_sum_coeff, Polynomial.coeff_X_pow_mul',
    Polynomial.coeff_one_add_X_pow] at h
  rw [← Nat.cast_inj (R := ℤ), h]
  push_cast
  exact Finset.sum_congr rfl (fun _ _ => rfl)

/-! ### The counts `t_{j,m}` -/

variable (G) in
/-- `t_{j,m}` (Zhang, Section 2.1): the number of independent `j`-subsets `J` of `s \ I` with
`|I \ N_I(J)| = m`. -/
def tCount (s I : Finset V) (j m : ℕ) : ℕ :=
  ((s \ I).powerset.filter
    (fun J => IsIndepFinset G J ∧ J.card = j ∧ (avail G I J).card = m)).card

/-- **Zhang (3), grouped form**: `c_r = Σ_{j ≤ |s \ I|} Σ_{m ≤ |I|} t_{j,m} [j ≤ r] C(m, r − j)`
for every independent `I ⊆ s`. -/
theorem indepCount_eq_sum_tCount {s I : Finset V} (hI : IsIndepFinset G I) (hIs : I ⊆ s)
    (r : ℕ) :
    indepCount G s r = ∑ j ∈ range ((s \ I).card + 1), ∑ m ∈ range (I.card + 1),
      tCount G s I j m * (if j ≤ r then m.choose (r - j) else 0) := by
  rw [indepCount_decomposition hI hIs r, ← Finset.sum_product']
  have hmaps : ∀ J ∈ (s \ I).powerset.filter (IsIndepFinset G),
      (fun J => (J.card, (avail G I J).card)) J ∈
        range ((s \ I).card + 1) ×ˢ range (I.card + 1) := by
    intro J hJ
    rw [Finset.mem_filter, Finset.mem_powerset] at hJ
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (Finset.card_le_card hJ.1),
      Nat.lt_succ_of_le (Finset.card_le_card (avail_subset G I J))⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_congr rfl
  rintro ⟨j, m⟩ -
  have hval : ∀ J ∈ ((s \ I).powerset.filter (IsIndepFinset G)).filter
      (fun J => (J.card, (avail G I J).card) = (j, m)),
      (if J.card ≤ r then (avail G I J).card.choose (r - J.card) else 0) =
        (if j ≤ r then m.choose (r - j) else 0) := by
    intro J hJ
    rw [Finset.mem_filter, Prod.mk.injEq] at hJ
    rw [hJ.2.1, hJ.2.2]
  rw [Finset.sum_congr rfl hval, Finset.sum_const, smul_eq_mul]
  congr 1
  unfold tCount
  congr 1
  ext J
  simp only [Finset.mem_filter, Finset.mem_powerset, Prod.mk.injEq]
  tauto

omit [DecidableEq V] in
theorem avail_card_eq_of_card_zero {I J : Finset V} (hJ : J.card = 0) :
    (avail G I J).card = I.card := by
  rw [Finset.card_eq_zero.mp hJ, avail_empty]

/-- `t_{0,m} = [m = |I|]`: the only `J` of size `0` is `∅`, with `I \ N_I(∅) = I`. -/
theorem tCount_zero (s I : Finset V) (m : ℕ) :
    tCount G s I 0 m = if m = I.card then 1 else 0 := by
  unfold tCount
  have h : (s \ I).powerset.filter
      (fun J => IsIndepFinset G J ∧ J.card = 0 ∧ (avail G I J).card = m) =
        if m = I.card then {∅} else ∅ := by
    ext J
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.card_eq_zero]
    split_ifs with hm
    · rw [Finset.mem_singleton]
      constructor
      · rintro ⟨-, -, hJ, -⟩
        exact hJ
      · rintro rfl
        refine ⟨Finset.empty_subset _, isIndepFinset_empty, rfl, ?_⟩
        rw [avail_empty, hm]
    · simp only [Finset.notMem_empty, iff_false]
      rintro ⟨-, -, rfl, hJm⟩
      rw [avail_empty] at hJm
      exact hm hJm.symm
  rw [h]
  split_ifs <;> simp

/-- `t_{j,m} = 0` when `j + m > α(G[s])`: `J ∪ (I \ N_I(J))` is an independent subset of `s` with
`j + m` vertices (for a maximum `I`, this is the paper's `j + m ≤ a`). -/
theorem tCount_eq_zero_of_alphaIn_lt {s I : Finset V} (hI : IsIndepFinset G I) (hIs : I ⊆ s)
    {j m : ℕ} (h : alphaIn G s < j + m) : tCount G s I j m = 0 := by
  unfold tCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro J hJ ⟨hJi, hJc, hJm⟩
  rw [Finset.mem_powerset] at hJ
  have hdisj : Disjoint J (avail G I J) := by
    rw [Finset.disjoint_left]
    intro x hxJ hxA
    exact (Finset.mem_sdiff.mp (hJ hxJ)).2 (avail_subset G I J hxA)
  have hind := isIndepFinset_union_avail hI hJi (subset_refl (avail G I J))
  have hsub : J ∪ avail G I J ⊆ s :=
    Finset.union_subset (hJ.trans Finset.sdiff_subset) ((avail_subset G I J).trans hIs)
  have hle := le_alphaIn hsub hind
  rw [Finset.card_union_of_disjoint hdisj, hJc, hJm] at hle
  omega

/-- `T_j = Σ_m t_{j,m}` is the number of independent `j`-subsets of `s \ I`. -/
theorem sum_tCount (s I : Finset V) (j : ℕ) :
    ∑ m ∈ range (I.card + 1), tCount G s I j m = indepCount G (s \ I) j := by
  unfold tCount indepCount
  rw [← Finset.card_biUnion]
  · congr 1
    ext J
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨m, -, hJ, hJi, hJc, -⟩
      exact ⟨⟨hJ, hJi⟩, hJc⟩
    · rintro ⟨⟨hJ, hJi⟩, hJc⟩
      exact ⟨(avail G I J).card,
        Nat.lt_succ_of_le (Finset.card_le_card (avail_subset G I J)), hJ, hJi, hJc, rfl⟩
  · intro m _ m' _ hmm'
    rw [Function.onFun, Finset.disjoint_left]
    intro J hJ hJ'
    rw [Finset.mem_filter] at hJ hJ'
    exact hmm' (hJ.2.2.2.symm.trans hJ'.2.2.2)

omit [DecidableEq V] in
/-- `T_1 = |Y|`: every single vertex is independent. -/
theorem indepCount_one (Y : Finset V) : indepCount G Y 1 = Y.card := by
  unfold indepCount
  rw [Finset.filter_filter]
  have h : Y.powerset.filter (fun t => IsIndepFinset G t ∧ t.card = 1) = Y.powersetCard 1 := by
    ext t
    rw [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
    constructor
    · rintro ⟨h1, -, h2⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_, h2⟩
      obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h2
      intro x hx y hy hxy
      rw [Finset.mem_singleton] at hx hy
      rw [hx, hy] at hxy
      exact G.irrefl hxy
  rw [h, Finset.card_powersetCard, Nat.choose_one_right]

omit [DecidableEq V] in
/-- `T_j ≤ W_j = C(|Y|, j)`. -/
theorem indepCount_le_choose (Y : Finset V) (j : ℕ) : indepCount G Y j ≤ Y.card.choose j := by
  unfold indepCount
  rw [← Finset.card_powersetCard]
  apply Finset.card_le_card
  intro t ht
  rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_powerset] at ht
  exact Finset.mem_powersetCard.mpr ⟨ht.1.1, ht.2⟩

/-- **The basic constraints (5)**: `T_1 = v` and `T_j ≤ C(v, j)` with `v = |s \ I|`. -/
theorem sum_tCount_one (s I : Finset V) :
    ∑ m ∈ range (I.card + 1), tCount G s I 1 m = (s \ I).card := by
  rw [sum_tCount, indepCount_one]

theorem sum_tCount_le_choose (s I : Finset V) (j : ℕ) :
    ∑ m ∈ range (I.card + 1), tCount G s I j m ≤ (s \ I).card.choose j := by
  rw [sum_tCount]
  exact indepCount_le_choose _ j

/-- **Zhang (3), the paper's display**: for an independent `I ⊆ s` of maximum size
(`|I| = α(G[s]) = a`) and `v = |s \ I|`,
`c_r = C(a, r) + Σ_{j=1}^{v} Σ_{m=0}^{a−j} [j ≤ r] C(m, r − j) t_{j,m}`. -/
theorem indepCount_eq_paper {s I : Finset V} (hI : IsIndepFinset G I) (hIs : I ⊆ s)
    (hmax : I.card = alphaIn G s) (r : ℕ) :
    indepCount G s r = I.card.choose r + ∑ j ∈ Finset.Icc 1 (s \ I).card,
      ∑ m ∈ range (I.card - j + 1), tCount G s I j m * (if j ≤ r then m.choose (r - j) else 0) := by
  rw [indepCount_eq_sum_tCount hI hIs r, Finset.sum_range_succ', add_comm]
  congr 1
  · -- the layer `j = 0`
    simp [tCount_zero]
  · -- the layers `j ≥ 1`: reindex, then drop the vanishing counts with `m > a - j`
    symm
    refine Finset.sum_nbij' (fun j => j - 1) (fun i => i + 1) ?_ ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_Icc, Finset.mem_range] at hj ⊢
      omega
    · intro i hi
      simp only [Finset.mem_Icc, Finset.mem_range] at hi ⊢
      omega
    · intro j hj
      simp only [Finset.mem_Icc] at hj ⊢
      omega
    · intro i _
      omega
    · intro j hj
      rw [Finset.mem_Icc] at hj
      have hj' : j - 1 + 1 = j := by omega
      simp only [hj']
      apply Finset.sum_subset
      · intro m hm
        rw [Finset.mem_range] at hm ⊢
        omega
      · intro m hm hm'
        rw [Finset.mem_range] at hm hm'
        rw [tCount_eq_zero_of_alphaIn_lt hI hIs (by omega), zero_mul]

end Zhang
end Erdos993Lean
