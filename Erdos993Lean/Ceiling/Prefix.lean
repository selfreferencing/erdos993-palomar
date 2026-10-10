module

public import Mathlib
public import Erdos993Lean.IndependencePoly

/-!
# The rising prefix of every forest (ceiling proof, Appendix R1)

For every finite forest on `n` vertices and every `k`,
`(k + 1) · i_{k+1} ≥ (n - 3k) · i_k`.
Equivalently the polynomial `(1 + 3x) I'(x) - n I(x)` has nonnegative coefficients.

Proof: induction on the vertex set.  For a leaf `l` with neighbour
`u`, writing `𝒟(F) := (1 + 3x) I_F' - |F| I_F`,
`𝒟(F) = 𝒟(F - l) + x 𝒟(F - l - u) + x (I(F - l - u) - I(F - N[u]))`,
and the last bracket has nonnegative coefficients because `F - N[u] ⊆ F - l - u`.  For an isolated
vertex `w`, `𝒟(F) = (1 + x) 𝒟(F - w) + 2x I(F - w)`.  The empty forest has `𝒟 = 0`.

Consequence: `i_k ≤ i_{k+1}` whenever `4k + 1 ≤ n`, so the independence sequence of every forest
is nondecreasing up to index `⌈n/4⌉`.

Provenance: this is the telescoped form of "Lemma 1" (the universal
two-extension inequality `(k + 2) i_k i_{k+2} + 3 i_k i_{k+1} ≥ (k + 1) i_{k+1}²` for every forest:
the average number of addable vertices drops by at most 3 per rank),
which is stronger step by step.
-/

@[expose] public section

namespace Erdos993Lean

open Polynomial Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The degree-score polynomial `(1 + 3x) I'(x) - |s| I(x)` of the subgraph induced on `s`. -/
noncomputable def prefixPoly (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) : ℤ[X] :=
  (1 + 3 * X) * derivative (indepPoly G s) - (s.card : ℤ[X]) * indepPoly G s

/-- In an acyclic graph every nonempty finite vertex set contains a vertex with at most one
neighbour inside the set. -/
theorem IsAcyclic.exists_le_one_nbr (hG : G.IsAcyclic) {s : Finset V} (hs : s.Nonempty) :
    ∃ v ∈ s, (s.filter (G.Adj v)).card ≤ 1 := by
  by_contra hcon
  push_neg at hcon
  -- If every vertex of `s` had two neighbours in `s`, paths inside `s` could be extended forever:
  -- a second neighbour of the start vertex is off the path, since the graph is acyclic.
  have key : ∀ n : ℕ, ∃ (u b : V) (p : G.Walk u b), p.IsPath ∧ (∀ x ∈ p.support, x ∈ s) ∧
      p.length = n := by
    intro n
    induction n with
    | zero =>
      obtain ⟨x, hx⟩ := hs
      exact ⟨x, x, SimpleGraph.Walk.nil, SimpleGraph.Walk.IsPath.nil, by simpa using hx, rfl⟩
    | succ n ih =>
      obtain ⟨u, b, p, hp, hps, hpl⟩ := ih
      have hu : u ∈ s := hps u p.start_mem_support
      obtain ⟨w, hw, hwne⟩ := Finset.exists_mem_ne (hcon u hu) (p.getVert 1)
      rw [Finset.mem_filter] at hw
      have hwp : w ∉ p.support := by
        intro hwp
        -- the initial segment of `p` up to `w` is the one-edge path `u w`
        have huniq := congrArg Subtype.val
          (hG.path_unique ⟨p.takeUntil w hwp, hp.takeUntil hwp⟩ (SimpleGraph.Path.singleton hw.2))
        apply hwne
        rw [← p.take_spec hwp]
        simp only [SimpleGraph.Path.singleton] at huniq
        rw [huniq]
        simp
      refine ⟨w, b, SimpleGraph.Walk.cons hw.2.symm p, ?_, ?_, ?_⟩
      · exact hp.cons hwp
      · intro x hx
        rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hw.1
        · exact hps x hx
      · simp [hpl]
  -- A path inside `s` has at most `|s|` vertices.
  obtain ⟨u, b, p, hp, hps, hpl⟩ := key s.card
  have h1 : p.support.toFinset ⊆ s := fun x hx => hps x (List.mem_toFinset.mp hx)
  have h2 := Finset.card_le_card h1
  rw [List.toFinset_card_of_nodup hp.support_nodup, SimpleGraph.Walk.length_support, hpl] at h2
  omega

/-! ### Helpers: monotonicity of counts, nonnegative coefficients, the two recurrences

These live in the namespace `Erdos993Lean.Ceiling`. -/

namespace Ceiling

omit [DecidableEq V] in
/-- Independence counts are monotone under inclusion of the vertex set. -/
theorem indepCount_mono {s t : Finset V} (hst : s ⊆ t) (k : ℕ) :
    indepCount G s k ≤ indepCount G t k := by
  unfold indepCount
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  apply Finset.filter_subset_filter
  exact Finset.powerset_mono.mpr hst

/-- A polynomial all of whose coefficients are nonnegative. -/
def CoeffNonneg (p : ℤ[X]) : Prop :=
  ∀ k, 0 ≤ p.coeff k

theorem CoeffNonneg.add {p q : ℤ[X]} (hp : CoeffNonneg p) (hq : CoeffNonneg q) :
    CoeffNonneg (p + q) := fun k => by
  rw [coeff_add]
  exact add_nonneg (hp k) (hq k)

theorem CoeffNonneg.X_mul {p : ℤ[X]} (hp : CoeffNonneg p) : CoeffNonneg (X * p) := fun k => by
  cases k with
  | zero => rw [coeff_X_mul_zero]
  | succ k => rw [coeff_X_mul]; exact hp k

omit [DecidableEq V] in
theorem indepPoly_coeffNonneg (s : Finset V) : CoeffNonneg (indepPoly G s) := fun k => by
  rw [indepPoly_coeff]
  exact Nat.cast_nonneg _

omit [DecidableEq V] in
theorem indepPoly_sub_coeffNonneg {s t : Finset V} (hst : s ⊆ t) :
    CoeffNonneg (indepPoly G t - indepPoly G s) := fun k => by
  rw [coeff_sub, indepPoly_coeff, indepPoly_coeff, sub_nonneg]
  exact_mod_cast indepCount_mono hst k

omit [DecidableEq V] in
theorem prefixPoly_empty : prefixPoly G (∅ : Finset V) = 0 := by
  rw [prefixPoly, indepPoly_empty, derivative_one, Finset.card_empty]
  simp

/-- The leaf recurrence: for `l ∈ s` whose only neighbour in `s` is `u`,
`𝒟(s) = 𝒟(s - l) + x 𝒟(s - l - u) + x (I(s - l - u) - I((s - l) - N[u]))`. -/
theorem prefixPoly_leaf {s : Finset V} {l u : V} (hl : l ∈ s) (hnbr : s.filter (G.Adj l) = {u}) :
    prefixPoly G s = prefixPoly G (s.erase l) + X * prefixPoly G ((s.erase l).erase u) +
      X * (indepPoly G ((s.erase l).erase u) - indepPoly G (outsideClosedNbhd G (s.erase l) u)) := by
  have hu : u ∈ s.filter (G.Adj l) := by
    rw [hnbr]
    exact Finset.mem_singleton_self u
  rw [Finset.mem_filter] at hu
  have hul : u ≠ l := hu.2.ne.symm
  have hu' : u ∈ s.erase l := Finset.mem_erase.mpr ⟨hul, hu.1⟩
  have hout : outsideClosedNbhd G s l = (s.erase l).erase u := by
    ext w
    simp only [outsideClosedNbhd, Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hws, hwl, hadj⟩
      refine ⟨?_, hwl, hws⟩
      rintro rfl
      exact hadj hu.2
    · rintro ⟨hwu, hwl, hws⟩
      refine ⟨hws, hwl, fun hadj => hwu ?_⟩
      have : w ∈ s.filter (G.Adj l) := Finset.mem_filter.mpr ⟨hws, hadj⟩
      rw [hnbr] at this
      exact Finset.mem_singleton.mp this
  have h1 := indepPoly_erase_add G hl
  rw [hout] at h1
  have h2 := indepPoly_erase_add G hu'
  have hc1 : s.card = (s.erase l).card + 1 := (Finset.card_erase_add_one hl).symm
  have hc2 : (s.erase l).card = ((s.erase l).erase u).card + 1 :=
    (Finset.card_erase_add_one hu').symm
  unfold prefixPoly
  rw [h1, hc1, hc2]
  simp only [derivative_add, derivative_mul, derivative_X, Nat.cast_add, Nat.cast_one]
  linear_combination (-1 : ℤ[X]) * h2

/-- The isolated-vertex recurrence: for `l ∈ s` with no neighbour in `s`,
`𝒟(s) = (1 + x) 𝒟(s - l) + 2x I(s - l)`. -/
theorem prefixPoly_isolated {s : Finset V} {l : V} (hl : l ∈ s) (hnbr : s.filter (G.Adj l) = ∅) :
    prefixPoly G s = (1 + X) * prefixPoly G (s.erase l) + 2 * X * indepPoly G (s.erase l) := by
  have hout : outsideClosedNbhd G s l = s.erase l := by
    ext w
    simp only [outsideClosedNbhd, Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hws, hwl, _⟩
      exact ⟨hwl, hws⟩
    · rintro ⟨hwl, hws⟩
      refine ⟨hws, hwl, fun hadj => ?_⟩
      have : w ∈ s.filter (G.Adj l) := Finset.mem_filter.mpr ⟨hws, hadj⟩
      rw [hnbr] at this
      exact Finset.notMem_empty w this
  have h1 := indepPoly_erase_add G hl
  rw [hout] at h1
  have hc1 : s.card = (s.erase l).card + 1 := (Finset.card_erase_add_one hl).symm
  unfold prefixPoly
  rw [h1, hc1]
  simp only [derivative_add, derivative_mul, derivative_X, Nat.cast_add, Nat.cast_one]
  ring

/-- **L394**, polynomial form: induction on the vertex set, removing a vertex with at most one
neighbour in the set. -/
theorem prefixPoly_coeffNonneg (hG : G.IsAcyclic) (s : Finset V) :
    CoeffNonneg (prefixPoly G s) := by
  induction s using Finset.strongInduction with
  | H s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · rw [prefixPoly_empty]
      intro k
      rw [coeff_zero]
    · obtain ⟨l, hl, hdeg⟩ := IsAcyclic.exists_le_one_nbr hG hs
      have hlt : s.erase l ⊂ s := Finset.erase_ssubset hl
      have hP := ih _ hlt
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hdeg with h0 | h1
      · -- `l` is isolated in `s`
        rw [Finset.card_eq_zero] at h0
        rw [prefixPoly_isolated hl h0]
        have hA := indepPoly_coeffNonneg (G := G) (s.erase l)
        have e : (1 + X) * prefixPoly G (s.erase l) + 2 * X * indepPoly G (s.erase l) =
            prefixPoly G (s.erase l) + X * prefixPoly G (s.erase l) +
              X * indepPoly G (s.erase l) + X * indepPoly G (s.erase l) := by ring
        rw [e]
        exact ((hP.add hP.X_mul).add hA.X_mul).add hA.X_mul
      · -- `l` is a leaf of `s` with neighbour `u`
        obtain ⟨u, hu⟩ := Finset.card_eq_one.mp h1
        rw [prefixPoly_leaf hl hu]
        have hlt2 : (s.erase l).erase u ⊂ s := (Finset.erase_subset u _).trans_ssubset hlt
        have hsub : outsideClosedNbhd G (s.erase l) u ⊆ (s.erase l).erase u := by
          intro w hw
          simp only [outsideClosedNbhd, Finset.mem_filter] at hw
          exact Finset.mem_erase.mpr ⟨hw.2.1, hw.1⟩
        exact (hP.add (ih _ hlt2).X_mul).add (indepPoly_sub_coeffNonneg hsub).X_mul

omit [DecidableEq V] in
/-- The coefficients of the degree-score polynomial:
`[x^k] 𝒟(s) = (k + 1) i_{k+1} + 3k i_k - |s| i_k`. -/
theorem prefixPoly_coeff (s : Finset V) (k : ℕ) :
    (prefixPoly G s).coeff k = ((k : ℤ) + 1) * indepCount G s (k + 1) +
      3 * k * indepCount G s k - s.card * indepCount G s k := by
  have e : prefixPoly G s = derivative (indepPoly G s) + 3 * (X * derivative (indepPoly G s)) -
      (s.card : ℤ[X]) * indepPoly G s := by
    unfold prefixPoly
    ring
  rw [e, coeff_sub, coeff_add, coeff_ofNat_mul, coeff_natCast_mul, coeff_derivative]
  cases k with
  | zero =>
    rw [coeff_X_mul_zero]
    simp only [indepPoly_coeff]
    push_cast
    ring
  | succ k =>
    rw [coeff_X_mul, coeff_derivative]
    simp only [indepPoly_coeff]
    push_cast
    ring

end Ceiling

/-- **L394**: the degree-score polynomial of every forest has nonnegative coefficients. -/
theorem prefixPoly_coeff_nonneg (hG : G.IsAcyclic) (s : Finset V) (k : ℕ) :
    0 ≤ (prefixPoly G s).coeff k := by
  exact Ceiling.prefixPoly_coeffNonneg hG s k

/-- **L394, coefficient form**: `(n - 3k) i_k ≤ (k + 1) i_{k+1}` for every forest. -/
theorem prefix_inequality (hG : G.IsAcyclic) (s : Finset V) (k : ℕ) :
    ((s.card : ℤ) - 3 * k) * indepCount G s k ≤ (k + 1) * indepCount G s (k + 1) := by
  have h := prefixPoly_coeff_nonneg hG s k
  rw [Ceiling.prefixPoly_coeff] at h
  linarith

/-- The rising prefix: `i_k ≤ i_{k+1}` whenever `4k + 1 ≤ n`. -/
theorem indepCount_le_succ_of_prefix (hG : G.IsAcyclic) (s : Finset V) {k : ℕ}
    (hk : 4 * k + 1 ≤ s.card) : indepCount G s k ≤ indepCount G s (k + 1) := by
  have h := prefix_inequality hG s k
  have hk' : ((k : ℤ) + 1) ≤ (s.card : ℤ) - 3 * k := by
    have : ((4 * k + 1 : ℕ) : ℤ) ≤ (s.card : ℤ) := by exact_mod_cast hk
    push_cast at this
    linarith
  have h2 : ((k : ℤ) + 1) * indepCount G s k ≤ ((k : ℤ) + 1) * indepCount G s (k + 1) :=
    le_trans (mul_le_mul_of_nonneg_right hk' (Nat.cast_nonneg _)) h
  have h3 : (indepCount G s k : ℤ) ≤ indepCount G s (k + 1) :=
    le_of_mul_le_mul_left h2 (by positivity)
  exact_mod_cast h3

end Erdos993Lean
