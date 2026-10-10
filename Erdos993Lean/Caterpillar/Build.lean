module

public import Mathlib
public import Erdos993Lean.IndependencePoly
public import Erdos993Lean.Caterpillar.PropertyP

/-!
# Growing a rooted vertex set by the letters S, L, E

Inside a fixed graph `G`, `Build G s r` says that the vertex set `s`, with root `r`, is obtained
from a single vertex by the three letters:
* `S`: add a new vertex adjacent (within the current set) exactly to the root; it becomes the root;
* `L`: add a pendant leaf at the root; the root is kept;
* `E`: add a pendant two-vertex path `r - a - b` at the root; the root is kept.

`Build.propP`: for every such `(s, r)`, the pair `(I(G[s]), I(G[s - r]))` satisfies property `P`.
Consequently `I(G[s])` is log-concave (`Build.logConcave`).
-/

@[expose] public section

namespace Erdos993Lean

open Polynomial Finset PropertyP

/-- The coefficient sequence of an integer polynomial, indexed by `ℤ` (zero at negative
indices). -/
noncomputable def coeffZ (p : ℤ[X]) : ZSeq := fun k => if 0 ≤ k then p.coeff k.toNat else 0

theorem coeffZ_add (p q : ℤ[X]) (k : ℤ) : coeffZ (p + q) k = coeffZ p k + coeffZ q k := by
  unfold coeffZ
  split_ifs <;> simp [Polynomial.coeff_add]

theorem coeffZ_X_mul (p : ℤ[X]) (k : ℤ) : coeffZ (X * p) k = coeffZ p (k - 1) := by
  unfold coeffZ
  by_cases hk : 1 ≤ k
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = (n : ℤ) + 1 := ⟨(k - 1).toNat, by omega⟩
    have h0 : (0 : ℤ) ≤ (n : ℤ) + 1 := by omega
    have h1 : (0 : ℤ) ≤ (n : ℤ) + 1 - 1 := by omega
    rw [if_pos h0, if_pos h1]
    have e1 : ((n : ℤ) + 1).toNat = n + 1 := by omega
    have e2 : ((n : ℤ) + 1 - 1).toNat = n := by omega
    rw [e1, e2, Polynomial.coeff_X_mul]
  · have h1 : ¬ (0 : ℤ) ≤ k - 1 := by omega
    rw [if_neg h1]
    split_ifs with h0
    · have hk0 : k = 0 := by omega
      subst hk0
      simp
    · rfl

theorem coeffZ_C_mul (a : ℤ) (p : ℤ[X]) (k : ℤ) : coeffZ (C a * p) k = a * coeffZ p k := by
  unfold coeffZ
  split_ifs <;> simp

/-- `coeffZ` at a natural index is the ordinary coefficient. -/
theorem coeffZ_natCast (p : ℤ[X]) (n : ℕ) : coeffZ p (n : ℤ) = p.coeff n := by
  simp [coeffZ]

/-- `coeffZ` vanishes at negative indices. -/
theorem coeffZ_of_neg (p : ℤ[X]) {k : ℤ} (hk : k < 0) : coeffZ p k = 0 := by
  simp [coeffZ, not_le.mpr hk]

section Build

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `Build G s r`: the rooted vertex set `(s, r)` grows from a single vertex by the letters
`S`, `L`, `E`. -/
inductive Build : Finset V → V → Prop
  | single (v : V) : Build {v} v
  | S {s : Finset V} {r v : V} : Build s r → v ∉ s → (∀ u ∈ s, G.Adj v u ↔ u = r) →
      Build (insert v s) v
  | L {s : Finset V} {r l : V} : Build s r → l ∉ s → (∀ u ∈ s, G.Adj l u ↔ u = r) →
      Build (insert l s) r
  | E {s : Finset V} {r a b : V} : Build s r → a ∉ s → b ∉ s → a ≠ b →
      (∀ u ∈ s, G.Adj a u ↔ u = r) → G.Adj a b → (∀ u ∈ s, ¬ G.Adj b u) →
      Build (insert b (insert a s)) r

variable {G}

-- The statement keeps the section's `[DecidableRel G.Adj]` (unused here); silence the linter
-- rather than change the statement.
set_option linter.unusedSectionVars false in
theorem Build.root_mem {s : Finset V} {r : V} (h : Build G s r) : r ∈ s := by
  induction h with
  | single v => exact Finset.mem_singleton_self v
  | S _ _ _ _ => exact Finset.mem_insert_self _ _
  | L _ _ _ ih => exact Finset.mem_insert_of_mem ih
  | E _ _ _ _ _ _ _ ih => exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ih)

/-- Adding a vertex `v` whose only neighbour in `t` is `r`:
`I(t + v) = I(t) + x · I(t - r)`. -/
theorem Build.indepPoly_insert_of_unique_nbr {t : Finset V} {v r : V} (hv : v ∉ t)
    (hadj : ∀ u ∈ t, G.Adj v u ↔ u = r) :
    indepPoly G (insert v t) = indepPoly G t + X * indepPoly G (t.erase r) := by
  have hN : outsideClosedNbhd G (insert v t) v = t.erase r := by
    ext w
    simp only [outsideClosedNbhd, Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ⟨h1 | h1, h2, h3⟩
      · exact absurd h1 h2
      · exact ⟨fun hw => h3 ((hadj w h1).mpr hw), h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨Or.inr h2, fun hw => hv (hw ▸ h2), fun hw => h1 ((hadj w h2).mp hw)⟩
  rw [indepPoly_erase_add G (Finset.mem_insert_self v t), Finset.erase_insert hv, hN]

/-- Adding a vertex `v` with no neighbour in `t`: `I(t + v) = I(t) + x · I(t)`. -/
theorem Build.indepPoly_insert_of_no_nbr {t : Finset V} {v : V} (hv : v ∉ t)
    (hadj : ∀ u ∈ t, ¬ G.Adj v u) :
    indepPoly G (insert v t) = indepPoly G t + X * indepPoly G t := by
  have hN : outsideClosedNbhd G (insert v t) v = t := by
    ext w
    simp only [outsideClosedNbhd, Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨h1 | h1, h2, _⟩
      · exact absurd h1 h2
      · exact h1
    · intro h1
      exact ⟨Or.inr h1, fun hw => hv (hw ▸ h1), hadj w h1⟩
  rw [indepPoly_erase_add G (Finset.mem_insert_self v t), Finset.erase_insert hv, hN]

/-- Soundness: every built rooted set carries property `P`. -/
theorem Build.propP {s : Finset V} {r : V} (h : Build G s r) :
    P (coeffZ (indepPoly G s)) (coeffZ (indepPoly G (s.erase r))) := by
  induction h with
  | single v =>
    rw [Finset.erase_singleton, indepPoly_singleton, indepPoly_empty]
    have hZ : coeffZ (1 + X) = fun k => if k = 0 ∨ k = 1 then 1 else 0 := by
      funext k
      rcases lt_or_ge k 0 with hk | hk
      · rw [coeffZ_of_neg _ hk, if_neg (by omega)]
      · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
        rw [coeffZ_natCast]
        rcases n with _ | _ | n
        · simp
        · simp [Polynomial.coeff_one, Polynomial.coeff_X]
        · simp [Polynomial.coeff_one, Polynomial.coeff_X]
          omega
    have hX : coeffZ (1 : ℤ[X]) = fun k => if k = 0 then 1 else 0 := by
      funext k
      rcases lt_or_ge k 0 with hk | hk
      · rw [coeffZ_of_neg _ hk, if_neg (by omega)]
      · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
        rw [coeffZ_natCast]
        rcases n with _ | n
        · simp
        · simp [Polynomial.coeff_one]
          omega
    rw [hZ, hX]
    exact P.single
  | @S s r v hs hv hadj ih =>
    rw [Finset.erase_insert hv, Build.indepPoly_insert_of_unique_nbr hv hadj]
    have hZ : coeffZ (indepPoly G s + X * indepPoly G (s.erase r)) =
        addShift (coeffZ (indepPoly G s)) (coeffZ (indepPoly G (s.erase r))) := by
      funext k
      rw [coeffZ_add, coeffZ_X_mul]
      rfl
    rw [hZ]
    exact ih.S
  | @L s r l hs hl hadj ih =>
    have hr : r ∈ s := hs.root_mem
    have hlr : l ≠ r := fun e => hl (e ▸ hr)
    have hl' : l ∉ s.erase r := fun h' => hl (Finset.mem_of_mem_erase h')
    have hadj' : ∀ u ∈ s.erase r, ¬ G.Adj l u := by
      intro u hu hlu
      exact (Finset.mem_erase.mp hu).1 ((hadj u (Finset.mem_of_mem_erase hu)).mp hlu)
    rw [Finset.erase_insert_of_ne hlr, Build.indepPoly_insert_of_unique_nbr hl hadj,
      Build.indepPoly_insert_of_no_nbr hl' hadj']
    have hZ : coeffZ (indepPoly G s + X * indepPoly G (s.erase r)) =
        addShift (coeffZ (indepPoly G s)) (coeffZ (indepPoly G (s.erase r))) := by
      funext k
      rw [coeffZ_add, coeffZ_X_mul]
      rfl
    have hX : coeffZ (indepPoly G (s.erase r) + X * indepPoly G (s.erase r)) =
        onePlusX (coeffZ (indepPoly G (s.erase r))) := by
      funext k
      rw [coeffZ_add, coeffZ_X_mul]
      rfl
    rw [hZ, hX]
    exact ih.L
  | @E s r a b hs ha hb hab hadja hab' hb' ih =>
    have hr : r ∈ s := hs.root_mem
    have har : a ≠ r := fun e => ha (e ▸ hr)
    have hbr : b ≠ r := fun e => hb (e ▸ hr)
    -- the vertex `b` has exactly one neighbour, `a`, in `insert a s`
    have hb1 : b ∉ insert a s := by
      rw [Finset.mem_insert, not_or]
      exact ⟨fun e => hab e.symm, hb⟩
    have hadjb : ∀ u ∈ insert a s, G.Adj b u ↔ u = a := by
      intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact ⟨fun _ => rfl, fun _ => hab'.symm⟩
      · exact ⟨fun h' => absurd h' (hb' u hu), fun e => absurd (e ▸ hu) ha⟩
    -- the same inside `insert a (s.erase r)`
    have hb2 : b ∉ insert a (s.erase r) := by
      rw [Finset.mem_insert, not_or]
      exact ⟨fun e => hab e.symm, fun h' => hb (Finset.mem_of_mem_erase h')⟩
    have hadjb2 : ∀ u ∈ insert a (s.erase r), G.Adj b u ↔ u = a := by
      intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact ⟨fun _ => rfl, fun _ => hab'.symm⟩
      · have hu' := Finset.mem_of_mem_erase hu
        exact ⟨fun h' => absurd h' (hb' u hu'), fun e => absurd (e ▸ hu') ha⟩
    have ha2 : a ∉ s.erase r := fun h' => ha (Finset.mem_of_mem_erase h')
    have hadja2 : ∀ u ∈ s.erase r, ¬ G.Adj a u := by
      intro u hu hau
      exact (Finset.mem_erase.mp hu).1 ((hadja u (Finset.mem_of_mem_erase hu)).mp hau)
    have hera : (insert a s).erase a = s := Finset.erase_insert ha
    have hera2 : (insert a (s.erase r)).erase a = s.erase r := Finset.erase_insert ha2
    rw [Finset.erase_insert_of_ne hbr, Finset.erase_insert_of_ne har,
      Build.indepPoly_insert_of_unique_nbr hb1 hadjb, hera,
      Build.indepPoly_insert_of_unique_nbr ha hadja,
      Build.indepPoly_insert_of_unique_nbr hb2 hadjb2, hera2,
      Build.indepPoly_insert_of_no_nbr ha2 hadja2]
    have hZ : coeffZ (indepPoly G s + X * indepPoly G (s.erase r) + X * indepPoly G s) =
        eZ (coeffZ (indepPoly G s)) (coeffZ (indepPoly G (s.erase r))) := by
      funext k
      rw [coeffZ_add, coeffZ_add, coeffZ_X_mul, coeffZ_X_mul]
      simp only [eZ]
      ring
    have hX : coeffZ (indepPoly G (s.erase r) + X * indepPoly G (s.erase r) +
        X * indepPoly G (s.erase r)) = eX (coeffZ (indepPoly G (s.erase r))) := by
      funext k
      rw [coeffZ_add, coeffZ_add, coeffZ_X_mul]
      simp only [eX]
      ring
    rw [hZ, hX]
    exact ih.E

/-- Every built vertex set has a log-concave independence sequence. -/
theorem Build.logConcave {s : Finset V} {r : V} (h : Build G s r) :
    LogConcave (indepCount G s) := by
  intro n
  have hD := h.propP.DZ ((n : ℤ) + 1)
  have e0 : ((n : ℤ) + 1 - 1) = ((n : ℕ) : ℤ) := by ring
  have e1 : ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
  have e2 : ((n : ℤ) + 1 + 1) = ((n + 2 : ℕ) : ℤ) := by push_cast; ring
  simp only [D] at hD
  rw [e0, e2, e1, coeffZ_natCast, coeffZ_natCast, coeffZ_natCast, indepPoly_coeff,
    indepPoly_coeff, indepPoly_coeff] at hD
  have h' : ((indepCount G s n * indepCount G s (n + 2) : ℕ) : ℤ) ≤
      ((indepCount G s (n + 1) * indepCount G s (n + 1) : ℕ) : ℤ) := by
    push_cast
    linarith
  exact_mod_cast h'

end Build

end Erdos993Lean
