module

public import Erdos993Lean.Analytic.Window
public import Erdos993Lean.Analytic.Translate
public import Erdos993Lean.Ceiling.ValleyFree

/-!
# The conditional top theorem of the analytic route, certificate-free core

Interface:
`Analytic/Defs.lean`.  Sources: T. Zhang, *Exact Certificates for Unimodality of Forest Independence Polynomials*,
v1.1, (45)–(50) (the conditional binomial mixture over a maximum-weight independent set) and §5.3 (stitching);
the notes T1 (the no-valley lemma) and T23 (the
forest inputs).

This module holds the two top-level theorems that use no finite certificate of Zhang's; it imports
nothing under `Erdos993Lean.Zhang.Rows`, `Erdos993Lean.ZhangKernel` or `Erdos993Lean.ZhangCert`, so that the
no-certificates proof (`Erdos993Lean.Analytic.MGF.N27.erdos993_noZhang`) has a certificate-free import closure.
The theorem that uses Zhang's finite part
(`Zhang.Rows.finite60_of_certificates`) is kept apart.  The statements and proofs are unchanged.

* `unimodal_of_noWeakValley_window`: the combinatorial assembly for one forest.  The rising prefix
  below `⌈n/4⌉`, the tail B6 against `B_F` from `h_B` on (as in `ceiling_of_R221Inputs`), and
  no weak valley at the interior ranks `⌈n/4⌉ < k < h_B` give a unimodal independence sequence
  (`unimodal_of_prefix_valleyFree_tail`).
* `noWeakValley_of_analytic_inputs`: for a forest with `n ≥ 61`, the mixture facts
  (`MixtureFacts`) and the inputs O1–O5 (`AnalyticInputs P`) exclude a weak valley at every interior
  rank `k`.  Select `t ∈ (1/3, 7/3)` with `μ_F(t) = k` (`exists_activity_eq`, B5), a maximum-weight
  independent set `B`, the mixture `X = forestMixture F B t` and `m = E M`.  The hypotheses of
  `NoValleyAt (actQ t) m θ D T M1` hold: `X` is a probability mixture, `E δ = 0`,
  `E δ² = V − q(1 − q) m ≤ θ q(1 − q) m` (O2 with `q m = W`), `Var M ≤ D m` (O1), the tails (O3);
  `m ≥ mfloor(t)` (O5) places `m` in the domain of the no-valley property (O4).  The
  weak-valley translation (`not_valley_of_not_weakValley`, with `MixtureFacts.prob_eq`) moves the
  conclusion to the counts.

Scalarity check: the numerical parameters are the fields of the profile `P`, evaluated at the
selected activity `t` and at `m = E M` of the forest mixture: `θb t` summarizes the second moment of
`δ` (produced by O2, consumed by O4/T1), `Db t` the variance of the free count `M` (O1 → O4/T1),
`Tb t m` and `M1b t m` the lower tail of `M` below the cutoff (O3 → O4/T1), `mfloor t` the expected
free count `m` (O5 → O4).  Nothing else is carried between the steps.
-/

@[expose] public section

namespace Erdos993Lean.Analytic

open Finset

/-- **The combinatorial assembly for one forest.**  If the independence sequence of `F` has no weak
valley at any interior window rank `⌈n/4⌉ < k < h_B`, it is unimodal: the rising prefix covers
the ranks below `⌈n/4⌉`, the tail inequality B6 against the row `B_F` covers the ranks from `h_B`
on, and `unimodal_of_prefix_valleyFree_tail` stitches them. -/
theorem unimodal_of_noWeakValley_window (F : FiniteForest)
    (hvf : ∀ k, (F.n + 3) / 4 < k → k < hB F →
      ¬ (independenceCount F k ≤ independenceCount F (k - 1) ∧
          independenceCount F k ≤ independenceCount F (k + 1))) :
    Unimodal (independenceCount F) := by
  classical
  have hcount : independenceCount F = fun k => (F.graph.indepSetFinset k).card := by
    funext k
    unfold independenceCount
    rfl
  -- counts vanish above `n - ν`
  have hzero : ∀ j, F.n - matchingNumber F.graph < j → independenceCount F j = 0 := by
    intro j hj
    rw [hcount]
    show (F.graph.indepSetFinset j).card = 0
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro t ht
    rw [SimpleGraph.mem_indepSetFinset_iff] at ht
    have h1 := Ceiling.card_add_matchingNumber_le F.graph t ht.isIndepSet
    rw [ht.card_eq] at h1
    omega
  -- the row `B_F`
  obtain ⟨hbLC, hbPos⟩ := Ceiling.bRow_good F.n (matchingNumber F.graph)
  have hbU : Unimodal (bRow F.n (matchingNumber F.graph)) :=
    unimodal_of_logConcave hbLC hbPos.noInternalZeros hbPos.finitelySupported
  have hbanti := Ceiling.firstMode_antitone hbU
  apply unimodal_of_prefix_valleyFree_tail (L := (F.n + 3) / 4) (U := hB F)
  · -- the rising prefix
    intro k hk
    have h4 : 4 * k + 1 ≤ (Finset.univ : Finset (Fin F.n)).card := by
      rw [Finset.card_univ, Fintype.card_fin]
      omega
    have h5 := indepCount_le_succ_of_prefix F.isForest Finset.univ h4
    rw [indepCount_univ, indepCount_univ] at h5
    rw [hcount]
    exact h5
  · -- no weak valley at the interior ranks
    intro k hLk hkU h1 h2
    exact hvf k hLk hkU ⟨h1, h2⟩
  · -- the tail B6 against the nonincreasing tail of `B_F`
    intro k hk
    have ht := tail_inequality F (k + 1) (by omega)
    simp only [Nat.add_sub_cancel] at ht
    have hbk : bRow F.n (matchingNumber F.graph) (k + 1) ≤ bRow F.n (matchingNumber F.graph) k :=
      hbanti k hk
    rcases Nat.eq_zero_or_pos (bRow F.n (matchingNumber F.graph) k) with h0 | hpos
    · have hkD : matchingNumber F.graph + (F.n - 2 * matchingNumber F.graph) < k := by
        by_contra hcon
        push_neg at hcon
        exact (hbPos.1 k hcon).ne' h0
      rw [hzero (k + 1) (by omega)]
      exact Nat.zero_le _
    · exact Nat.le_of_mul_le_mul_right (le_trans ht (Nat.mul_le_mul_left _ hbk)) hpos

/-- **No weak valley at the interior ranks, from the analytic inputs.**  For a forest with at least
61 vertices, the mixture facts (Zhang (45)–(46)) and the inputs O1–O5 exclude
`i_k ≤ i_{k−1} ∧ i_k ≤ i_{k+1}` at every rank `⌈n/4⌉ < k < h_B`. -/
theorem noWeakValley_of_analytic_inputs (hmix : MixtureFacts) {P : Profile}
    (h : AnalyticInputs P) (F : FiniteForest) (hn : 61 ≤ F.n) (k : ℕ)
    (hk1 : (F.n + 3) / 4 < k) (hk2 : k < hB F) :
    ¬ (independenceCount F k ≤ independenceCount F (k - 1) ∧
        independenceCount F k ≤ independenceCount F (k + 1)) := by
  -- the activity with `μ_F(t) = k` (O6, option (b)) and a maximum-weight independent set
  obtain ⟨t, hR, ht, hI, hμ⟩ := exists_activity_inRange F k hk1 hk2
  obtain ⟨B, hBmax⟩ := hmix.exists_maxWeight F t ht
  have hBind : F.graph.IsIndepSet (B : Set (Fin F.n)) := hBmax.1
  -- the no-valley property at `q = t/(1 + t)` and `m = E M`: O5 gives `m ≥ mfloor t`, then O4
  have hNV := h.o4 t hR (forestMixture F B t).meanM (h.o5 F hn t hR hI B hBmax)
  -- the second moment of `δ`: `E δ² = V − q(1 − q) m ≤ θ q(1 − q) m` (O2 and `q m = W`)
  have hδ2 : (forestMixture F B t).expect (fun M Y => delta (actQ t) k M Y ^ 2) ≤
      P.θb t * (actQ t * (1 - actQ t)) * (forestMixture F B t).meanM := by
    rw [hmix.var_delta F t B ht hBind k hμ]
    have hO2 := h.o2 F hn t hR hI B hBmax
    rw [← hmix.weight_eq F t B ht hBind] at hO2
    linarith
  -- T1's conclusion for the forest mixture
  have hnv : ¬ (forestMixture F B t).WeakValley (actQ t) k :=
    hNV (Finset (Fin F.n)) (forestMixture F B t) k (hmix.isProb F t B ht hBind) rfl
      (hmix.mean_delta F t B ht hBind k hμ) hδ2 (h.o1 F hn t hR hI B hBmax)
      (h.o3 F hn t hR hI B hBmax)
  -- back to the counts
  exact not_valley_of_not_weakValley F (forestMixture F B t) ht (by omega)
    (hmix.prob_eq F t B ht hBind (k - 1)) (hmix.prob_eq F t B ht hBind k)
    (hmix.prob_eq F t B ht hBind (k + 1)) hnv

end Erdos993Lean.Analytic
