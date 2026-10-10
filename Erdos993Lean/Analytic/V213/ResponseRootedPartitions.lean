module

public import Erdos993Lean.Analytic.Tail.Rooted

/-!
# Current Section 5: the actual root-deleted partition conventions

Version 2.13 of the manuscript, the definitions preceding Lemma 5.2 and its proof.
`rootE` deletes only the root; `rootC0` deletes its closed neighbourhood; `rootF`
is the full independence partition sum. The finite weighted-partition proofs
in Tail are reused explicitly, with their original authorship retained.
This file uses no variance profile, numerical certificate, or assumed recursion.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse

open Finset

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def rootF (lam : ℝ) (s : Finset V) : ℝ :=
  Tail.Zw G (fun _ => lam) s

noncomputable def rootE (lam : ℝ) (s : Finset V) (v : V) : ℝ :=
  rootF G lam (s.erase v)

noncomputable def rootC0 (lam : ℝ) (s : Finset V) (v : V) : ℝ :=
  rootF G lam (outsideClosedNbhd G s v)

variable {G}

theorem rootF_eq_independent_sum (lam : ℝ) (s : Finset V) :
    rootF G lam s = ∑ I ∈ s.powerset.filter (IsIndepFinset G), lam ^ I.card := by
  classical
  simp only [rootF, Tail.Zw, Finset.prod_const]

theorem rootF_eq_count_sum (lam : ℝ) (s : Finset V) :
    rootF G lam s = ∑ k ∈ Finset.range (s.card + 1),
      (indepCount G s k : ℝ) * lam ^ k :=
  Tail.Zw_const_eq_sum_count lam s

theorem rootF_empty (lam : ℝ) : rootF G lam ∅ = 1 :=
  Tail.Zw_empty (fun _ => lam)

theorem rootF_pos {lam : ℝ} (hlam : 0 ≤ lam) (s : Finset V) :
    0 < rootF G lam s :=
  Tail.Zw_pos (fun _ => hlam) s

theorem rootE_pos {lam : ℝ} (hlam : 0 ≤ lam) (s : Finset V) (v : V) :
    0 < rootE G lam s v :=
  rootF_pos hlam (s.erase v)

theorem rootC0_pos {lam : ℝ} (hlam : 0 ≤ lam) (s : Finset V) (v : V) :
    0 < rootC0 G lam s v :=
  rootF_pos hlam (outsideClosedNbhd G s v)

theorem rootF_delete (lam : ℝ) {s : Finset V} {v : V} (hv : v ∈ s) :
    rootF G lam s = rootE G lam s v + lam * rootC0 G lam s v :=
  Tail.Zw_erase_add (fun _ => lam) hv

theorem rootE_children (hG : G.IsAcyclic) (lam : ℝ) {s : Finset V}
    (hs : ConnectedIn G s) {v : V} (hv : v ∈ s) :
    rootE G lam s v = ∏ w ∈ nbrsIn G s v,
      rootF G lam (compIn G (s.erase v) w) :=
  Tail.Zw_erase_root hG (fun _ => lam) hs hv

theorem rootC0_children (hG : G.IsAcyclic) (lam : ℝ) {s : Finset V}
    (hs : ConnectedIn G s) {v : V} (hv : v ∈ s) :
    rootC0 G lam s v = ∏ w ∈ nbrsIn G s v,
      rootE G lam (compIn G (s.erase v) w) w :=
  Tail.Zw_outside_root hG (fun _ => lam) hs hv

theorem message_eq_partition_ratio (lam : ℝ) (s : Finset V) (v : V) :
    Tail.rootProb G lam s v = lam * rootC0 G lam s v / rootF G lam s := rfl

theorem vacancy_eq_partition_ratio {lam : ℝ} (hlam : 0 ≤ lam)
    {s : Finset V} {v : V} (hv : v ∈ s) :
    1 - Tail.rootProb G lam s v = rootE G lam s v / rootF G lam s :=
  Tail.one_sub_rootProb hlam hv

/-- The message is the actual normalized occupied-set weight in the printed law. -/
theorem message_eq_occupied_probability (lam : ℝ) {s : Finset V} {v : V}
    (hv : v ∈ s) :
    Tail.rootProb G lam s v =
      (∑ I ∈ (s.powerset.filter (IsIndepFinset G)).filter (fun I => v ∈ I),
        lam ^ I.card) / rootF G lam s := by
  classical
  have h := Tail.sum_mem_eq (G := G) (fun _ => lam) hv
  simp only [Finset.prod_const] at h
  rw [h]
  rfl

end Erdos993Lean.Analytic.V213.VarianceResponse

#check Erdos993Lean.Analytic.V213.VarianceResponse.rootF
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.rootF
#check Erdos993Lean.Analytic.V213.VarianceResponse.rootE
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.rootE
#check Erdos993Lean.Analytic.V213.VarianceResponse.rootC0
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.rootC0
#check Erdos993Lean.Analytic.V213.VarianceResponse.rootF_eq_independent_sum
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.rootF_eq_independent_sum
#check Erdos993Lean.Analytic.V213.VarianceResponse.rootF_eq_count_sum
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.rootF_eq_count_sum
#check Erdos993Lean.Analytic.V213.VarianceResponse.rootF_empty
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.rootF_empty
#check Erdos993Lean.Analytic.V213.VarianceResponse.rootF_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.rootF_pos
#check Erdos993Lean.Analytic.V213.VarianceResponse.rootE_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.rootE_pos
#check Erdos993Lean.Analytic.V213.VarianceResponse.rootC0_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.rootC0_pos
#check Erdos993Lean.Analytic.V213.VarianceResponse.rootF_delete
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.rootF_delete
#check Erdos993Lean.Analytic.V213.VarianceResponse.rootE_children
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.rootE_children
#check Erdos993Lean.Analytic.V213.VarianceResponse.rootC0_children
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.rootC0_children
#check Erdos993Lean.Analytic.V213.VarianceResponse.message_eq_partition_ratio
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.message_eq_partition_ratio
#check Erdos993Lean.Analytic.V213.VarianceResponse.vacancy_eq_partition_ratio
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.vacancy_eq_partition_ratio
#check Erdos993Lean.Analytic.V213.VarianceResponse.message_eq_occupied_probability
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.message_eq_occupied_probability
