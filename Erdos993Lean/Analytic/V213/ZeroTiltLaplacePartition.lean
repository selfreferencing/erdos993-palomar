module

public import Erdos993Lean.Analytic.Tail.Weight

/-!
The current paper's T(X) is the partition ratio after
deleting the selected vertices, not a newly defined abstract expectation.
The zero-weight deletion identity below identifies it with generic phiF at z=0.
The last theorem reuses the actual simultaneous partition-product induction.
No certified rate, cap or old profile is imported or applied.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem partition_congr_on (u v : V → ℝ) (s : Finset V)
    (huv : ∀ x ∈ s, u x = v x) : Tail.Zw G u s = Tail.Zw G v s := by
  unfold Tail.Zw
  apply Finset.sum_congr rfl
  intro I hI
  have hIs : I ⊆ s := Finset.mem_powerset.mp (Finset.mem_filter.mp hI).1
  apply Finset.prod_congr rfl
  intro x hx
  exact huv x (hIs hx)

theorem partition_erase_zero (wt : V → ℝ) (s : Finset V) (v : V)
    (hv : wt v = 0) : Tail.Zw G wt s = Tail.Zw G wt (s.erase v) := by
  by_cases hvs : v ∈ s
  · rw [Tail.Zw_erase_add wt hvs, hv, zero_mul, add_zero]
  · rw [Finset.erase_eq_of_notMem hvs]

theorem partition_delete_zero (wt : V → ℝ) (B s : Finset V)
    (hB : ∀ v ∈ B, wt v = 0) : Tail.Zw G wt s = Tail.Zw G wt (s \ B) := by
  induction B using Finset.induction_on generalizing s with
  | empty => simp
  | @insert v B hvB ih =>
    have hv : wt v = 0 := hB v (Finset.mem_insert_self _ _)
    have hB' : ∀ x ∈ B, wt x = 0 := fun x hx => hB x (Finset.mem_insert_of_mem hx)
    calc
      Tail.Zw G wt s = Tail.Zw G wt (s.erase v) := partition_erase_zero wt s v hv
      _ = Tail.Zw G wt ((s.erase v) \ B) := ih (s.erase v) hB'
      _ = Tail.Zw G wt (s \ insert v B) := by
        congr 1
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
        tauto

theorem zero_weight_partition (B s : Finset V) (lam : ℝ) :
    Tail.Zw G (Tail.lapW B lam 0) s = Tail.Zw G (fun _ => lam) (s \ B) := by
  rw [partition_delete_zero (Tail.lapW B lam 0) B s
    (fun v hv => by simp [Tail.lapW, hv])]
  apply partition_congr_on
  intro v hv
  have hvB := (Finset.mem_sdiff.mp hv).2
  simp [Tail.lapW, hvB]

noncomputable def partitionRatio (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Finset V) (lam : ℝ) (X : Finset V) : ℝ :=
  Tail.Zw G (fun _ => lam) (X \ B) / Tail.Zw G (fun _ => lam) X

theorem partitionRatio_eq_phiF (B X : Finset V) (lam : ℝ) :
    partitionRatio G B lam X = Tail.phiF G B lam 0 X := by
  unfold partitionRatio Tail.phiF
  rw [zero_weight_partition]

@[simp] theorem partitionRatio_empty (B : Finset V) (lam : ℝ) :
    partitionRatio G B lam ∅ = 1 := by
  rw [partitionRatio_eq_phiF]
  exact Tail.phiF_empty

theorem partitionRatio_singleton_in (B : Finset V) (lam : ℝ) {v : V} (hv : v ∈ B) :
    partitionRatio G B lam {v} = 1/(1+lam) := by
  rw [partitionRatio_eq_phiF, Tail.phiF_singleton]
  simp [Tail.lapW, hv]

theorem partitionRatio_singleton_out (B : Finset V) {lam : ℝ} (hlam : 0 ≤ lam)
    {v : V} (hv : v ∉ B) : partitionRatio G B lam {v} = 1 := by
  rw [partitionRatio_eq_phiF, Tail.phiF_singleton]
  have hd : 1+lam ≠ 0 := by positivity
  simp [Tail.lapW, hv, hd]

theorem partitionRatio_component (B s : Finset V) (lam : ℝ) (x : V) :
    partitionRatio G B lam s =
      partitionRatio G B lam (compIn G s x)*
      partitionRatio G B lam (s \ compIn G s x) := by
  simp only [partitionRatio_eq_phiF]
  exact Tail.phiF_comp_split s x

/-- This is the generic simultaneous root-deletion product proof specialized at zero. -/
theorem partitionRatio_le_product (hG : G.IsAcyclic) {B : Finset V}
    (hB : IsIndepFinset G B) {lam : ℝ} (hlam : 0 ≤ lam)
    {s : Finset V} (hs : ConnectedIn G s) {r : V} (hr : r ∈ s) :
    partitionRatio G B lam s ≤ Tail.toy G B lam 0 s r := by
  rw [partitionRatio_eq_phiF]
  exact Tail.phiF_le_toy hG hB hlam le_rfl zero_le_one hs hr

end Erdos993Lean.Analytic.V213.ZeroTiltLaplace

-- Audit commands.
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.partition_congr_on
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.partition_congr_on
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.partition_erase_zero
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.partition_erase_zero
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.partition_delete_zero
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.partition_delete_zero
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.zero_weight_partition
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.zero_weight_partition
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.partitionRatio_eq_phiF
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.partitionRatio_eq_phiF
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.partitionRatio_empty
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.partitionRatio_empty
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.partitionRatio_singleton_in
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.partitionRatio_singleton_in
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.partitionRatio_singleton_out
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.partitionRatio_singleton_out
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.partitionRatio_component
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.partitionRatio_component
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.partitionRatio_le_product
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.partitionRatio_le_product
