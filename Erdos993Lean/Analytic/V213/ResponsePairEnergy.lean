module

public import Mathlib

/-!
Finite weighted-pair algebra for current Lemma 5.19.  pairEnergy counts each
unordered pair once as half the ordered double sum; the diagonal vanishes.
The exact equality with the printed i<j presentation is proved separately,
so no order on the forest's vertex type is needed by its mathematical claim.

-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse

open Finset

noncomputable def pairEnergy {ι : Type*} (S : Finset ι) (phi y : ι → ℝ) : ℝ :=
  (∑ i ∈ S, ∑ j ∈ S, phi i*phi j*(y i-y j)^2)/2

/-- The weighted variance is exactly the unordered-pair sum of squares. -/
theorem weighted_pair_identity {ι : Type*} (S : Finset ι) (phi y : ι → ℝ) :
    (∑ i ∈ S, phi i)*(∑ i ∈ S, phi i*y i^2) - (∑ i ∈ S, phi i*y i)^2 =
      pairEnergy S phi y := by
  have he : (∑ i ∈ S, ∑ j ∈ S, phi i*phi j*(y i-y j)^2) =
      2*((∑ i ∈ S, phi i)*(∑ i ∈ S, phi i*y i^2) - (∑ i ∈ S, phi i*y i)^2) := by
    calc
      _ = ∑ i ∈ S, ∑ j ∈ S,
          (phi i*(phi j*y j^2)+(phi i*y i^2)*phi j-2*(phi i*y i)*(phi j*y j)) := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = _ := by
        simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,
          ← Finset.mul_sum,← Finset.sum_mul]
        ring
  unfold pairEnergy
  rw [he]
  ring

/-- Pair energy is nonnegative for nonnegative log-masses and arbitrary signed responses. -/
theorem pairEnergy_nonneg {ι : Type*} (S : Finset ι) (phi y : ι → ℝ)
    (hphi : ∀ i ∈ S, 0 ≤ phi i) : 0 ≤ pairEnergy S phi y := by
  apply div_nonneg _ (by norm_num : (0 : ℝ) ≤ 2)
  exact Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj =>
    mul_nonneg (mul_nonneg (hphi i hi) (hphi j hj)) (sq_nonneg _)

/-- Equality with the literal printed sum over i<j; the choice of order is immaterial. -/
theorem pairEnergy_eq_ordered {ι : Type*} [LinearOrder ι]
    (S : Finset ι) (phi y : ι → ℝ) :
    pairEnergy S phi y = ∑ i ∈ S, ∑ j ∈ S with i < j, phi i*phi j*(y i-y j)^2 := by
  let f : ι → ι → ℝ := fun i j => phi i*phi j*(y i-y j)^2
  have hterm (i j : ι) : f i j =
      (if i < j then f i j else 0)+(if j < i then f i j else 0) := by
    rcases lt_trichotomy i j with hij | hij | hij
    · rw [if_pos hij,if_neg (not_lt.mpr hij.le),add_zero]
    · subst j
      simp only [lt_self_iff_false,if_false,f,sub_self,zero_pow (by decide : (2 : ℕ) ≠ 0),
        mul_zero,add_zero]
    · rw [if_neg (not_lt.mpr hij.le),if_pos hij,zero_add]
  have hs : (∑ i ∈ S, ∑ j ∈ S, f i j) =
      (∑ i ∈ S, ∑ j ∈ S, if i < j then f i j else 0)+
      (∑ i ∈ S, ∑ j ∈ S, if j < i then f i j else 0) := by
    calc
      _ = ∑ i ∈ S, ∑ j ∈ S,
          ((if i < j then f i j else 0)+(if j < i then f i j else 0)) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact Finset.sum_congr rfl fun j hj => hterm i j
      _ = _ := by simp only [Finset.sum_add_distrib]
  have hswap : (∑ i ∈ S, ∑ j ∈ S, if j < i then f i j else 0) =
      ∑ i ∈ S, ∑ j ∈ S, if i < j then f i j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> dsimp only [f] <;> ring
  change (∑ i ∈ S, ∑ j ∈ S, f i j)/2 = _
  rw [hs,hswap]
  simp only [Finset.sum_filter]
  change ((∑ i ∈ S, ∑ j ∈ S, if i < j then f i j else 0)+
      (∑ i ∈ S, ∑ j ∈ S, if i < j then f i j else 0))/2 =
    ∑ i ∈ S, ∑ j ∈ S, if i < j then f i j else 0
  ring

end Erdos993Lean.Analytic.V213.VarianceResponse

#check Erdos993Lean.Analytic.V213.VarianceResponse.pairEnergy
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.pairEnergy
#check Erdos993Lean.Analytic.V213.VarianceResponse.weighted_pair_identity
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.weighted_pair_identity
#check Erdos993Lean.Analytic.V213.VarianceResponse.pairEnergy_nonneg
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.pairEnergy_nonneg
#check Erdos993Lean.Analytic.V213.VarianceResponse.pairEnergy_eq_ordered
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.pairEnergy_eq_ordered
