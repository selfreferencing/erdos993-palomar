module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Jensen

/-! The coefficient-norm lower bound in current Lemma 5.29 (T8a Lemma6.4).
N is a declared upper degree and coefficients may be zero-padded. No table,
coefficient array, polynomial expansion or finite sign result is assumed. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightShape

open Set
open scoped BigOperators

noncomputable def centeredValue (N : ℕ) (e : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (N+1), e i*t^i
noncomputable def tailNorm (N : ℕ) (e : ℕ → ℝ) (r : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (N+1), if 3 ≤ i then |e i| *r^(i-2) else 0
noncomputable def lowerK (N : ℕ) (e : ℕ → ℝ) (r : ℝ) : ℝ := e 2-tailNorm N e r
noncomputable def lowerQ (N : ℕ) (e : ℕ → ℝ) (r t : ℝ) : ℝ :=
  e 0+e 1*t+lowerK N e r*t^2

theorem centered_split_low {N : ℕ} (hN : 2≤N) (e : ℕ → ℝ) (t : ℝ) :
    centeredValue N e t=e 0+e 1*t+e 2*t^2+
      ∑ i ∈ Finset.range (N+1), if 3 ≤ i then e i*t^i else 0 := by
  induction N, hN using Nat.le_induction with
  | base => norm_num [centeredValue,Finset.sum_range_succ]
  | succ n hn ih =>
      unfold centeredValue at ih ⊢
      rw [Finset.sum_range_succ (f:=fun i=>e i*t^i) (n:=n+1),
        Finset.sum_range_succ (f:=fun i=>if 3 ≤ i then e i*t^i else 0) (n:=n+1)]
      simp only [show 3≤n+1 by omega,if_true]
      rw [ih]
      ring

theorem monomial_tail_lower {i : ℕ} (hi : 3 ≤ i) {r t : ℝ} (ht : |t|≤r) (a : ℝ) :
    -(|a| *r^(i-2))*t^2 ≤ a*t^i := by
  have hp := pow_le_pow_left₀ (abs_nonneg t) ht (i-2)
  have habs : |a*t^(i-2)|≤|a| *r^(i-2) := by
    rw [abs_mul,abs_pow]
    exact mul_le_mul_of_nonneg_left hp (abs_nonneg a)
  have hlow := (abs_le.mp habs).1
  have hm := mul_le_mul_of_nonneg_right hlow (sq_nonneg t)
  have he : t^i=t^(i-2)*t^2 := by
    rw [←pow_add]
    congr 1
    omega
  rw [he]
  nlinarith

theorem centered_lower {N : ℕ} (hN : 2≤N) (e : ℕ → ℝ) {r t : ℝ}
    (ht : |t|≤r) : lowerQ N e r t≤centeredValue N e t := by
  have hs : (∑ i ∈ Finset.range (N+1),
      -(if 3 ≤ i then |e i| *r^(i-2) else 0)*t^2) ≤
      ∑ i ∈ Finset.range (N+1), if 3 ≤ i then e i*t^i else 0 := by
    apply Finset.sum_le_sum
    intro i hi
    by_cases h3 : 3 ≤ i
    · simpa only [h3,if_pos] using monomial_tail_lower h3 ht (e i)
    · simp only [h3,if_false,neg_zero,zero_mul,le_refl]
  have he : (∑ i ∈ Finset.range (N+1),
      -(if 3 ≤ i then |e i| *r^(i-2) else 0)*t^2) = -tailNorm N e r*t^2 := by
    rw [←Finset.sum_mul,Finset.sum_neg_distrib]
    rfl
  rw [he] at hs
  rw [centered_split_low hN]
  unfold lowerQ lowerK
  nlinarith

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightShape

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightShape.centeredValue
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightShape.centeredValue
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightShape.tailNorm
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightShape.tailNorm
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightShape.lowerK
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightShape.lowerK
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightShape.lowerQ
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightShape.lowerQ
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightShape.centered_split_low
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightShape.centered_split_low
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightShape.monomial_tail_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightShape.monomial_tail_lower
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightShape.centered_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightShape.centered_lower
