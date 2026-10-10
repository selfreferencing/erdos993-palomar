module

public import Erdos993Lean.BCFG.UniWholePolynomial
public import Mathlib.Data.List.GetD
public import Mathlib.Tactic

/-! Full ascending-list semantics with an explicit declared degree bound.
No coefficient outside the declared range is silently discarded. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates

open Erdos993Lean.BCFG
open scoped BigOperators

theorem uni_eval_sum_of_length_le (p : Uni) (N : ℕ) (hp : p.length ≤ N+1) (x : ℝ) :
    Uni.evalReal p x = ∑ i ∈ Finset.range (N+1), (p.getD i 0 : ℝ)*x^i := by
  rw [Uni.evalReal_eq_sum]
  apply Finset.sum_subset (Finset.range_mono hp)
  intro i hi hnot
  have hn : p.length ≤ i := Nat.le_of_not_gt (fun h => hnot (Finset.mem_range.mpr h))
  rw [List.getD_eq_default p 0 hn]
  simp

theorem bi_eval_sum_of_length_le (p : Bi) (n : ℕ) (hp : p.length ≤ n+1) (x z : ℝ) :
    Bi.evalReal p x z =
      ∑ i ∈ Finset.range (n+1), Uni.evalReal (p.getD i []) z*x^i := by
  rw [Bi.evalReal_eq_sum]
  apply Finset.sum_subset (Finset.range_mono hp)
  intro i hi hnot
  have hn : p.length ≤ i := Nat.le_of_not_gt (fun h => hnot (Finset.mem_range.mpr h))
  rw [List.getD_eq_default p [] hn]
  simp

def homogenizeUni (N : ℕ) (p : Uni) : Uni :=
  Uni.trim (Uni.sumRange (fun a => Uni.scale (p.getD a 0)
    (Uni.mul (Uni.pow [0,1] a) (Uni.pow [1,-1] (N-a)))) (N+1))

theorem homogenizeUni_eval (N : ℕ) (p : Uni) (q : ℝ) :
    Uni.evalReal (homogenizeUni N p) q =
      ∑ a ∈ Finset.range (N+1), (p.getD a 0 : ℝ)*q^a*(1-q)^(N-a) := by
  unfold homogenizeUni
  rw [Uni.evalReal_trim,Uni.evalReal_sumRange]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [Uni.evalReal_scale,Uni.evalReal_mul,Uni.evalReal_pow,
    Uni.evalReal_one_sub,Uni.evalReal_cons,Uni.evalReal_nil,Rat.cast_zero,Rat.cast_one,
    mul_zero,add_zero,mul_one,zero_add]
  ring

theorem homogenizeUni_sound (N : ℕ) (p : Uni) (hp : p.length ≤ N+1)
    (q : ℝ) (hq : q ≠ 1) :
    Uni.evalReal (homogenizeUni N p) q =
      (1-q)^N*Uni.evalReal p (q/(1-q)) := by
  rw [homogenizeUni_eval,uni_eval_sum_of_length_le p N hp,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have he := Bi.homogenized_power N a q
    (Nat.le_of_lt_succ (Finset.mem_range.mp ha)) hq
  calc
    (p.getD a 0 : ℝ)*q^a*(1-q)^(N-a) =
        (p.getD a 0 : ℝ)*(q^a*(1-q)^(N-a)) := by ring
    _ = (p.getD a 0 : ℝ)*((1-q)^N*(q/(1-q))^a) := by rw [he]
    _ = _ := by ring

theorem affine_shift_eval (p : Uni) (c : ℚ) (t : ℝ) :
    Uni.evalReal (Uni.trim (Uni.comp p [c,1])) t = Uni.evalReal p ((c:ℝ)+t) := by
  rw [Uni.evalReal_trim,Uni.evalReal_comp]
  simp only [Uni.evalReal_cons,Uni.evalReal_nil,Rat.cast_one,mul_zero,add_zero,mul_one]

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates

/-! Actual declaration and inherited-helper audits; no numerical computation. -/
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.uni_eval_sum_of_length_le
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.uni_eval_sum_of_length_le
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.bi_eval_sum_of_length_le
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.bi_eval_sum_of_length_le
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.homogenizeUni
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.homogenizeUni
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.homogenizeUni_eval
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.homogenizeUni_eval
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.homogenizeUni_sound
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.homogenizeUni_sound
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.affine_shift_eval
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.affine_shift_eval
#check Erdos993Lean.BCFG.Uni.evalReal_eq_sum
#print axioms Erdos993Lean.BCFG.Uni.evalReal_eq_sum
#check Erdos993Lean.BCFG.Bi.evalReal_eq_sum
#print axioms Erdos993Lean.BCFG.Bi.evalReal_eq_sum
#check Erdos993Lean.BCFG.Uni.evalReal_trim
#print axioms Erdos993Lean.BCFG.Uni.evalReal_trim
#check Erdos993Lean.BCFG.Uni.evalReal_sumRange
#print axioms Erdos993Lean.BCFG.Uni.evalReal_sumRange
#check Erdos993Lean.BCFG.Uni.evalReal_scale
#print axioms Erdos993Lean.BCFG.Uni.evalReal_scale
#check Erdos993Lean.BCFG.Uni.evalReal_mul
#print axioms Erdos993Lean.BCFG.Uni.evalReal_mul
#check Erdos993Lean.BCFG.Uni.evalReal_pow
#print axioms Erdos993Lean.BCFG.Uni.evalReal_pow
#check Erdos993Lean.BCFG.Uni.evalReal_comp
#print axioms Erdos993Lean.BCFG.Uni.evalReal_comp
#check Erdos993Lean.BCFG.Uni.evalReal_one_sub
#print axioms Erdos993Lean.BCFG.Uni.evalReal_one_sub
#check Erdos993Lean.BCFG.Uni.evalReal_cons
#print axioms Erdos993Lean.BCFG.Uni.evalReal_cons
#check Erdos993Lean.BCFG.Uni.evalReal_nil
#print axioms Erdos993Lean.BCFG.Uni.evalReal_nil
#check Erdos993Lean.BCFG.Bi.homogenized_power
#print axioms Erdos993Lean.BCFG.Bi.homogenized_power
