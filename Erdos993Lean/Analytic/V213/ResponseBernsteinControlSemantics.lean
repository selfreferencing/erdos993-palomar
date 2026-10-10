module

public import Erdos993Lean.Analytic.V213.ResponseControlListSemantics
public import Erdos993Lean.BCFG.BernsteinPositivity

/-! The normalized Bernstein control formula for any declared degree n.
The only source-shape premise is the full outer coefficient-list bound. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates

open Erdos993Lean.BCFG
open scoped BigOperators

def bernControl (n : ℕ) (p : Bi) (j : ℕ) : Uni :=
  Uni.trim (Uni.sumRange (fun b =>
    Uni.scale ((j.choose b : ℚ)/(n.choose b : ℚ)) (p.getD b [])) (j+1))

theorem bernControl_eval (n : ℕ) (p : Bi) (j : ℕ) (lam : ℝ) :
    Uni.evalReal (bernControl n p j) lam =
      ∑ b ∈ Finset.range (j+1),
        ((j.choose b : ℝ)/(n.choose b : ℝ))*Uni.evalReal (p.getD b []) lam := by
  unfold bernControl
  rw [Uni.evalReal_trim,Uni.evalReal_sumRange]
  apply Finset.sum_congr rfl
  intro b hb
  simp only [Uni.evalReal_scale,Rat.cast_div,Rat.cast_natCast]

theorem bernstein_monomial (n b : ℕ) (hb : b ≤ n) (x : ℝ) :
    (∑ j ∈ Finset.range (n+1),
      ((j.choose b : ℝ)/(n.choose b : ℝ))*bernsteinBasis n j x) = x^b := by
  have hden : (n.choose b : ℝ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero hb
  have hn : n+1 = b+(n-b+1) := by omega
  rw [hn,Finset.sum_range_add]
  have hz : (∑ j ∈ Finset.range b,
      ((j.choose b : ℝ)/(n.choose b : ℝ))*bernsteinBasis n j x) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hj)]
    simp
  rw [hz,zero_add]
  calc
    _ = x^b*(∑ k ∈ Finset.range (n-b+1),
        x^k*(1-x)^((n-b)-k)*((n-b).choose k : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hc : (n.choose (b+k):ℝ)*((b+k).choose b:ℝ) =
          (n.choose b:ℝ)*((n-b).choose k:ℝ) := by
        have he := Nat.choose_mul (n := n) (k := b+k) (s := b) (by omega)
        exact_mod_cast (by simpa only [Nat.add_sub_cancel_left] using he)
      have hratio : ((b+k).choose b:ℝ)/(n.choose b:ℝ)*(n.choose (b+k):ℝ) =
          ((n-b).choose k:ℝ) := by
        calc
          _ = ((n.choose (b+k):ℝ)*((b+k).choose b:ℝ))/(n.choose b:ℝ) := by ring
          _ = ((n.choose b:ℝ)*((n-b).choose k:ℝ))/(n.choose b:ℝ) := by rw [hc]
          _ = _ := mul_div_cancel_left₀ _ hden
      have he : n-(b+k) = (n-b)-k := by omega
      unfold bernsteinBasis
      rw [he,pow_add]
      calc
        _ = (((b+k).choose b:ℝ)/(n.choose b:ℝ)*(n.choose (b+k):ℝ))*
            (x^b*x^k*(1-x)^((n-b)-k)) := by ring
        _ = _ := by rw [hratio]; ring
    _ = x^b*(x+(1-x))^(n-b) := by rw [add_pow]
    _ = x^b := by
      rw [show x+(1-x) = (1:ℝ) by ring,one_pow,mul_one]

theorem control_sum_reconstruction (n : ℕ) (a : ℕ → ℝ) (x : ℝ) :
    bernsteinSum n
      (fun j => ∑ b ∈ Finset.range (j+1), ((j.choose b:ℝ)/(n.choose b:ℝ))*a b) x =
      ∑ b ∈ Finset.range (n+1), a b*x^b := by
  have hext (j : ℕ) (hj : j ≤ n) :
      (∑ b ∈ Finset.range (j+1), ((j.choose b:ℝ)/(n.choose b:ℝ))*a b) =
        ∑ b ∈ Finset.range (n+1), ((j.choose b:ℝ)/(n.choose b:ℝ))*a b := by
    apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hj 1))
    intro b hb hnot
    have hjb : j < b := by
      have hnb : ¬ b < j+1 := fun h => hnot (Finset.mem_range.mpr h)
      omega
    rw [Nat.choose_eq_zero_of_lt hjb]
    simp
  unfold bernsteinSum
  calc
    _ = ∑ j ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1),
        (((j.choose b:ℝ)/(n.choose b:ℝ))*a b)*bernsteinBasis n j x := by
      apply Finset.sum_congr rfl
      intro j hj
      dsimp only
      rw [hext j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)),Finset.sum_mul]
    _ = ∑ b ∈ Finset.range (n+1), ∑ j ∈ Finset.range (n+1),
        (((j.choose b:ℝ)/(n.choose b:ℝ))*a b)*bernsteinBasis n j x := Finset.sum_comm
    _ = ∑ b ∈ Finset.range (n+1), a b*
        (∑ j ∈ Finset.range (n+1), ((j.choose b:ℝ)/(n.choose b:ℝ))*bernsteinBasis n j x) := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [bernstein_monomial n b (Nat.le_of_lt_succ (Finset.mem_range.mp hb)) x]

theorem bernControl_reconstruct (n : ℕ) (p : Bi) (hp : p.length ≤ n+1) (xi lam : ℝ) :
    Bi.evalReal p xi lam = bernsteinSum n (fun j => Uni.evalReal (bernControl n p j) lam) xi := by
  simp only [bernControl_eval]
  rw [control_sum_reconstruction,bi_eval_sum_of_length_le p n hp]

theorem bernControl_positive (n : ℕ) (p : Bi) (hp : p.length ≤ n+1)
    {xi lam : ℝ} (hx : 0 ≤ xi ∧ xi ≤ 1)
    (hc : ∀ j ≤ n, 0 < Uni.evalReal (bernControl n p j) lam) :
    0 < Bi.evalReal p xi lam := by
  rw [bernControl_reconstruct n p hp xi lam]
  exact bernsteinSum_pos n _ hc hx

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates

/-! Actual declaration and inherited-helper audits; no numerical computation. -/
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.bernControl
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.bernControl
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.bernControl_eval
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.bernControl_eval
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.bernstein_monomial
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.bernstein_monomial
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.control_sum_reconstruction
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.control_sum_reconstruction
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.bernControl_reconstruct
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.bernControl_reconstruct
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.bernControl_positive
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.bernControl_positive
#check Erdos993Lean.BCFG.bernsteinSum_pos
#print axioms Erdos993Lean.BCFG.bernsteinSum_pos
#check Nat.choose_mul
#print axioms Nat.choose_mul
#check Nat.choose_ne_zero
#print axioms Nat.choose_ne_zero
