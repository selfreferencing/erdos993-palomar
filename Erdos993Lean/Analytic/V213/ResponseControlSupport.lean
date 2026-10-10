module

public import Erdos993Lean.BCFG.StructuralLengths
public import Mathlib.Data.List.GetD
public import Mathlib.Tactic

/-! Structural support, including the trailing zeros retained by raw Uni.mul
and Uni.comp. No concrete coefficient is evaluated. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates

open Erdos993Lean.BCFG

/-- Every coefficient at or above L is zero; lower entries need not be nonzero. -/
def zeroAbove (p : Uni) (L : ℕ) : Prop := ∀ i, L ≤ i → p.getD i 0 = 0

theorem zeroAbove_of_length_le (p : Uni) (L : ℕ) (h : p.length ≤ L) :
    zeroAbove p L := by
  intro i hi
  exact List.getD_eq_default p 0 (h.trans hi)

theorem zeroAbove_mono {p : Uni} {L K : ℕ} (h : zeroAbove p L) (hLK : L ≤ K) :
    zeroAbove p K := fun i hi => h i (hLK.trans hi)

theorem zeroAbove_cons_succ (a : ℚ) {p : Uni} {L : ℕ} (h : zeroAbove p L) :
    zeroAbove (a::p) (L+1) := by
  intro i hi
  cases i with
  | zero => omega
  | succ i =>
      change p.getD i 0 = 0
      exact h i (by omega)

theorem uni_getD_add (p q : Uni) (i : ℕ) :
    (Uni.add p q).getD i 0 = p.getD i 0+q.getD i 0 := by
  induction p generalizing q i with
  | nil => simp [Uni.add]
  | cons a p ih =>
      cases q with
      | nil => simp [Uni.add]
      | cons b q =>
          cases i with
          | zero => rfl
          | succ i => exact ih q i

theorem uni_getD_scale (a : ℚ) (p : Uni) (i : ℕ) :
    (Uni.scale a p).getD i 0 = a*p.getD i 0 := by
  induction p generalizing i with
  | nil => simp [Uni.scale]
  | cons b p ih =>
      cases i with
      | zero => rfl
      | succ i => exact ih i

theorem zeroAbove_add {p q : Uni} {L : ℕ} (hp : zeroAbove p L) (hq : zeroAbove q L) :
    zeroAbove (Uni.add p q) L := by
  intro i hi
  rw [uni_getD_add,hp i hi,hq i hi,add_zero]

theorem zeroAbove_scale (a : ℚ) {p : Uni} {L : ℕ} (hp : zeroAbove p L) :
    zeroAbove (Uni.scale a p) L := by
  intro i hi
  rw [uni_getD_scale,hp i hi,mul_zero]

theorem zeroAbove_zero_singleton (L : ℕ) : zeroAbove [0] L := by
  intro i hi
  cases i <;> rfl

/-- Removing trailing zeros converts coefficient support into an actual length bound. -/
theorem trim_length_le_of_zeroAbove (p : Uni) (L : ℕ) (h : zeroAbove p L) :
    (Uni.trim p).length ≤ L := by
  induction p generalizing L with
  | nil => simp [Uni.trim]
  | cons a p ih =>
      cases L with
      | zero =>
          have ha : a=0 := h 0 (le_refl 0)
          have hp : zeroAbove p 0 := by
            intro i hi
            exact h (i+1) (by omega)
          have ht : Uni.trim p = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero (ih 0 hp))
          simp [Uni.trim,ha,ht]
      | succ L =>
          have hp : zeroAbove p L := by
            intro i hi
            exact h (i+1) (by omega)
          have ht := ih L hp
          simp only [Uni.trim]
          split_ifs <;> simp only [List.length_nil,List.length_cons] <;> omega

theorem uni_trim_length_le (p : Uni) : (Uni.trim p).length ≤ p.length :=
  trim_length_le_of_zeroAbove p p.length (zeroAbove_of_length_le p p.length (le_refl _))

/-- Raw affine multiplication preserves support with one extra degree, even
when the input is [] or carries leading zero coefficients. -/
theorem zeroAbove_mul_affine (a b : ℚ) {p : Uni} {L : ℕ} (hp : zeroAbove p L) :
    zeroAbove (Uni.mul [a,b] p) (L+1) := by
  change zeroAbove (Uni.add (Uni.scale a p)
    (0::Uni.add (Uni.scale b p) [0])) (L+1)
  exact zeroAbove_add (zeroAbove_mono (zeroAbove_scale a hp) (by omega))
    (zeroAbove_cons_succ 0 (zeroAbove_add (zeroAbove_scale b hp) (zeroAbove_zero_singleton L)))

/-- This is a support bound, not the false assertion that raw comp preserves
length. For instance comp[a][c,1] retains a trailing zero. -/
theorem zeroAbove_comp_affine (p : Uni) (a b : ℚ) :
    zeroAbove (Uni.comp p [a,b]) p.length := by
  induction p with
  | nil => exact zeroAbove_of_length_le [] 0 (le_refl _)
  | cons c p ih =>
      change zeroAbove (Uni.add [c] (Uni.mul [a,b] (Uni.comp p [a,b]))) (p.length+1)
      exact zeroAbove_add (zeroAbove_of_length_le [c] (p.length+1) (by simp))
        (zeroAbove_mul_affine a b ih)

theorem trim_comp_affine_length_le (p : Uni) (a b : ℚ) :
    (Uni.trim (Uni.comp p [a,b])).length ≤ p.length :=
  trim_length_le_of_zeroAbove _ _ (zeroAbove_comp_affine p a b)

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates

-- Declaration and axiom audits.
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.zeroAbove
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.zeroAbove
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.zeroAbove_of_length_le
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.zeroAbove_of_length_le
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.zeroAbove_mono
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.zeroAbove_mono
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.zeroAbove_cons_succ
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.zeroAbove_cons_succ
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.uni_getD_add
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.uni_getD_add
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.uni_getD_scale
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.uni_getD_scale
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.zeroAbove_add
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.zeroAbove_add
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.zeroAbove_scale
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.zeroAbove_scale
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.zeroAbove_zero_singleton
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.zeroAbove_zero_singleton
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.trim_length_le_of_zeroAbove
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.trim_length_le_of_zeroAbove
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.uni_trim_length_le
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.uni_trim_length_le
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.zeroAbove_mul_affine
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.zeroAbove_mul_affine
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.zeroAbove_comp_affine
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.zeroAbove_comp_affine
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.trim_comp_affine_length_le
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.trim_comp_affine_length_le
