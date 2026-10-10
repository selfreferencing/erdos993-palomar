module

public import Erdos993Lean.BCFG.ExactPolynomial
public import Erdos993Lean.BCFG.NormMinorant

/-!
A minimal executable bivariate coefficient-list layer for the BCFG packet.
Only addition, tensor products and finite sums are needed. Exact list equality
is interpreted in the reals; source dimensions and input custody are separate.

-/

@[expose] public section

set_option autoImplicit false

namespace Erdos993Lean.BCFG

open scoped BigOperators

/-- Ascending outer-variable coefficients; each row is an ascending Uni. -/
abbrev Bi := List Uni

namespace Bi

noncomputable def evalReal : Bi → ℝ → ℝ → ℝ
  | [], _, _ => 0
  | p :: ps, s, z => Uni.evalReal p z + s * evalReal ps s z

def add : Bi → Bi → Bi
  | [], q => q
  | p, [] => p
  | p :: ps, q :: qs => Uni.add p q :: add ps qs

/-- The outer factor is u(s); the inner factor is v(z). -/
def tensor (u v : Uni) : Bi := u.map (fun c => Uni.scale c v)

def sumRange (f : Nat → Bi) : Nat → Bi
  | 0 => []
  | n+1 => add (sumRange f n) (f n)

/-- Trim each inner row, then remove trailing zero rows. -/
def trim : Bi → Bi
  | [] => []
  | p :: ps =>
      let p' := Uni.trim p
      let t := trim ps
      if p' = [] ∧ t = [] then [] else p' :: t

@[simp] theorem evalReal_nil (s z : ℝ) : evalReal [] s z = 0 := rfl

@[simp] theorem evalReal_cons (p : Uni) (ps : Bi) (s z : ℝ) :
    evalReal (p :: ps) s z = Uni.evalReal p z + s * evalReal ps s z := rfl

@[simp] theorem evalReal_add (p q : Bi) (s z : ℝ) :
    evalReal (add p q) s z = evalReal p s z + evalReal q s z := by
  induction p generalizing q with
  | nil => simp [add]
  | cons p ps ih =>
      cases q with
      | nil => simp [add]
      | cons q qs =>
          simp only [add, evalReal_cons, Uni.evalReal_add, ih]
          ring

@[simp] theorem evalReal_tensor (u v : Uni) (s z : ℝ) :
    evalReal (tensor u v) s z = Uni.evalReal u s * Uni.evalReal v z := by
  induction u with
  | nil => simp [tensor]
  | cons c u ih =>
      change Uni.evalReal (Uni.scale c v) z + s * evalReal (tensor u v) s z =
        ((c : ℝ) + s * Uni.evalReal u s) * Uni.evalReal v z
      rw [Uni.evalReal_scale, ih]
      ring

@[simp] theorem evalReal_sumRange (f : Nat → Bi) (n : Nat) (s z : ℝ) :
    evalReal (sumRange f n) s z = ∑ i ∈ Finset.range n, evalReal (f i) s z := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih => simp [sumRange, ih, Finset.sum_range_succ]

@[simp] theorem evalReal_trim (p : Bi) (s z : ℝ) :
    evalReal (trim p) s z = evalReal p s z := by
  induction p with
  | nil => rfl
  | cons p ps ih =>
      simp only [trim]
      split_ifs with h
      · rcases h with ⟨hp, ht⟩
        have hpr : Uni.evalReal p z = 0 := by
          rw [← Uni.evalReal_trim p z, hp]
          rfl
        have htr : evalReal ps s z = 0 := by
          rw [← ih, ht]
          rfl
        simp [evalReal, hpr, htr]
      · simp only [evalReal_cons, Uni.evalReal_trim, ih]

theorem evalReal_eq_of_trim_eq {p q : Bi} (h : trim p = trim q) (s z : ℝ) :
    evalReal p s z = evalReal q s z := by
  rw [← evalReal_trim p s z, h, evalReal_trim]

def checkEq (p q : Bi) : Bool := decide (trim p = trim q)

theorem checkEq_sound {p q : Bi} (h : checkEq p q = true) (s z : ℝ) :
    evalReal p s z = evalReal q s z := by
  exact evalReal_eq_of_trim_eq (of_decide_eq_true h) s z

/-- Bounded source evaluation, explicitly retaining only outer powers 0,...,N.
The finite input layer must separately check its declared shape and custody. -/
noncomputable def sourceEval (N : Nat) (p : Bi) (lambda y : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (N+1), Uni.evalReal (p.getD i []) y * lambda^i

/-- Homogeneous q-normalization followed by the two affine chart substitutions.
All arithmetic here is executable exact rational-list arithmetic. -/
def normalized (N : Nat) (p : Bi) (qc rq a b : Rat) : Bi :=
  sumRange (fun i =>
    tensor
      (Uni.mul (Uni.pow [qc, rq] i) (Uni.pow [1-qc, -rq] (N-i)))
      (Uni.comp (p.getD i []) [a, b])) (N+1)

/-- Reconstructs the supplied norm coefficients in monomial/Bernstein form. -/
def fromNorm (N M : Nat) (A : Bi) : Bi :=
  sumRange (fun i =>
    tensor (Uni.monomial 1 i) (Uni.bernVector M (A.getD i []))) (N+1)

private theorem uni_eval_affine (a b : Rat) (x : ℝ) :
    Uni.evalReal [a, b] x = (a : ℝ) + (b : ℝ) * x := by
  simp [Uni.evalReal, mul_comm]

private theorem uni_eval_complement (qc rq : Rat) (s : ℝ) :
    Uni.evalReal [1-qc, -rq] s = 1-((qc : ℝ)+(rq : ℝ)*s) := by
  rw [uni_eval_affine]
  simp only [Rat.cast_sub, Rat.cast_one, Rat.cast_neg]
  ring

/-- Explicit value of the executable homogeneous normalization. -/
theorem evalReal_normalized (N : Nat) (p : Bi) (qc rq a b : Rat) (s z : ℝ) :
    evalReal (normalized N p qc rq a b) s z =
      ∑ i ∈ Finset.range (N+1),
        (((qc : ℝ)+(rq : ℝ)*s)^i *
          (1-((qc : ℝ)+(rq : ℝ)*s))^(N-i)) *
            Uni.evalReal (p.getD i []) ((a : ℝ)+(b : ℝ)*z) := by
  unfold normalized
  rw [evalReal_sumRange]
  apply Finset.sum_congr rfl
  intro i hi
  rw [evalReal_tensor, Uni.evalReal_mul, Uni.evalReal_pow, Uni.evalReal_pow,
    Uni.evalReal_comp, uni_eval_affine, uni_eval_complement, uni_eval_affine]

/-- The truncated natural difference N-i is used only under i≤N. -/
theorem homogenized_power (N i : Nat) (q : ℝ) (hi : i ≤ N) (hq : q ≠ 1) :
    (1-q)^N * (q/(1-q))^i = q^i * (1-q)^(N-i) := by
  have hp : (1-q)^i ≠ 0 := pow_ne_zero i (sub_ne_zero.mpr (Ne.symm hq))
  calc
    (1-q)^N * (q/(1-q))^i =
        ((1-q)^(N-i) * (1-q)^i) * (q^i/(1-q)^i) := by
      rw [← pow_add, Nat.sub_add_cancel hi, div_pow]
    _ = q^i * (1-q)^(N-i) := by
      field_simp [hp] <;> ring

/-- Generic semantic normalization; no signs are needed, only q≠1. -/
theorem normalized_sound (N : Nat) (p : Bi) (qc rq a b : Rat) (s z q : ℝ)
    (hqdef : q = (qc : ℝ)+(rq : ℝ)*s) (hq : q ≠ 1) :
    evalReal (normalized N p qc rq a b) s z =
      (1-q)^N * sourceEval N p (q/(1-q)) ((a : ℝ)+(b : ℝ)*z) := by
  rw [evalReal_normalized]
  simp only [← hqdef]
  unfold sourceEval
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hpower := homogenized_power N i q
    (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) hq
  calc
    (q^i * (1-q)^(N-i)) * Uni.evalReal (p.getD i []) ((a : ℝ)+(b : ℝ)*z) =
        Uni.evalReal (p.getD i []) ((a : ℝ)+(b : ℝ)*z) *
          ((1-q)^N * (q/(1-q))^i) := by rw [hpower]; ring
    _ = (1-q)^N * (Uni.evalReal (p.getD i []) ((a : ℝ)+(b : ℝ)*z) *
          (q/(1-q))^i) := by ring

/-- Interpretation of every supplied norm row; default zero entries are explicit. -/
theorem fromNorm_sound (N M : Nat) (A : Bi) (s z : ℝ) :
    evalReal (fromNorm N M A) s z =
      normEval N M (fun i j => ((A.getD i []).getD j 0 : ℝ)) s z := by
  unfold fromNorm
  rw [evalReal_sumRange, normEval_eq_double_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [evalReal_tensor, Uni.evalReal_monomial, Uni.evalReal_bernVector]
  simp only [Rat.cast_one, one_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  unfold bernsteinBasis
  ring

/-- The finite equality check supplies exactly the expansion premise consumed
by the norm-minorant theorem. This is a soundness implication, not acceptance
of any packet instance. -/
theorem checked_expansion (N M : Nat) (p A : Bi) (qc rq a b : Rat)
    (hcheck : checkEq (normalized N p qc rq a b) (fromNorm N M A) = true)
    (s z q : ℝ) (hqdef : q = (qc : ℝ)+(rq : ℝ)*s) (hq : q ≠ 1) :
    (1-q)^N * sourceEval N p (q/(1-q)) ((a : ℝ)+(b : ℝ)*z) =
      normEval N M (fun i j => ((A.getD i []).getD j 0 : ℝ)) s z := by
  calc
    (1-q)^N * sourceEval N p (q/(1-q)) ((a : ℝ)+(b : ℝ)*z) =
        evalReal (normalized N p qc rq a b) s z :=
      (normalized_sound N p qc rq a b s z q hqdef hq).symm
    _ = evalReal (fromNorm N M A) s z := checkEq_sound hcheck s z
    _ = normEval N M (fun i j => ((A.getD i []).getD j 0 : ℝ)) s z :=
      fromNorm_sound N M A s z

end Bi

end Erdos993Lean.BCFG
