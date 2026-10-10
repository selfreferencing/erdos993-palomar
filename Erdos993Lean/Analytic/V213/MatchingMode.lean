module

public import Erdos993Lean.Analytic.V213.StrongMode
public import Erdos993Lean.Analytic.V213.ModeBound

/-!
The exact coefficient and first-mode consequences of Lemma2.1 of version 2.13 of the manuscript.
All coefficient products include the empty product. The threshold is written
without truncated subtraction: 4a+3b≤6s+2 is the printed 6s≥4a+3b-2.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Finset Polynomial

noncomputable def twoWeightPoly (a b : ℕ) : ℕ[X] :=
  (1 + 2 * X) ^ a * (1 + X) ^ b

noncomputable def trialProb (a b : ℕ) : Fin a ⊕ Fin b → ℝ :=
  Sum.elim (fun _ => 2 / 3) (fun _ => 1 / 2)

noncomputable def realTwoWeightPoly (a b : ℕ) : ℝ[X] :=
  (1 + 2 * X) ^ a * (1 + X) ^ b

theorem trialProb_in_unit (a b : ℕ) (i : Fin a ⊕ Fin b) :
    0 < trialProb a b i ∧ trialProb a b i < 1 := by
  cases i <;> norm_num [trialProb]

theorem trialProb_cap (a b : ℕ) (i : Fin a ⊕ Fin b) :
    trialProb a b i ≤ 2 / 3 := by
  cases i <;> norm_num [trialProb]

theorem trialProb_sum (a b : ℕ) :
    (∑ i : Fin a ⊕ Fin b, trialProb a b i) = (4 * (a : ℝ) + 3 * b) / 6 := by
  rw [Fintype.sum_sum_type]
  simp only [trialProb, Sum.elim_inl, Sum.elim_inr, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem bernoulli_twoWeight_normalization (a b : ℕ) :
    Bernoulli.bernPoly univ (trialProb a b) =
      C ((1 / 3 : ℝ) ^ a * (1 / 2 : ℝ) ^ b) * realTwoWeightPoly a b := by
  unfold Bernoulli.bernPoly
  rw [Fintype.prod_sum_type]
  have h2 : Bernoulli.bernFactor (2 / 3) =
      C (1 / 3 : ℝ) * (1 + 2 * X) := by
    have hc2 : C (2 / 3 : ℝ) = C (1 / 3 : ℝ) * (2 : ℝ[X]) := by
      rw [show (2 : ℝ[X]) = C (2 : ℝ) from rfl, ← Polynomial.C_mul]
      norm_num
    simp only [Bernoulli.bernFactor]
    norm_num
    rw [hc2]
    ring
  have h1 : Bernoulli.bernFactor (1 / 2) =
      C (1 / 2 : ℝ) * (1 + X) := by
    simp only [Bernoulli.bernFactor]
    norm_num
    ring
  simp only [trialProb, Sum.elim_inl, Sum.elim_inr, h2, h1, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, mul_pow]
  simp only [← Polynomial.C_pow, Polynomial.C_mul, realTwoWeightPoly]
  ring

theorem realTwoWeight_coeff (a b s : ℕ) :
    (realTwoWeightPoly a b).coeff s = ((twoWeightPoly a b).coeff s : ℝ) := by
  have hm : (twoWeightPoly a b).map (Nat.castRingHom ℝ) = realTwoWeightPoly a b := by
    simp [twoWeightPoly, realTwoWeightPoly]
  rw [← hm, Polynomial.coeff_map]
  rfl

/-- The Bernoulli coefficient is the positive normalization of the printed count. -/
theorem bernoulli_twoWeight_coeff (a b s : ℕ) :
    (Bernoulli.bernPoly univ (trialProb a b)).coeff s =
      ((1 / 3 : ℝ) ^ a * (1 / 2 : ℝ) ^ b) * ((twoWeightPoly a b).coeff s : ℝ) := by
  rw [bernoulli_twoWeight_normalization, Polynomial.coeff_C_mul, realTwoWeight_coeff]

/-- Log-concavity and exact positive support follow from the new printed
Bernoulli convolution proof, including a=b=0. -/
theorem twoWeight_logConcave_positive (a b : ℕ) :
    LogConcave (fun s => (twoWeightPoly a b).coeff s) ∧
      Ceiling.PosUpTo (fun s => (twoWeightPoly a b).coeff s) (a + b) := by
  let c : ℝ := (1 / 3 : ℝ) ^ a * (1 / 2 : ℝ) ^ b
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨hs, hlc⟩ := Bernoulli.bernPoly_support_logConcave
    (univ : Finset (Fin a ⊕ Fin b)) (trialProb a b)
    (fun i _ => trialProb_in_unit a b i)
  have hsupport : Bernoulli.PositiveSupport
      (Bernoulli.coeffZ (Bernoulli.bernPoly univ (trialProb a b))) (a + b) := by
    simpa only [Finset.card_univ, Fintype.card_sum, Fintype.card_fin] using hs
  have hcoef (s : ℕ) :
      Bernoulli.coeffZ (Bernoulli.bernPoly univ (trialProb a b)) (s : ℤ) =
        c * ((twoWeightPoly a b).coeff s : ℝ) := by
    rw [Bernoulli.coeffZ_nat, bernoulli_twoWeight_coeff]
  constructor
  · intro k
    have h := hlc ((k + 1 : ℕ) : ℤ)
    have hm : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by omega
    have hp : ((k + 1 : ℕ) : ℤ) + 1 = ((k + 2 : ℕ) : ℤ) := by omega
    rw [hm, hp] at h
    simp only [hcoef] at h
    have hscaled : (c * c) *
        (((twoWeightPoly a b).coeff k : ℝ) * ((twoWeightPoly a b).coeff (k + 2) : ℝ)) ≤
        (c * c) * (((twoWeightPoly a b).coeff (k + 1) : ℝ) *
          ((twoWeightPoly a b).coeff (k + 1) : ℝ)) := by
      nlinarith only [h]
    exact_mod_cast (mul_le_mul_iff_of_pos_left (mul_pos hc hc)).mp hscaled
  · constructor
    · intro k hk
      have h := hsupport.pos (k : ℤ) (by omega) (by exact_mod_cast hk)
      rw [hcoef] at h
      exact_mod_cast (mul_pos_iff_of_pos_left hc).mp h
    · intro k hk
      have h := hsupport.zero (k : ℤ) (Or.inr (by exact_mod_cast hk))
      rw [hcoef] at h
      have hz : ((twoWeightPoly a b).coeff k : ℝ) = 0 :=
        (mul_eq_zero.mp h).resolve_left hc.ne'
      exact_mod_cast hz

/-- Both equality and all finite-support endpoint cases are retained. -/
theorem twoWeight_coeff_succ_le (a b s : ℕ)
    (hthreshold : 4 * a + 3 * b ≤ 6 * s + 2) :
    (twoWeightPoly a b).coeff (s + 1) ≤ (twoWeightPoly a b).coeff s := by
  have hm : (∑ i : Fin a ⊕ Fin b, trialProb a b i) + (2 / 3 : ℝ) ≤ (s : ℝ) + 1 := by
    rw [trialProb_sum]
    have ht : 4 * (a : ℝ) + 3 * b ≤ 6 * s + 2 := by exact_mod_cast hthreshold
    linarith
  have h := Bernoulli.bernPoly_succ_le_of_mean_add_cap_le
    (s := (univ : Finset (Fin a ⊕ Fin b))) (p := trialProb a b)
    (c := (2 / 3 : ℝ)) (k := s)
    (fun i _ => trialProb_in_unit a b i) (by constructor <;> norm_num)
    (fun i _ => trialProb_cap a b i) hm
  rw [bernoulli_twoWeight_normalization, Polynomial.coeff_C_mul,
    Polynomial.coeff_C_mul, realTwoWeight_coeff, realTwoWeight_coeff] at h
  have hc : 0 < (1 / 3 : ℝ) ^ a * (1 / 2 : ℝ) ^ b := by positivity
  exact_mod_cast (mul_le_mul_iff_of_pos_left hc).mp h

theorem bRow_eq_twoWeight (n ν : ℕ) : bRow n ν = fun s => (twoWeightPoly ν (n - 2 * ν)).coeff s :=
  rfl

/-- The stronger +3 bound, with the matching-number hypotheses discharged. -/
theorem forest_firstMode_sharp (F : FiniteForest) :
    hB F ≤ (3 * F.n - 2 * matchingNumber F.graph + 3) / 6 := by
  have h2 := Join.two_mul_matchingNumber_le F.graph
  have hrow := twoWeight_logConcave_positive (matchingNumber F.graph)
    (F.n - 2 * matchingNumber F.graph)
  change firstMode (fun s => (twoWeightPoly (matchingNumber F.graph)
    (F.n - 2 * matchingNumber F.graph)).coeff s) ≤
      (3 * F.n - 2 * matchingNumber F.graph + 3) / 6
  apply firstMode_le_at_descent hrow.1 hrow.2
  exact twoWeight_coeff_succ_le (matchingNumber F.graph)
    (F.n - 2 * matchingNumber F.graph)
    ((3 * F.n - 2 * matchingNumber F.graph + 3) / 6) (by omega)

/-- The paper's second mode inequality in integer arithmetic. -/
theorem forest_firstMode_sharp_le_ceil_nat (F : FiniteForest) :
    hB F ≤ (3 * F.n - 2 * matchingNumber F.graph + 5) / 6 := by
  exact (forest_firstMode_sharp F).trans (Nat.div_le_div_right (by omega))

/-- Integer floor of a nonnegative sixth, with no rounding approximation. -/
theorem floor_nat_sixth (y : ℕ) :
    Int.floor ((y : ℝ) / 6) = ((y / 6 : ℕ) : ℤ) := by
  apply Int.floor_eq_iff.mpr
  constructor
  · have h : y / 6 * 6 ≤ y := by omega
    have hr : ((y / 6 : ℕ) : ℝ) * 6 ≤ (y : ℝ) := by exact_mod_cast h
    simp only [Int.cast_natCast]
    linarith
  · have h : y < (y / 6 + 1) * 6 := by omega
    have hr : (y : ℝ) < (((y / 6 : ℕ) : ℝ) + 1) * 6 := by exact_mod_cast h
    simp only [Int.cast_natCast]
    linarith

/-- Integer ceiling of a nonnegative sixth. -/
theorem ceil_nat_sixth (y : ℕ) :
    Int.ceil ((y : ℝ) / 6) = (((y + 5) / 6 : ℕ) : ℤ) := by
  apply Int.ceil_eq_iff.mpr
  constructor
  · have h : (((y + 5) / 6 : ℕ) : ℤ) * 6 < (y : ℤ) + 6 := by omega
    have hr : (((y + 5) / 6 : ℕ) : ℝ) * 6 < (y : ℝ) + 6 := by exact_mod_cast h
    simp only [Int.cast_natCast]
    linarith
  · have h : y ≤ (y + 5) / 6 * 6 := by omega
    have hr : (y : ℝ) ≤ (((y + 5) / 6 : ℕ) : ℝ) * 6 := by exact_mod_cast h
    simp only [Int.cast_natCast]
    linarith

/-- The two literal floor/ceiling inequalities displayed in Lemma2.1. -/
theorem forest_firstMode_paper (F : FiniteForest) :
    (hB F : ℤ) ≤ Int.floor ((3 * (F.n : ℝ) - 2 * (matchingNumber F.graph : ℝ) + 3) / 6) ∧
      Int.floor ((3 * (F.n : ℝ) - 2 * (matchingNumber F.graph : ℝ) + 3) / 6) ≤
        Int.ceil ((3 * (F.n : ℝ) - 2 * (matchingNumber F.graph : ℝ)) / 6) := by
  have h2 := Join.two_mul_matchingNumber_le F.graph
  have hn : 3 * F.n - 2 * matchingNumber F.graph + 2 * matchingNumber F.graph =
      3 * F.n := by omega
  have hr : ((3 * F.n - 2 * matchingNumber F.graph : ℕ) : ℝ) +
      2 * (matchingNumber F.graph : ℝ) = 3 * (F.n : ℝ) := by exact_mod_cast hn
  have heq : 3 * (F.n : ℝ) - 2 * (matchingNumber F.graph : ℝ) =
      ((3 * F.n - 2 * matchingNumber F.graph : ℕ) : ℝ) := by linarith
  rw [heq]
  have hadd : ((3 * F.n - 2 * matchingNumber F.graph : ℕ) : ℝ) + 3 =
      ((3 * F.n - 2 * matchingNumber F.graph + 3 : ℕ) : ℝ) := by push_cast; rfl
  rw [hadd, floor_nat_sixth, ceil_nat_sixth]
  constructor
  · exact_mod_cast forest_firstMode_sharp F
  · exact_mod_cast (show (3 * F.n - 2 * matchingNumber F.graph + 3) / 6 ≤
        (3 * F.n - 2 * matchingNumber F.graph + 5) / 6 by omega)

end Erdos993Lean.Analytic.V213


#check Erdos993Lean.Analytic.V213.trialProb_in_unit
#print axioms Erdos993Lean.Analytic.V213.trialProb_in_unit

#check Erdos993Lean.Analytic.V213.trialProb_cap
#print axioms Erdos993Lean.Analytic.V213.trialProb_cap

#check Erdos993Lean.Analytic.V213.trialProb_sum
#print axioms Erdos993Lean.Analytic.V213.trialProb_sum

#check Erdos993Lean.Analytic.V213.bernoulli_twoWeight_normalization
#print axioms Erdos993Lean.Analytic.V213.bernoulli_twoWeight_normalization

#check Erdos993Lean.Analytic.V213.realTwoWeight_coeff
#print axioms Erdos993Lean.Analytic.V213.realTwoWeight_coeff

#check Erdos993Lean.Analytic.V213.bernoulli_twoWeight_coeff
#print axioms Erdos993Lean.Analytic.V213.bernoulli_twoWeight_coeff

#check Erdos993Lean.Analytic.V213.twoWeight_logConcave_positive
#print axioms Erdos993Lean.Analytic.V213.twoWeight_logConcave_positive

#check Erdos993Lean.Analytic.V213.twoWeight_coeff_succ_le
#print axioms Erdos993Lean.Analytic.V213.twoWeight_coeff_succ_le

#check Erdos993Lean.Analytic.V213.bRow_eq_twoWeight
#print axioms Erdos993Lean.Analytic.V213.bRow_eq_twoWeight

#check Erdos993Lean.Analytic.V213.forest_firstMode_sharp
#print axioms Erdos993Lean.Analytic.V213.forest_firstMode_sharp

#check Erdos993Lean.Analytic.V213.forest_firstMode_sharp_le_ceil_nat
#print axioms Erdos993Lean.Analytic.V213.forest_firstMode_sharp_le_ceil_nat

#check Erdos993Lean.Analytic.V213.floor_nat_sixth
#print axioms Erdos993Lean.Analytic.V213.floor_nat_sixth

#check Erdos993Lean.Analytic.V213.ceil_nat_sixth
#print axioms Erdos993Lean.Analytic.V213.ceil_nat_sixth

#check Erdos993Lean.Analytic.V213.forest_firstMode_paper
#print axioms Erdos993Lean.Analytic.V213.forest_firstMode_paper
