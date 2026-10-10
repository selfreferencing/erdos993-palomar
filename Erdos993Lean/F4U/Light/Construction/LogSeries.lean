module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace F4Unified.LightConstruction
noncomputable section
open scoped BigOperators

/-- A common integer denominator for the finite odd logarithm series. -/
def logOddProduct (n : ℕ) : ℕ := ∏ i ∈ Finset.range n, (2*i+1)

def logOddExcept (n i : ℕ) : ℕ := ∏ j ∈ (Finset.range n).erase i, (2*j+1)

def logSeriesNumerator (n : ℕ) (a b : ℤ) : ℤ :=
  ∑ i ∈ Finset.range n,
    a^(2*i+1) * b^(2*(n-1-i)) * (logOddExcept n i : ℤ)

def logSeriesDenominator (n : ℕ) (b : ℤ) : ℤ :=
  b^(2*n-1) * (logOddProduct n : ℤ)

theorem logOddProduct_pos (n : ℕ) : 0 < logOddProduct n := by
  apply Finset.prod_pos
  intro i hi
  omega

theorem logOddExcept_mul {n i : ℕ} (hi : i < n) :
    logOddExcept n i * (2*i+1) = logOddProduct n := by
  exact Finset.prod_erase_mul _ _ (Finset.mem_range.mpr hi)

theorem logSeriesDenominator_pos {n : ℕ} {b : ℤ} (hb : 0 < b) :
    0 < logSeriesDenominator n b := by
  exact mul_pos (pow_pos hb _) (by exact_mod_cast logOddProduct_pos n)

theorem logSeries_term {n i : ℕ} (hi : i < n) (a b : ℤ) (hb : b ≠ 0) :
    ((a^(2*i+1) * b^(2*(n-1-i)) * (logOddExcept n i : ℤ) : ℤ) : ℝ) /
      (logSeriesDenominator n b : ℝ) =
      ((a : ℝ)/(b : ℝ))^(2*i+1)/(2*i+1) := by
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  have hoR : (logOddProduct n : ℝ) ≠ 0 := by
    exact_mod_cast (logOddProduct_pos n).ne'
  have hiR : (2*i+1 : ℝ) ≠ 0 := by positivity
  have hp : (b : ℝ)^(2*(n-1-i)) * (b : ℝ)^(2*i+1) = (b : ℝ)^(2*n-1) := by
    rw [← pow_add]
    congr 1
    omega
  have ho : (logOddExcept n i : ℝ)*(2*i+1) = (logOddProduct n : ℝ) := by
    exact_mod_cast logOddExcept_mul hi
  simp only [logSeriesDenominator, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
  rw [div_pow, div_div]
  apply (div_eq_div_iff (mul_ne_zero (pow_ne_zero _ hbR) hoR)
    (mul_ne_zero (pow_ne_zero _ hbR) hiR)).mpr
  calc
    _ = (a : ℝ)^(2*i+1)*
        (((b : ℝ)^(2*(n-1-i))*(b : ℝ)^(2*i+1))*((logOddExcept n i : ℝ)*(2*i+1))) := by ring
    _ = _ := by rw [hp, ho]

theorem logSeries_eval {n : ℕ} (a b : ℤ) (hb : b ≠ 0) :
    (logSeriesNumerator n a b : ℝ)/(logSeriesDenominator n b : ℝ) =
      ∑ i ∈ Finset.range n, ((a : ℝ)/(b : ℝ))^(2*i+1)/(2*i+1) := by
  unfold logSeriesNumerator
  rw [Int.cast_sum, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  simpa only [div_eq_mul_inv] using logSeries_term (Finset.mem_range.mp hi) a b hb

/-- The exact integer objects used by each logarithm enclosure. -/
structure LogCertificate where
  a : ℤ
  b : ℤ
  n : ℕ
  loNumerator : ℤ
  loDenominator : ℤ
  hiNumerator : ℤ
  hiDenominator : ℤ
  deriving DecidableEq, Repr

def LogCertificate.centerNumerator (c : LogCertificate) : ℤ :=
  logSeriesNumerator c.n c.a c.b * (c.b^2-c.a^2)

def LogCertificate.errorNumerator (c : LogCertificate) : ℤ :=
  |c.a|^(2*c.n+1) * (logOddProduct c.n : ℤ)

def LogCertificate.denominator (c : LogCertificate) : ℤ :=
  logSeriesDenominator c.n c.b * (c.b^2-c.a^2)

def checkLogCertificate (c : LogCertificate) : Bool := decide (
  1 ≤ c.n ∧ 0 < c.b ∧ c.a^2 < c.b^2 ∧
  0 < c.loDenominator ∧ 0 < c.hiDenominator ∧
  c.loNumerator*c.denominator ≤
    2*(c.centerNumerator-c.errorNumerator)*c.loDenominator ∧
  2*(c.centerNumerator+c.errorNumerator)*c.hiDenominator ≤
    c.hiNumerator*c.denominator)

/-- Integer arithmetic certifies bounds on this literal positive logarithm argument. -/
def LogCertificate.argument (c : LogCertificate) : ℝ :=
  ((c.b+c.a : ℤ) : ℝ)/((c.b-c.a : ℤ) : ℝ)

theorem logSeries_error_eval {n : ℕ} (hn : 1 ≤ n) (a b : ℤ) (hb : 0 < b)
    (hab : a^2 < b^2) :
    |(a : ℝ)/(b : ℝ)|^(2*n+1)/(1-((a : ℝ)/(b : ℝ))^2) =
      ((|a|^(2*n+1)*(logOddProduct n : ℤ) : ℤ) : ℝ)/
        ((logSeriesDenominator n b*(b^2-a^2) : ℤ) : ℝ) := by
  have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
  have hdiff : 0 < (b : ℝ)^2-(a : ℝ)^2 := by exact_mod_cast sub_pos.mpr hab
  have hprod : 0 < (logOddProduct n : ℝ) := by exact_mod_cast logOddProduct_pos n
  have hp : (b : ℝ)^(2*n-1)*(b : ℝ)^2 = (b : ℝ)^(2*n+1) := by
    rw [← pow_add]
    congr 1
    omega
  simp only [abs_div, abs_of_pos hbR, logSeriesDenominator, Int.cast_mul,
    Int.cast_pow, Int.cast_abs, Int.cast_natCast, Int.cast_sub]
  rw [div_pow]
  field_simp
  rw [← hp]
  ring

theorem checkLogCertificate_sound {c : LogCertificate} (hc : checkLogCertificate c = true) :
    (c.loNumerator : ℝ)/(c.loDenominator : ℝ) ≤ Real.log c.argument ∧
      Real.log c.argument ≤ (c.hiNumerator : ℝ)/(c.hiDenominator : ℝ) := by
  have h := of_decide_eq_true hc
  rcases h with ⟨hn, hb, hab, hloD, hhiD, hlo, hhi⟩
  have hbR : 0 < (c.b : ℝ) := by exact_mod_cast hb
  have habR : (c.a : ℝ)^2 < (c.b : ℝ)^2 := by exact_mod_cast hab
  have ha : |(c.a : ℝ)/(c.b : ℝ)| < 1 := by
    rw [abs_div, abs_of_pos hbR, div_lt_one hbR]
    nlinarith [sq_abs (c.a : ℝ), abs_nonneg (c.a : ℝ)]
  have hdR : 0 < (c.denominator : ℝ) := by
    exact_mod_cast mul_pos (logSeriesDenominator_pos hb) (sub_pos.mpr hab)
  have hsdR : (logSeriesDenominator c.n c.b : ℝ) ≠ 0 := by
    exact_mod_cast (logSeriesDenominator_pos hb).ne'
  have hdiffR : (c.b : ℝ)^2-(c.a : ℝ)^2 ≠ 0 := by nlinarith
  have hloDR : 0 < (c.loDenominator : ℝ) := by exact_mod_cast hloD
  have hhiDR : 0 < (c.hiDenominator : ℝ) := by exact_mod_cast hhiD
  have harg : (1+(c.a : ℝ)/(c.b : ℝ))/(1-(c.a : ℝ)/(c.b : ℝ)) = c.argument := by
    simp only [LogCertificate.argument, Int.cast_add, Int.cast_sub]
    field_simp
  have hbnd := Real.sum_range_sub_log_div_le ha c.n
  rw [harg, ← logSeries_eval c.a c.b hb.ne', logSeries_error_eval hn c.a c.b hb hab] at hbnd
  have hcenter : (logSeriesNumerator c.n c.a c.b : ℝ)/(logSeriesDenominator c.n c.b : ℝ) =
      (c.centerNumerator : ℝ)/(c.denominator : ℝ) := by
    simp only [LogCertificate.centerNumerator, LogCertificate.denominator,
      Int.cast_mul, Int.cast_sub, Int.cast_pow]
    field_simp
  rw [hcenter] at hbnd
  change |1/2*Real.log c.argument-(c.centerNumerator : ℝ)/(c.denominator : ℝ)| ≤
    (c.errorNumerator : ℝ)/(c.denominator : ℝ) at hbnd
  rcases abs_le.mp hbnd with ⟨hleft, hright⟩
  have hloR : (c.loNumerator : ℝ)*(c.denominator : ℝ) ≤
      2*((c.centerNumerator : ℝ)-(c.errorNumerator : ℝ))*(c.loDenominator : ℝ) := by
    exact_mod_cast hlo
  have hhiR : 2*((c.centerNumerator : ℝ)+(c.errorNumerator : ℝ))*(c.hiDenominator : ℝ) ≤
      (c.hiNumerator : ℝ)*(c.denominator : ℝ) := by exact_mod_cast hhi
  constructor
  · have hlower : (c.loNumerator : ℝ)/(c.loDenominator : ℝ) ≤
        2*((c.centerNumerator : ℝ)-(c.errorNumerator : ℝ))/(c.denominator : ℝ) := by
      apply (div_le_div_iff₀ hloDR hdR).mpr
      exact hloR
    rw [mul_div_assoc, sub_div] at hlower
    linarith
  · have hupper : 2*((c.centerNumerator : ℝ)+(c.errorNumerator : ℝ))/(c.denominator : ℝ) ≤
        (c.hiNumerator : ℝ)/(c.hiDenominator : ℝ) := by
      apply (div_le_div_iff₀ hdR hhiDR).mpr
      exact hhiR
    rw [mul_div_assoc, add_div] at hupper
    linarith

#print axioms logOddProduct
#print axioms logOddExcept
#print axioms logSeriesNumerator
#print axioms logSeriesDenominator
#print axioms logOddProduct_pos
#print axioms logOddExcept_mul
#print axioms logSeriesDenominator_pos
#print axioms logSeries_term
#print axioms logSeries_eval
#print axioms LogCertificate
#print axioms checkLogCertificate
#print axioms logSeries_error_eval
#print axioms checkLogCertificate_sound

end
end F4Unified.LightConstruction
