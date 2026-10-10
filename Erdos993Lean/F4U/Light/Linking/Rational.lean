module
public import Erdos993Lean.F4U.Light.Linking.Polynomial2
public import Mathlib.Tactic.FieldSimp

@[expose] public section

namespace F4U.Light.Linking
open Polynomial2
noncomputable section

/-- Both integer polynomials are retained. No ratio is accepted without its
original nonzero denominator and the exact cancellation identities. -/
structure RationalPair where
  numerator : Rows
  denominator : Rows
  deriving DecidableEq, Repr

def RationalPair.value (p : RationalPair) (x t : ℝ) : ℝ :=
  Polynomial2.eval p.numerator x t / Polynomial2.eval p.denominator x t

def RationalPair.NonzeroDenominator (p : RationalPair) (x t : ℝ) : Prop :=
  Polynomial2.eval p.denominator x t ≠ 0

def rationalConst (a b : ℤ) : RationalPair := ⟨const a, const b⟩
def rationalX : RationalPair := ⟨X, const 1⟩
def rationalT : RationalPair := ⟨Y, const 1⟩

def rawAdd (p q : RationalPair) : RationalPair :=
  ⟨Polynomial2.padd (pmul p.numerator q.denominator) (pmul q.numerator p.denominator),
    pmul p.denominator q.denominator⟩
def rawSub (p q : RationalPair) : RationalPair :=
  ⟨Polynomial2.psub (pmul p.numerator q.denominator) (pmul q.numerator p.denominator),
    pmul p.denominator q.denominator⟩
def rawMul (p q : RationalPair) : RationalPair :=
  ⟨pmul p.numerator q.numerator, pmul p.denominator q.denominator⟩
def rawDiv (p q : RationalPair) : RationalPair :=
  ⟨pmul p.numerator q.denominator, pmul p.denominator q.numerator⟩
def rawPow (p : RationalPair) (n : ℕ) : RationalPair :=
  ⟨ppow p.numerator n, ppow p.denominator n⟩

theorem rationalConst_sound (a b : ℤ) (x t : ℝ) (hb : b ≠ 0) :
    (rationalConst a b).NonzeroDenominator x t ∧
      (rationalConst a b).value x t = (a : ℝ)/(b : ℝ) := by
  simp only [rationalConst, RationalPair.NonzeroDenominator, RationalPair.value, Polynomial2.eval_const]
  exact ⟨by exact_mod_cast hb, trivial⟩

theorem rationalX_sound (x t : ℝ) : rationalX.NonzeroDenominator x t ∧ rationalX.value x t = x := by
  simp [rationalX, RationalPair.NonzeroDenominator, RationalPair.value]
theorem rationalT_sound (x t : ℝ) : rationalT.NonzeroDenominator x t ∧ rationalT.value x t = t := by
  simp [rationalT, RationalPair.NonzeroDenominator, RationalPair.value]

theorem rawAdd_sound (p q : RationalPair) (x t : ℝ)
    (hp : p.NonzeroDenominator x t) (hq : q.NonzeroDenominator x t) :
    (rawAdd p q).NonzeroDenominator x t ∧
      (rawAdd p q).value x t = p.value x t+q.value x t := by
  simp only [rawAdd, RationalPair.NonzeroDenominator, RationalPair.value,
    Polynomial2.eval_padd, Polynomial2.eval_pmul] at *
  exact ⟨mul_ne_zero hp hq, by field_simp <;> ring⟩

theorem rawSub_sound (p q : RationalPair) (x t : ℝ)
    (hp : p.NonzeroDenominator x t) (hq : q.NonzeroDenominator x t) :
    (rawSub p q).NonzeroDenominator x t ∧
      (rawSub p q).value x t = p.value x t-q.value x t := by
  simp only [rawSub, RationalPair.NonzeroDenominator, RationalPair.value,
    Polynomial2.eval_psub, Polynomial2.eval_pmul] at *
  exact ⟨mul_ne_zero hp hq, by field_simp <;> ring⟩

theorem rawMul_sound (p q : RationalPair) (x t : ℝ)
    (hp : p.NonzeroDenominator x t) (hq : q.NonzeroDenominator x t) :
    (rawMul p q).NonzeroDenominator x t ∧
      (rawMul p q).value x t = p.value x t*q.value x t := by
  simp only [rawMul, RationalPair.NonzeroDenominator, RationalPair.value, Polynomial2.eval_pmul] at *
  exact ⟨mul_ne_zero hp hq, by field_simp⟩

theorem rawDiv_sound (p q : RationalPair) (x t : ℝ)
    (hp : p.NonzeroDenominator x t) (hq : q.NonzeroDenominator x t)
    (hvalue : q.value x t ≠ 0) :
    (rawDiv p q).NonzeroDenominator x t ∧
      (rawDiv p q).value x t = p.value x t/q.value x t := by
  have hn : Polynomial2.eval q.numerator x t ≠ 0 := by
    intro hz
    apply hvalue
    simp [RationalPair.value, hz]
  simp only [rawDiv, RationalPair.NonzeroDenominator, RationalPair.value, Polynomial2.eval_pmul] at *
  exact ⟨mul_ne_zero hp hn, by field_simp⟩

theorem rawPow_sound (p : RationalPair) (n : ℕ) (x t : ℝ)
    (hp : p.NonzeroDenominator x t) :
    (rawPow p n).NonzeroDenominator x t ∧
      (rawPow p n).value x t = (p.value x t)^n := by
  simp only [rawPow, RationalPair.NonzeroDenominator, RationalPair.value, Polynomial2.eval_ppow] at *
  exact ⟨pow_ne_zero n hp, (div_pow _ _ n).symm⟩

structure Reduction where
  raw : RationalPair
  reduced : RationalPair
  factor : Rows
  scale : ℤ
  deriving DecidableEq, Repr

def checkReduction (c : Reduction) : Bool :=
  decide (0 < c.scale) &&
    normalizedEq (Polynomial2.pscale c.scale c.raw.numerator) (pmul c.factor c.reduced.numerator) &&
    normalizedEq (Polynomial2.pscale c.scale c.raw.denominator) (pmul c.factor c.reduced.denominator)

theorem checkReduction_sound {c : Reduction} (hc : checkReduction c = true) (x t : ℝ)
    (hraw : c.raw.NonzeroDenominator x t) :
    c.reduced.NonzeroDenominator x t ∧ c.raw.value x t = c.reduced.value x t := by
  simp only [checkReduction, Bool.and_eq_true, decide_eq_true_eq] at hc
  exact reduction_sound hc.1.1 hc.1.2 hc.2 x t hraw

#print axioms rawAdd_sound
#print axioms rawSub_sound
#print axioms rawMul_sound
#print axioms rawDiv_sound
#print axioms rawPow_sound
#print axioms checkReduction_sound

end
end F4U.Light.Linking
