module

public import Erdos993Lean.Analytic.V213.FreeCountScalarCasts
public import Erdos993Lean.Analytic.V213.FreeCountUniformEll
public import Erdos993Lean.Analytic.V213.P03ScalarData.Fixed002
public import Erdos993Lean.Analytic.V213.P03ScalarData.Fixed003
public import Erdos993Lean.Analytic.V213.P03ScalarData.Parameters

/-! The retained F16--F25/F32--F36 inequalities
and H1--H5 parameter equalities supply the first three comparisons in (18).
Only its newly printed fourth comparison, and the five comparisons in (30),
are new finite proofs here.
No retained comparison list is recomputed. Closed cap endpoints are retained.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance.Finite

open Real Envelopes Uniform PrintedScalarRecords

/-- Quoted M column: exactly H1.M,...,H5.M in the retained parameter records. -/
noncomputable def printedM : Cap → ℝ
  | .first => 267809/60000
  | .second => 3029/700
  | .third => 7001/1600
  | .fourth => 2011/450
  | .fifth => 2417/525

/-- Quoted R column: exactly H1.R,...,H5.R in the retained parameter records. -/
noncomputable def printedR : Cap → ℝ
  | .first => 405884/267809
  | .second => 9733/6058
  | .third => 11201/7001
  | .fourth => 3361/2011
  | .fifth => 8509/4834

theorem capM_eq_printedM (c : Cap) :
    capM (5*c.value/12) c.upper = printedM c := by
  cases c with
  | first =>
    have h := parameter_H1_M
    push_cast at h
    simpa only [capM, Cap.value, Cap.upper, printedM] using h.symm
  | second =>
    have h := parameter_H2_M
    push_cast at h
    simpa only [capM, Cap.value, Cap.upper, printedM] using h.symm
  | third =>
    have h := parameter_H3_M
    push_cast at h
    simpa only [capM, Cap.value, Cap.upper, printedM] using h.symm
  | fourth =>
    have h := parameter_H4_M
    push_cast at h
    simpa only [capM, Cap.value, Cap.upper, printedM] using h.symm
  | fifth =>
    have h := parameter_H5_M
    push_cast at h
    simpa only [capM, Cap.value, Cap.upper, printedM] using h.symm

theorem capR_eq_printedR (c : Cap) :
    capR (5*c.value/12) c.upper c.eta = printedR c := by
  unfold capR
  rw [capM_eq_printedM]
  cases c with
  | first =>
    have h := parameter_H1_R
    push_cast at h
    simpa only [Cap.upper, Cap.eta, printedM, printedR] using h.symm
  | second =>
    have h := parameter_H2_R
    push_cast at h
    simpa only [Cap.upper, Cap.eta, printedM, printedR] using h.symm
  | third =>
    have h := parameter_H3_R
    push_cast at h
    simpa only [Cap.upper, Cap.eta, printedM, printedR] using h.symm
  | fourth =>
    have h := parameter_H4_R
    push_cast at h
    simpa only [Cap.upper, Cap.eta, printedM, printedR] using h.symm
  | fifth =>
    have h := parameter_H5_R
    push_cast at h
    simpa only [Cap.upper, Cap.eta, printedM, printedR] using h.symm

theorem cap_taylor (c : Cap) :
    CapEndpoint.H c < expPartial 5 (capR (5*c.value/12) c.upper c.eta) := by
  rw [capR_eq_printedR]
  cases c with
  | first =>
    have h := fixed_F16
    rw [expFive_cast] at h
    push_cast at h
    exact h
  | second =>
    have h := fixed_F18
    rw [expFive_cast] at h
    push_cast at h
    exact h
  | third =>
    have h := fixed_F20
    rw [expFive_cast] at h
    push_cast at h
    exact h
  | fourth =>
    have h := fixed_F22
    rw [expFive_cast] at h
    push_cast at h
    exact h
  | fifth =>
    have h := fixed_F24
    rw [expFive_cast] at h
    push_cast at h
    exact h

theorem cap_margin (c : Cap) :
    0 < 1-capM (5*c.value/12) c.upper/CapEndpoint.H c-
      c.upper^2/4*(3/8 : ℝ)^(CapEndpoint.exponent c) := by
  rw [capM_eq_printedM]
  cases c with
  | first =>
    have h := fixed_F17
    push_cast at h
    convert h using 1 <;>
      simp only [printedM, Cap.upper, CapEndpoint.H, PrintedCapData.H, CapEndpoint.exponent] <;> ring
  | second =>
    have h := fixed_F19
    push_cast at h
    convert h using 1 <;>
      simp only [printedM, Cap.upper, CapEndpoint.H, PrintedCapData.H, CapEndpoint.exponent] <;> ring
  | third =>
    have h := fixed_F21
    push_cast at h
    convert h using 1 <;>
      simp only [printedM, Cap.upper, CapEndpoint.H, PrintedCapData.H, CapEndpoint.exponent] <;> ring
  | fourth =>
    have h := fixed_F23
    push_cast at h
    convert h using 1 <;>
      simp only [printedM, Cap.upper, CapEndpoint.H, PrintedCapData.H, CapEndpoint.exponent] <;> ring
  | fifth =>
    have h := fixed_F25
    push_cast at h
    convert h using 1 <;>
      simp only [printedM, Cap.upper, CapEndpoint.H, PrintedCapData.H, CapEndpoint.exponent] <;> ring

theorem cap_rate_comparison (c : Cap) :
    (25/24+(81/200)*c.upper)/(5*c.value/12) < 10/3 := by
  cases c with
  | first =>
    have h := fixed_F32
    push_cast at h
    convert h using 1 <;> simp only [Cap.upper, Cap.value] <;> ring
  | second =>
    have h := fixed_F33
    push_cast at h
    convert h using 1 <;> simp only [Cap.upper, Cap.value] <;> ring
  | third =>
    have h := fixed_F34
    push_cast at h
    convert h using 1 <;> simp only [Cap.upper, Cap.value] <;> ring
  | fourth =>
    have h := fixed_F35
    push_cast at h
    convert h using 1 <;> simp only [Cap.upper, Cap.value] <;> ring
  | fifth =>
    have h := fixed_F36
    push_cast at h
    convert h using 1 <;> simp only [Cap.upper, Cap.value] <;> ring

/-- Five new displayed comparisons in (18), not claims about the old list. -/
theorem cap_rate_sum_comparison (c : Cap) :
    c.upper+(25/24+(81/200)*c.upper)/(5*c.value/12) < 14/3 := by
  cases c <;> norm_num [Cap.upper, Cap.value]

theorem cap_printed (c : Cap) : CapEndpoint.Printed c :=
  ⟨cap_taylor c, cap_margin c, cap_rate_comparison c, cap_rate_sum_comparison c⟩

/-- The literal five-conclusion scalar lemma, now without finite premises. -/
theorem scalarBounds {c : Cap} {lam t y : ℝ}
    (hc : c.Contains lam) (ht : 0 ≤ t) (hy : 0 < y) :
    c.ScalarBounds lam t y :=
  scalarBounds_of_printed_finite hc ht hy log_369_80_lt (cap_printed c)

/-- The five new displayed comparisons in (30); distinct from retained F data. -/
theorem cap_tail_comparison (c : Cap) :
    (1+c.upper)*(1/c.value+25/48) < 10/3 := by
  cases c <;> norm_num [Cap.upper, Cap.value]

end Erdos993Lean.Analytic.V213.FreeCountVariance.Finite

#check Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.capM_eq_printedM
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.capM_eq_printedM
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.capR_eq_printedR
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.capR_eq_printedR
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.cap_taylor
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.cap_taylor
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.cap_margin
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.cap_margin
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.cap_rate_comparison
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.cap_rate_comparison
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.cap_rate_sum_comparison
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.cap_rate_sum_comparison
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.cap_printed
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.cap_printed
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.scalarBounds
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.scalarBounds
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.cap_tail_comparison
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.cap_tail_comparison
