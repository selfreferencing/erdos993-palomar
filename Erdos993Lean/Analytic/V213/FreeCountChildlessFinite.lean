module

public import Erdos993Lean.Analytic.V213.FreeCountScalarFinite
public import Erdos993Lean.Analytic.V213.FreeCountCAChildlessFace
public import Erdos993Lean.Analytic.V213.FreeCountACTail
public import Erdos993Lean.Analytic.V213.P03ScalarData.Fixed004
public import Erdos993Lean.Analytic.V213.P03PointData.BetaInputs

/-! The ten retained N4/N5 checks, the five retained
beta checks, and their actual parameter/enclosure identities are consumed here.
The actual childless CA face and the AC tail consequently have no numerical
premises. No conclusion for the bounded positive-parent cell region is made.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance.Finite

open Real PrintedScalarRecords
open Erdos993Lean.ExactComparisons
open Erdos993Lean.Analytic.V213.P03PointData.BetaInputs

/-- The quoted Q1,...,Q5 values in the retained parameter family. -/
noncomputable def printedQ : Cap → ℝ
  | .first => 263/463
  | .second => 3/5
  | .third => 7/11
  | .fourth => 2/3
  | .fifth => 7/10

theorem q_upper_eq_printedQ (c : Cap) : q c.upper = printedQ c := by
  cases c with
  | first =>
    have h := parameter_Q1
    push_cast at h
    simpa only [q, Cap.upper, printedQ] using h.symm
  | second =>
    have h := parameter_Q2
    push_cast at h
    simpa only [q, Cap.upper, printedQ] using h.symm
  | third =>
    have h := parameter_Q3
    push_cast at h
    simpa only [q, Cap.upper, printedQ] using h.symm
  | fourth =>
    have h := parameter_Q4
    push_cast at h
    simpa only [q, Cap.upper, printedQ] using h.symm
  | fifth =>
    have h := parameter_Q5
    push_cast at h
    simpa only [q, Cap.upper, printedQ] using h.symm

theorem cap_N4_lower (c : Cap) :
    PrintedCapData.N4_floor c < childlessN4 c.value (q c.upper) := by
  rw [q_upper_eq_printedQ]
  cases c with
  | first =>
    have h := fixed_F42
    rw [nFour_cast] at h
    push_cast at h
    exact h
  | second =>
    have h := fixed_F44
    rw [nFour_cast] at h
    push_cast at h
    exact h
  | third =>
    have h := fixed_F46
    rw [nFour_cast] at h
    push_cast at h
    exact h
  | fourth =>
    have h := fixed_F48
    rw [nFour_cast] at h
    push_cast at h
    exact h
  | fifth =>
    have h := fixed_F50
    rw [nFour_cast] at h
    push_cast at h
    exact h

theorem cap_N5_lower (c : Cap) :
    PrintedCapData.N5_floor c < childlessN5 c.value (q c.upper) := by
  rw [q_upper_eq_printedQ]
  cases c with
  | first =>
    have h := fixed_F43
    rw [nFive_cast] at h
    push_cast at h
    exact h
  | second =>
    have h := fixed_F45
    rw [nFive_cast] at h
    push_cast at h
    exact h
  | third =>
    have h := fixed_F47
    rw [nFive_cast] at h
    push_cast at h
    exact h
  | fourth =>
    have h := fixed_F49
    rw [nFive_cast] at h
    push_cast at h
    exact h
  | fifth =>
    have h := fixed_F51
    rw [nFive_cast] at h
    push_cast at h
    exact h

theorem cap_N4_pos (c : Cap) : 0 < childlessN4 c.value (q c.upper) := by
  have hf : 0 ≤ PrintedCapData.N4_floor c := by
    cases c <;> norm_num [PrintedCapData.N4_floor]
  exact hf.trans_lt (cap_N4_lower c)

theorem cap_N5_pos (c : Cap) : 0 < childlessN5 c.value (q c.upper) := by
  have hf : 0 ≤ PrintedCapData.N5_floor c := by
    cases c <;> norm_num [PrintedCapData.N5_floor]
  exact hf.trans_lt (cap_N5_lower c)

theorem beta_upper_lt_ybar (c : Cap) :
    logActivity c.upper < PrintedCapData.ybar c := by
  cases c with
  | first =>
    have h := b05_bounds.2.2.trans fixed_F37
    simpa [F3All.b05, Cap.upper, PrintedCapData.ybar] using h
  | second =>
    have h := b06_bounds.2.2.trans fixed_F38
    simpa [F3All.b06, Cap.upper, PrintedCapData.ybar] using h
  | third =>
    have h := b07_bounds.2.2.trans fixed_F39
    simpa [F3All.b07, Cap.upper, PrintedCapData.ybar] using h
  | fourth =>
    have h := b08_bounds.2.2.trans fixed_F40
    simpa [F3All.b08, Cap.upper, PrintedCapData.ybar] using h
  | fifth =>
    have h := b09_bounds.2.2.trans fixed_F41
    simpa [F3All.b09, Cap.upper, PrintedCapData.ybar] using h

theorem CA_childless_positive {c : Cap} {lam y : ℝ}
    (hc : c.Contains lam) (hy : logActivity lam ≤ y) :
    0 < CA c.value lam 0 y := by
  have hD : (6/5 : ℝ) ≤ c.value := by cases c <;> norm_num [Cap.value]
  have hlam := Cap.activity_pos hc
  have hd := Cap.activity_domain hc
  have hu : c.upper ≤ (7/3 : ℝ) := by cases c <;> norm_num [Cap.upper]
  have hlu : (1/3 : ℝ) ≤ c.upper := hd.1.trans hc.2
  have hq := q_le_q hlam.le hc.2
  have hqr := (q_closed_domain hlu hu).2
  have hyp := (logActivity_pos hlam).trans_le hy
  have hs := scalarBounds hc (t := 0) (by norm_num) hyp
  exact CA_pos_on_childless_face hD hd.1 hd.2 hq hqr (cap_N4_pos c)
    (cap_N5_pos c) hs.2.2.2.1.le hy

/-- The whole large-parent AC region; no feasibility restriction is required. -/
theorem AC_tail_positive {c : Cap} {lam t y : ℝ}
    (hc : c.Contains lam) (ht : 0 ≤ t) (hy : 3 ≤ y) :
    0 < AC c.value lam t y := by
  have hs := scalarBounds hc ht (show 0 < y by linarith)
  exact Tail.AC_positive_on_cap hc ht hy hs.2.2.2.2 (cap_tail_comparison c)

end Erdos993Lean.Analytic.V213.FreeCountVariance.Finite

#check Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.q_upper_eq_printedQ
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.q_upper_eq_printedQ
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.cap_N4_lower
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.cap_N4_lower
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.cap_N5_lower
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.cap_N5_lower
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.cap_N4_pos
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.cap_N4_pos
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.cap_N5_pos
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.cap_N5_pos
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.beta_upper_lt_ybar
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.beta_upper_lt_ybar
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.CA_childless_positive
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.CA_childless_positive
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.AC_tail_positive
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.AC_tail_positive
