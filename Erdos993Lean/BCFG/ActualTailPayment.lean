module

public import Erdos993Lean.BCFG.ActualReductionChoices
public import Erdos993Lean.BCFG.TailScalar

/-! The original Lemma 5.11 applied to actual records on the small-vacancy tail.
Every comparison choice is discharged; no scalar positivity premise remains. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Erdos993Lean.BCFG.Analytic

open Finset Erdos993Lean.Analytic
open Erdos993Lean.Analytic.Tail Erdos993Lean.Analytic.Reserve
open Erdos993Lean.Analytic.V213.VarianceResponse

theorem actual_tail_H_nonneg (r : AnalyticRow) : 0 ≤ tailH r := by
  have hBC : (0 : ℝ) < 3/4 := tail_fraction_pos (by decide +kernel)
    (by decide +kernel : (0 : ℕ)*4 < 3*1)
  have hFG : (0 : ℝ) < 5/8 := tail_fraction_pos (by decide +kernel)
    (by decide +kernel : (0 : ℕ)*8 < 5*1)
  cases r
  · exact hBC.le
  · exact hBC.le
  · exact hFG.le
  · exact hFG.le

theorem actual_tail_H_le_massLine {r : AnalyticRow} {lam : ℝ}
    (hrow : InRow r lam) : tailH r ≤ massLine r lam := by
  have h := massLine_strict_lower hrow
  cases r
  · exact (h.1 (Or.inl rfl)).le
  · exact (h.1 (Or.inr rfl)).le
  · exact (h.2 (Or.inl rfl)).le
  · exact (h.2 (Or.inr rfl)).le

theorem actual_tail_cutoff_lt_one (r : AnalyticRow) : tailCutoff r < 1 := by
  have hBC : (1 : ℝ)/16 < 1 := by
    simpa only [Nat.cast_one, Nat.cast_ofNat, div_one] using
      (tail_fraction_lt (by decide +kernel) (by decide +kernel)
        (by decide +kernel : (1 : ℕ)*1 < 1*16))
  have hFG : (1 : ℝ)/64 < 1 := by
    simpa only [Nat.cast_one, Nat.cast_ofNat, div_one] using
      (tail_fraction_lt (by decide +kernel) (by decide +kernel)
        (by decide +kernel : (1 : ℕ)*1 < 1*64))
  cases r
  · exact hBC
  · exact hBC
  · exact hFG
  · exact hFG

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

theorem actual_tail_payment_margin {r : AnalyticRow} {lam : ℝ}
    (hrow : InRow r lam) (hG : G.IsAcyclic)
    {K : Finset V} (hK : ConnectedIn G K) {r0 : V} (hr0 : r0 ∈ K)
    {s : Finset V} {v : V} {rho t : ℝ}
    (hrec : RootRecord G lam K r0 s v rho t)
    (ht : Real.exp (-Tmass G lam s v) ≤ tailCutoff r) :
    epsilon*rootProb G lam s v <
      responsePayment G lam (price r lam) (alpha r) (beta r) (gamma r lam) 0 s v rho t := by
  have hl := activity_pos hrow
  have hs := rootRecord_connected hG hK hr0 hrec
  have hv := rootRecord_mem hr0 hrec
  have hf := reduction_actual_feasible hrow hG hK hr0 hrec
  have hrho : 0 ≤ rho :=
    ((rhoZero_bounds hl (Real.exp_pos _)).1.trans_le hf.2.2.2.1).le
  have hp := rootProb_pos (G := G) hl s v
  have hchild : (nbrsIn G s v).Nonempty := by
    by_contra hn
    have hempty : nbrsIn G s v = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hT : Tmass G lam s v = 0 := by simp only [Tmass, hempty, Finset.sum_empty]
    have hone : Real.exp (-Tmass G lam s v) = 1 := by simp only [hT, neg_zero, Real.exp_zero]
    have hcut := actual_tail_cutoff_lt_one r
    rw [hone] at ht
    linarith only [ht, hcut]
  have hpsi := tail_scalar hf ht (O2.zR G lam s v)
  rw [tailPsi_eq_oneVertexPsi, reduction_actual_occupation hG hl hs hv,
    reduction_actual_logMass] at hpsi
  have hpay := one_vertex_payment_lower hG hl
    (price r lam) (alpha r) (beta r) (gamma r lam) rho t 0 (tailH r)
    (cubicEnvelope (rootProb G lam s v))
    (price_pos hl).le (row_constants_pos r).2.2.1.le (gamma_pos hl).le hrho
    hs hv hchild (reduction_source_nonneg hl hp.le hrho) (actual_tail_H_nonneg r)
    ((actual_tail_H_le_massLine hrow).trans (reduction_actual_massLine hrow hG hs hv))
    (reduction_actual_T0 hG hl hs hv)
  have hm := (mul_lt_mul_of_pos_left hpsi hp).trans_le hpay
  simpa only [mul_comm] using hm

end Erdos993Lean.BCFG.Analytic

#check Erdos993Lean.BCFG.Analytic.actual_tail_H_nonneg
#print axioms Erdos993Lean.BCFG.Analytic.actual_tail_H_nonneg
#check Erdos993Lean.BCFG.Analytic.actual_tail_H_le_massLine
#print axioms Erdos993Lean.BCFG.Analytic.actual_tail_H_le_massLine
#check Erdos993Lean.BCFG.Analytic.actual_tail_cutoff_lt_one
#print axioms Erdos993Lean.BCFG.Analytic.actual_tail_cutoff_lt_one
#check Erdos993Lean.BCFG.Analytic.actual_tail_payment_margin
#print axioms Erdos993Lean.BCFG.Analytic.actual_tail_payment_margin
