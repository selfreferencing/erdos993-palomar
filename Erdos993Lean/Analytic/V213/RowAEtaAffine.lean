module

public import Erdos993Lean.Analytic.V213.RowADefinitions
public import Erdos993Lean.Analytic.V213.FreeCountRealLogEnvelopes

/-!
Current Row A auxiliary. The printed affine lower bound for eta follows
from a first-derivative comparison for a rational upper bound of log(1+lambda).
This avoids the convexity proof for eta in the printed argument. Every
coefficient in the derivative and chord identities is checked by ring; none is
an external certificate record.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.RowA

open Set FreeCountVariance.Envelopes

noncomputable def etaLogUpper (lam : ℝ) : ℝ :=
  400*lam/((1+lam)*(373-90*lam))

noncomputable def etaUpperDerivativeNumerator (lam : ℝ) : ℝ :=
  10071-61918*lam+23051*lam^2+86940*lam^3-8100*lam^4

theorem eta_upper_numerator_negative {lam : ℝ}
    (hl : (1:ℝ)/3 ≤ lam) (hu : lam ≤ 3/5) :
    etaUpperDerivativeNumerator lam < 0 := by
  let t := (15*lam-5)/4
  have ht0 : 0 ≤ t := by dsimp [t]; linarith
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  have hlam0 : 0 ≤ lam := by linarith
  have hlam2 : lam^2 ≤ 9/25 := by
    nlinarith [mul_nonneg hlam0 (show 0 ≤ 3/5-lam by linarith)]
  have hQ : 0 ≤ 98759+79380*lam-8100*lam^2 := by nlinarith
  have hn := mul_nonneg
    (mul_nonneg (show 0 ≤ lam-1/3 by linarith)
      (show 0 ≤ 3/5-lam by linarith)) hQ
  have hid : etaUpperDerivativeNumerator lam =
      (1-t)*(-43984/9)+t*(-26304/25) -
        (lam-1/3)*(3/5-lam)*(98759+79380*lam-8100*lam^2) := by
    dsimp [etaUpperDerivativeNumerator, t]
    ring
  rw [hid]
  nlinarith

theorem eta_log_gap_hasDerivAt {lam : ℝ}
    (hl : (1:ℝ)/3 ≤ lam) (hu : lam ≤ 3/5) :
    HasDerivAt (fun x => etaLogUpper x-Real.log (1+x))
      (etaUpperDerivativeNumerator lam/((1+lam)^3*(373-90*lam)^2)) lam := by
  have h1 : 1+lam ≠ 0 := by linarith
  have h2 : 373-90*lam ≠ 0 := by linarith
  have hD := mul_ne_zero h1 h2
  have hsq : 139129-lam*67140+lam^2*8100 ≠ 0 := by
    have heq : 139129-lam*67140+lam^2*8100=(373-90*lam)^2 := by ring
    rw [heq]
    exact pow_ne_zero 2 h2
  convert ((((hasDerivAt_id lam).const_mul 400).div
    (((hasDerivAt_id lam).const_add 1).mul
      (((hasDerivAt_id lam).const_mul 90).const_sub 373)) hD).sub
        (((hasDerivAt_id lam).const_add 1).log h1)) using 1 <;>
    first
    | (funext t <;> (try dsimp [etaLogUpper]) <;> ring)
    | (dsimp [etaLogUpper, etaUpperDerivativeNumerator] <;>
        field_simp [h1,h2,hsq] <;> ring_nf <;> field_simp [hsq] <;> ring)

theorem eta_log_gap_antitone :
    AntitoneOn (fun x => etaLogUpper x-Real.log (1+x)) (Icc (1/3:ℝ) (3/5)) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc (1/3:ℝ) (3/5))
    (f' := fun x => etaUpperDerivativeNumerator x/((1+x)^3*(373-90*x)^2))
  · intro x hx
    exact (eta_log_gap_hasDerivAt hx.1 hx.2).continuousAt.continuousWithinAt
  · intro x hx
    have h := interior_subset hx
    exact (eta_log_gap_hasDerivAt h.1 h.2).hasDerivWithinAt
  · intro x hx
    have h := interior_subset hx
    have hx0 : 0 ≤ x := by linarith [h.1]
    exact div_nonpos_of_nonpos_of_nonneg
      (eta_upper_numerator_negative h.1 h.2).le (by positivity)

theorem log_eight_fifths_upper :
    Real.log (8/5:ℝ) ≤ 413043/878800 := by
  have h := artanh_brackets (w := 3/13) (by norm_num) (by norm_num)
  norm_num [seriesS,seriesT] at h
  linarith [h.2]

theorem eta_log_gap_positive {lam : ℝ}
    (hl : (1:ℝ)/3 ≤ lam) (hu : lam ≤ 3/5) :
    0 < etaLogUpper lam-Real.log (1+lam) := by
  have hright : 0 < etaLogUpper (3/5)-Real.log (1+(3/5:ℝ)) := by
    have h := log_eight_fifths_upper
    norm_num [etaLogUpper]
    linarith
  exact lt_of_lt_of_le hright
    (eta_log_gap_antitone ⟨hl,hu⟩ ⟨by norm_num,le_rfl⟩ hu)

/-- The actual printed affine lower bound; eta is q/log, not an abstract input. -/
theorem eta_lower {lam : ℝ} (hl : (1:ℝ)/3 ≤ lam) (hu : lam ≤ 3/5) :
    (373-90*lam)/400 ≤ eta lam := by
  have h1 : 0 < 1+lam := by linarith
  have h2 : 0 < 373-90*lam := by linarith
  have hlog : 0 < Real.log (1+lam) := Real.log_pos (by linarith)
  have hbound : Real.log (1+lam) ≤ etaLogUpper lam :=
    (sub_pos.mp (eta_log_gap_positive hl hu)).le
  have hm := mul_le_mul_of_nonneg_left hbound
    (show 0 ≤ (373-90*lam)/400 by positivity)
  have hid : ((373-90*lam)/400)*etaLogUpper lam = q lam := by
    dsimp [etaLogUpper, q]
    field_simp [h1.ne',h2.ne'] <;> ring
  rw [hid] at hm
  unfold eta
  exact (le_div_iff₀ hlog).2 hm

end Erdos993Lean.Analytic.V213.VarianceResponse.RowA

#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.etaLogUpper
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.etaLogUpper
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.etaUpperDerivativeNumerator
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.etaUpperDerivativeNumerator
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.eta_upper_numerator_negative
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.eta_upper_numerator_negative
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.eta_log_gap_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.eta_log_gap_hasDerivAt
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.eta_log_gap_antitone
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.eta_log_gap_antitone
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.log_eight_fifths_upper
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.log_eight_fifths_upper
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.eta_log_gap_positive
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.eta_log_gap_positive
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.eta_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.eta_lower
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.artanh_brackets
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.artanh_brackets

