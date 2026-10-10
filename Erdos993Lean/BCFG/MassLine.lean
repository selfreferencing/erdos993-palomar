module

public import Erdos993Lean.BCFG.RowParameters
public import Erdos993Lean.BCFG.RatioConcavity
public import Erdos993Lean.BCFG.LogFixedInterpretation
public import Erdos993Lean.BCFG.FullLightConcavity

/-! The actual two affine mass lower bounds on the full B/C and F/G ranges.
The four endpoint logarithm comparisons are supplied by integer kernel gates. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Erdos993Lean.BCFG.Analytic

open Set Erdos993Lean.Analytic.V213.VarianceResponse

theorem mass_endpoint_BC_left :
    (409 : ℝ)/400-(3/5)*(3/8) ≤ messageRatio (3/8) := by
  have h := NatLog.mass_three_fifths_log
  have hp := Real.log_pos (show (1 : ℝ) < 8/5 by norm_num)
  rw [messageRatio_of_ne_zero (by norm_num : (3/8 : ℝ) ≠ 0)]
  rw [show (1 : ℝ)-3/8 = (8/5 : ℝ)⁻¹ by norm_num, Real.log_inv, neg_neg]
  apply (le_div_iff₀ hp).2
  nlinarith

theorem mass_endpoint_BC_right :
    (409 : ℝ)/400-(3/5)*(4/9) ≤ messageRatio (4/9) := by
  have h := NatLog.mass_four_fifths_log
  have hp := Real.log_pos (show (1 : ℝ) < 9/5 by norm_num)
  rw [messageRatio_of_ne_zero (by norm_num : (4/9 : ℝ) ≠ 0)]
  rw [show (1 : ℝ)-4/9 = (9/5 : ℝ)⁻¹ by norm_num, Real.log_inv, neg_neg]
  apply (le_div_iff₀ hp).2
  nlinarith

theorem mass_endpoint_FG_left :
    (13 : ℝ)/12-(5/7)*(8/13) ≤ messageRatio (8/13) := by
  have h := NatLog.mass_eight_fifths_log
  have hp := Real.log_pos (show (1 : ℝ) < 13/5 by norm_num)
  rw [messageRatio_of_ne_zero (by norm_num : (8/13 : ℝ) ≠ 0)]
  rw [show (1 : ℝ)-8/13 = (13/5 : ℝ)⁻¹ by norm_num, Real.log_inv, neg_neg]
  apply (le_div_iff₀ hp).2
  nlinarith

theorem mass_endpoint_FG_right :
    (13 : ℝ)/12-(5/7)*(7/11) ≤ messageRatio (7/11) := by
  have h := NatLog.mass_seven_fourths_log
  have hp := Real.log_pos (show (1 : ℝ) < 11/4 by norm_num)
  rw [messageRatio_of_ne_zero (by norm_num : (7/11 : ℝ) ≠ 0)]
  rw [show (1 : ℝ)-7/11 = (11/4 : ℝ)⁻¹ by norm_num, Real.log_inv, neg_neg]
  apply (le_div_iff₀ hp).2
  nlinarith

theorem mass_line_BC {u : ℝ} (hu : u ∈ Icc (3/8 : ℝ) (4/9)) :
    409/400-(3/5)*u ≤ messageRatio u := by
  have hc := messageRatio_concaveOn.subset
    (show Icc (3/8 : ℝ) (4/9) ⊆ Ico 0 1 by
      intro x hx
      constructor <;> linarith [hx.1,hx.2]) (convex_Icc _ _)
  have h := affine_minorant_of_concave_endpoints
    (a := -(3/5 : ℝ)) (b := 409/400) hc hu
    (by nlinarith [mass_endpoint_BC_left]) (by nlinarith [mass_endpoint_BC_right])
  nlinarith

theorem mass_line_FG {u : ℝ} (hu : u ∈ Icc (8/13 : ℝ) (7/11)) :
    13/12-(5/7)*u ≤ messageRatio u := by
  have hc := messageRatio_concaveOn.subset
    (show Icc (8/13 : ℝ) (7/11) ⊆ Ico 0 1 by
      intro x hx
      constructor <;> linarith [hx.1,hx.2]) (convex_Icc _ _)
  have h := affine_minorant_of_concave_endpoints
    (a := -(5/7 : ℝ)) (b := 13/12) hc hu
    (by nlinarith [mass_endpoint_FG_left]) (by nlinarith [mass_endpoint_FG_right])
  nlinarith

theorem q_mono {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : q a ≤ q b := by
  unfold q
  apply (div_le_div_iff₀ (by linarith : 0 < 1+a) (by linarith : 0 < 1+b)).2
  nlinarith

theorem q_in_mass_interval {r : AnalyticRow} {lam : ℝ} (hr : InRow r lam) :
    (r = .B ∨ r = .C → q lam ∈ Icc (3/8 : ℝ) (4/9)) ∧
    (r = .F ∨ r = .G → q lam ∈ Icc (8/13 : ℝ) (7/11)) := by
  have hl := activity_pos hr
  cases r <;> simp only [InRow,rowLow,rowHigh] at hr
  all_goals constructor
  all_goals intro h
  all_goals first
    | (exfalso; simpa using h)
    | have hlow := q_mono (by norm_num) hr.1
      have hhigh := q_mono hl hr.2
      norm_num [q] at hlow hhigh
      change _ ≤ lam/(1+lam) ∧ lam/(1+lam) ≤ _
      constructor <;> linarith

/-- The printed H_q is a lower bound on the actual assigned mass ratio. -/
theorem massLine_le_messageRatio {r : AnalyticRow} {lam : ℝ} (hr : InRow r lam) :
    massLine r lam ≤ messageRatio (q lam) := by
  have hi := q_in_mass_interval hr
  cases r
  · simpa only [massLine,massIntercept,massSlope] using
      mass_line_BC (hi.1 (Or.inl rfl))
  · simpa only [massLine,massIntercept,massSlope] using
      mass_line_BC (hi.1 (Or.inr rfl))
  · simpa only [massLine,massIntercept,massSlope] using
      mass_line_FG (hi.2 (Or.inl rfl))
  · simpa only [massLine,massIntercept,massSlope] using
      mass_line_FG (hi.2 (Or.inr rfl))

/-- The strict lower bounds used in the two small-omega tails. -/
theorem massLine_strict_lower {r : AnalyticRow} {lam : ℝ} (hr : InRow r lam) :
    (r = .B ∨ r = .C → 3/4 < massLine r lam) ∧
    (r = .F ∨ r = .G → 5/8 < massLine r lam) := by
  have hi := q_in_mass_interval hr
  constructor
  · intro h
    have hb := (hi.1 h).2
    rcases h with rfl | rfl <;>
      simp only [massLine, massIntercept, massSlope] <;> linarith
  · intro h
    have hb := (hi.2 h).2
    rcases h with rfl | rfl <;>
      simp only [massLine, massIntercept, massSlope] <;> linarith

end Erdos993Lean.BCFG.Analytic

#check Erdos993Lean.BCFG.Analytic.mass_endpoint_BC_left
#print axioms Erdos993Lean.BCFG.Analytic.mass_endpoint_BC_left
#check Erdos993Lean.BCFG.Analytic.mass_endpoint_BC_right
#print axioms Erdos993Lean.BCFG.Analytic.mass_endpoint_BC_right
#check Erdos993Lean.BCFG.Analytic.mass_endpoint_FG_left
#print axioms Erdos993Lean.BCFG.Analytic.mass_endpoint_FG_left
#check Erdos993Lean.BCFG.Analytic.mass_endpoint_FG_right
#print axioms Erdos993Lean.BCFG.Analytic.mass_endpoint_FG_right
#check Erdos993Lean.BCFG.Analytic.mass_line_BC
#print axioms Erdos993Lean.BCFG.Analytic.mass_line_BC
#check Erdos993Lean.BCFG.Analytic.mass_line_FG
#print axioms Erdos993Lean.BCFG.Analytic.mass_line_FG
#check Erdos993Lean.BCFG.Analytic.q_mono
#print axioms Erdos993Lean.BCFG.Analytic.q_mono
#check Erdos993Lean.BCFG.Analytic.q_in_mass_interval
#print axioms Erdos993Lean.BCFG.Analytic.q_in_mass_interval
#check Erdos993Lean.BCFG.Analytic.massLine_le_messageRatio
#print axioms Erdos993Lean.BCFG.Analytic.massLine_le_messageRatio
#check Erdos993Lean.BCFG.Analytic.massLine_strict_lower
#print axioms Erdos993Lean.BCFG.Analytic.massLine_strict_lower
