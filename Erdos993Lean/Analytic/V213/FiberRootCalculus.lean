module

public import Erdos993Lean.Analytic.V22.Analysis.SharedRoot

/-!
Eq65--66 using the actual unique solution s>-1 of s+log(1+s)=omega.
Both Taylor forms and all zero/monotonicity clauses retain their printed
real domains. This is accepted generic calculus, with no finite data.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real Set
open Erdos993Lean.Analytic.V22.Analysis

theorem fiber_root_solution (omega : ℝ) :
    -1 < V22.rootMap omega ∧
      V22.rootMap omega + Real.log (1 + V22.rootMap omega) = omega :=
  ⟨shared_rootMap_gt_neg_one omega, shared_rootMap_equation omega⟩

theorem fiber_root_derivative (omega : ℝ) :
    HasDerivAt V22.rootMap ((1 + V22.rootMap omega) / (2 + V22.rootMap omega)) omega ∧
      0 < (1 + V22.rootMap omega) / (2 + V22.rootMap omega) ∧
      (1 + V22.rootMap omega) / (2 + V22.rootMap omega) < 1 := by
  have hs : 0 < 1 + V22.rootMap omega := by linarith [shared_rootMap_gt_neg_one omega]
  have ht : 0 < 2 + V22.rootMap omega := by linarith
  exact ⟨shared_hasDerivAt_rootMap omega, div_pos hs ht,
    (div_lt_one ht).2 (by linarith)⟩

theorem fiber_G_derivatives (omega : ℝ) :
    HasDerivAt V22.G (V22.rootMap omega / (1 + V22.rootMap omega)) omega ∧
      V22.rootMap omega / (1 + V22.rootMap omega) < 1 ∧
      HasDerivAt V22.G1 (1 / ((1 + V22.rootMap omega) * (2 + V22.rootMap omega))) omega ∧
      0 < 1 / ((1 + V22.rootMap omega) * (2 + V22.rootMap omega)) := by
  exact ⟨shared_hasDerivAt_G omega, shared_G1_lt_one omega,
    shared_hasDerivAt_G1 omega, shared_G2_pos omega⟩

theorem fiber_G_monotonicity :
    Antitone V22.G2 ∧ AntitoneOn V22.G (Iic 0) ∧ MonotoneOn V22.G (Ici 0) :=
  ⟨shared_G2_antitone, shared_G_antitoneOn_nonpos, shared_G_monotoneOn_nonneg⟩

theorem fiber_G_zero : V22.rootMap 0 = 0 ∧ V22.G 0 = 0 ∧ V22.G1 0 = 0 := by
  simp

theorem fiber_G_taylor_forward (omega h : ℝ) (hh : 0 ≤ h) :
    V22.G (omega + h) ≤ V22.G omega + h * V22.G1 omega + h ^ 2 / 2 * V22.G2 omega :=
  shared_G_taylor_shift_upper omega h hh

theorem fiber_G_taylor_all_real (omega h : ℝ) :
    V22.G (omega + h) ≤ V22.G omega + h * V22.G1 (omega + h) := by
  simpa only [shared_G_eq, shared_G1_eq] using rootG_shift_linear_upper omega h

end Erdos993Lean.Analytic.V213
