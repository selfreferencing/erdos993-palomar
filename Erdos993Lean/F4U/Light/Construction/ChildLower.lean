module

public import Erdos993Lean.F4U.Light.Construction.ChildConcavity
public import Erdos993Lean.F4U.Light.Construction.Domain

/-! The h-minus bound on the exact light parent/child domain, and the
nonnegative original J field. No extra light hypothesis is introduced. -/

@[expose] public section

namespace F4Unified.LightConstruction
noncomputable section

 theorem hMinus_le_childH {r : Row} {lam H u : ℝ} (hlam : InRow r lam)
    (hHq : H ≤ q lam) (hu0 : 0 ≤ u) (huH : u ≤ H) :
    hMinus r H ≤ F4Unified.childH u := by
  cases r with
  | H =>
    have hu7 : u ≤ 7/10 := huH.trans (hHq.trans (inRow_q_bounds hlam).2)
    have hh := childH_lower_H hu0 hu7
    simp only [hMinus, sigma]
    linarith
  | D | E1 | E2 =>
    have hlpos := (inRow_lambda_bounds hlam).1
    have hlhi : lam ≤ 8/5 := by
      simp only [InRow, rowData] at hlam
      linarith [hlam.2]
    have hq8 : q lam ≤ 8/13 := by
      rw [q, div_le_iff₀ (by linarith : 0 < 1+lam)]
      linarith
    have hh := childH_lower_D_E hu0 (huH.trans (hHq.trans hq8))
    simp only [hMinus, sigma]
    linarith

 theorem childH_positive {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    0 < F4Unified.childH u := by
  have hl : Real.log (1-u) < 0 := Real.log_neg (by linarith) (by linarith)
  simp only [F4Unified.childH, F4Unified.phi, if_neg hu0.ne']
  exact div_pos hu0 (neg_pos.mpr hl)

 theorem childJ_nonnegative {lam u : ℝ} (hlam : 0 < lam)
    (hu0 : 0 < u) (hu1 : u < 1) (huq : u ≤ q lam) :
    0 ≤ F4Unified.childJ lam u := by
  have hden : 0 < 1+lam := by linarith
  have hlu : u*(1+lam) ≤ lam := (le_div_iff₀ hden).mp huq
  have harg : 1 ≤ lam*(1-u)/u := (le_div_iff₀ hu0).2 (by nlinarith)
  have hlog := Real.log_nonneg harg
  have hh := childH_positive hu0 hu1
  simp only [F4Unified.childJ, if_neg hu0.ne']
  exact mul_nonneg (mul_nonneg hu0.le hh.le) hlog

#print axioms hMinus_le_childH
#print axioms childH_positive
#print axioms childJ_nonnegative

end
end F4Unified.LightConstruction
