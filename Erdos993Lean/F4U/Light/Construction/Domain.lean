module

public import Erdos993Lean.F4U.Light.Construction.Definitions
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

/-! Explicit parent-coordinate bridges and denominator domains. These lemmas
preserve lambda, H, p and the original source rather than replacing them by
unrelated scalar bounds. -/

@[expose] public section

namespace F4Unified.LightConstruction
noncomputable section

 theorem inRow_lambda_bounds {r : Row} {lam : ℝ} (hlam : InRow r lam) :
    0 < lam ∧ lam ≤ 7 / 3 := by
  cases r <;> simp only [InRow, rowData] at hlam <;> constructor <;> linarith [hlam.1, hlam.2]

 theorem inRow_q_bounds {r : Row} {lam : ℝ} (hlam : InRow r lam) :
    0 < q lam ∧ q lam ≤ 7 / 10 := by
  have hl := inRow_lambda_bounds hlam
  have hden : 0 < 1+lam := by linarith
  constructor
  · exact div_pos hl.1 hden
  · rw [q, div_le_iff₀ hden]
    linarith [hl.2]

 theorem parentH_bounds {Y : ℝ} (hY : 0 < Y) :
    0 < parentH Y ∧ parentH Y < 1 := by
  have he0 := Real.exp_pos (-Y)
  have he1 : Real.exp (-Y) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  unfold parentH
  constructor <;> linarith

 theorem pH_original (lam Y : ℝ) : pH lam (parentH Y) = p lam Y := by
  unfold pH p parentH
  congr 1 <;> ring

 theorem sourceH_original {lam Y rho : ℝ} (hcap : parentH Y ≤ q lam) :
    sourceH lam (parentH Y) rho = source lam Y rho := by
  simp only [sourceH, source, pH_original, childCap, min_eq_right hcap]

 theorem light_child_integral_domain {r : Row} {lam Y u : ℝ}
    (hlam : InRow r lam) (hY : 0 < Y) (hcap : parentH Y ≤ q lam)
    (hu0 : q lam / 2 ≤ u) (huH : u ≤ parentH Y) : 0 ≤ u ∧ u < 1 := by
  have hq := inRow_q_bounds hlam
  constructor <;> linarith [hq.1, hq.2]

 theorem light_rational_denominators {r : Row} {lam H : ℝ}
    (hlam : InRow r lam) (hH0 : 0 ≤ H) (hHq : H ≤ q lam) :
    0 < lam ∧ 0 < 1+lam ∧ 0 < q lam ∧ 0 < 1-q lam ∧
    0 < 1+q lam ∧ 0 < 2-q lam ∧ 0 < 1-H ∧ 0 < 2-H ∧
    0 < 1-q lam*H ∧ 0 < 1+q lam-q lam*H ∧
    0 < H^2-6*H+6 ∧ 0 < pH lam H ∧ 0 < 1-pH lam H ∧
    0 < vacancyLo lam H := by
  have hl := inRow_lambda_bounds hlam
  have hq := inRow_q_bounds hlam
  have hH : H ≤ 7/10 := hHq.trans hq.2
  have hqH : q lam * H ≤ (7/10 : ℝ)*(7/10) :=
    mul_le_mul hq.2 hH hH0 (by norm_num)
  have hlampos := hl.1
  have hHpos : 0 < 1-H := by linarith
  have hpden : 0 < 1+lam*(1-H) := by positivity
  have hp : 0 < pH lam H := by unfold pH; positivity
  have hp1 : pH lam H < 1 := by
    unfold pH
    rw [div_lt_one hpden]
    linarith
  have hpcompl : 0 < 1-pH lam H := by linarith
  have hv : 0 < vacancyLo lam H := by unfold vacancyLo; positivity
  refine ⟨hl.1, by linarith, hq.1, by linarith, by linarith, by linarith,
    by linarith, by linarith, by nlinarith, by nlinarith,
    by nlinarith [sq_nonneg H], hp, by linarith, hv⟩

#print axioms inRow_lambda_bounds
#print axioms inRow_q_bounds
#print axioms parentH_bounds
#print axioms pH_original
#print axioms sourceH_original
#print axioms light_child_integral_domain
#print axioms light_rational_denominators

end
end F4Unified.LightConstruction
