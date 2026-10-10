module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceDefs

/-!
# Five closed cap domains and their exact dispatch

Current Section 3 of version 2.13 of the manuscript, equations (13), (17), and Lemma 3.2.
Both neighboring constructions contain a shared endpoint. The selected cap is
the left one there; no equality or continuity of the two reserves is claimed.
`ScalarBounds` states the full five-conclusion target, not a proved numerical
result. Its analytic and finite premises belong to later slices.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance

inductive Cap where
  | first | second | third | fourth | fifth
  deriving DecidableEq

namespace Cap

noncomputable def lower : Cap → ℝ
  | .first => 1 / 3
  | .second => 263 / 200
  | .third => 3 / 2
  | .fourth => 7 / 4
  | .fifth => 2

noncomputable def upper : Cap → ℝ
  | .first => 263 / 200
  | .second => 3 / 2
  | .third => 7 / 4
  | .fourth => 2
  | .fifth => 7 / 3

noncomputable def value : Cap → ℝ
  | .first => 6 / 5
  | .second => 7 / 5
  | .third => 8 / 5
  | .fourth => 9 / 5
  | .fifth => 21 / 10

noncomputable def eta : Cap → ℝ
  | .first | .second => 3 / 4
  | .third | .fourth | .fifth => 1 / 2

noncomputable def jBound : Cap → ℝ
  | .first | .second => 1 / 3
  | .third | .fourth | .fifth => 1 / 2

def Contains (c : Cap) (lam : ℝ) : Prop := c.lower ≤ lam ∧ lam ≤ c.upper

theorem lower_pos (c : Cap) : 0 < c.lower := by cases c <;> norm_num [lower]
theorem lower_lt_upper (c : Cap) : c.lower < c.upper := by
  cases c <;> norm_num [lower, upper]
theorem value_pos (c : Cap) : 0 < c.value := by cases c <;> norm_num [value]
theorem eta_pos (c : Cap) : 0 < c.eta := by cases c <;> norm_num [eta]
theorem jBound_pos (c : Cap) : 0 < c.jBound := by cases c <;> norm_num [jBound]
theorem eta_mul_jBound (c : Cap) : c.eta * c.jBound = (1 / 4 : ℝ) := by
  cases c <;> norm_num [eta, jBound]

theorem activity_pos {c : Cap} {lam : ℝ} (hc : c.Contains lam) : 0 < lam :=
  lt_of_lt_of_le c.lower_pos hc.1

theorem activity_domain {c : Cap} {lam : ℝ} (hc : c.Contains lam) :
    (1 / 3 : ℝ) ≤ lam ∧ lam ≤ 7 / 3 := by
  cases c <;> simp only [Contains, lower, upper] at hc <;> constructor <;> linarith

/-- All five bounds of Lemma 3.2, with no hidden feasibility premise. -/
def ScalarBounds (c : Cap) (lam t y : ℝ) : Prop :=
  J lam t < c.jBound ∧ -c.eta < ell c.value lam y ∧
    (3 / 4 : ℝ) * message lam y * gamma c.value lam < Z c.value lam t y ∧
    lam / gamma c.value lam < 10 / 3 ∧ lam * (1 + 1 / gamma c.value lam) < 14 / 3

/-- This is only the symbolic denominator implication. The two strict scalar
premises remain obligations on the whole printed domain `y>0,t≥0`. -/
theorem denominator_of_two_bounds {c : Cap} {lam t y : ℝ}
    (hc : c.Contains lam) (ht : 0 ≤ t)
    (hJ : J lam t < c.jBound) (hell : -c.eta < ell c.value lam y) :
    (3 / 4 : ℝ) * message lam y * gamma c.value lam < Z c.value lam t y :=
  Z_gt_three_quarters_of_bounds c.value_pos (activity_pos hc) ht c.eta_pos
    c.jBound_pos c.eta_mul_jBound hJ hell

end Cap

noncomputable def selectedCap (lam : ℝ) : Cap :=
  if lam ≤ 263 / 200 then .first else
  if lam ≤ 3 / 2 then .second else
  if lam ≤ 7 / 4 then .third else
  if lam ≤ 2 then .fourth else .fifth

noncomputable def Dhat (lam : ℝ) : ℝ := (selectedCap lam).value

theorem selectedCap_contains {lam : ℝ} (hl : (1 / 3 : ℝ) ≤ lam) (hu : lam ≤ 7 / 3) :
    (selectedCap lam).Contains lam := by
  unfold selectedCap
  split_ifs <;> simp only [Cap.Contains, Cap.lower, Cap.upper] <;> constructor <;> linarith

theorem closed_cap_cover {lam : ℝ} (hl : (1 / 3 : ℝ) ≤ lam) (hu : lam ≤ 7 / 3) :
    ∃ c : Cap, c.Contains lam := ⟨selectedCap lam, selectedCap_contains hl hu⟩

theorem Dhat_pos {lam : ℝ} : 0 < Dhat lam := (selectedCap lam).value_pos

theorem selected_left_end : selectedCap (1 / 3) = .first := by norm_num [selectedCap]
theorem selected_seam_one : selectedCap (263 / 200) = .first := by norm_num [selectedCap]
theorem selected_seam_two : selectedCap (3 / 2) = .second := by norm_num [selectedCap]
theorem selected_seam_three : selectedCap (7 / 4) = .third := by norm_num [selectedCap]
theorem selected_seam_four : selectedCap 2 = .fourth := by norm_num [selectedCap]
theorem selected_right_end : selectedCap (7 / 3) = .fifth := by norm_num [selectedCap]

theorem Dhat_endpoints :
    Dhat (1 / 3) = 6 / 5 ∧ Dhat (263 / 200) = 6 / 5 ∧
    Dhat (3 / 2) = 7 / 5 ∧ Dhat (7 / 4) = 8 / 5 ∧ Dhat 2 = 9 / 5 ∧
    Dhat (7 / 3) = 21 / 10 := by
  norm_num [Dhat, selectedCap, Cap.value]

theorem both_seam_one : Cap.first.Contains (263 / 200) ∧ Cap.second.Contains (263 / 200) := by
  norm_num [Cap.Contains, Cap.lower, Cap.upper]
theorem both_seam_two : Cap.second.Contains (3 / 2) ∧ Cap.third.Contains (3 / 2) := by
  norm_num [Cap.Contains, Cap.lower, Cap.upper]
theorem both_seam_three : Cap.third.Contains (7 / 4) ∧ Cap.fourth.Contains (7 / 4) := by
  norm_num [Cap.Contains, Cap.lower, Cap.upper]
theorem both_seam_four : Cap.fourth.Contains 2 ∧ Cap.fifth.Contains 2 := by
  norm_num [Cap.Contains, Cap.lower, Cap.upper]

theorem q_le_q {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : q a ≤ q b := by
  have hb : 0 ≤ b := le_trans ha hab
  unfold q
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith

theorem q_lt_q {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) : q a < q b := by
  have hb : 0 < b := lt_of_le_of_lt ha hab
  unfold q
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
  nlinarith

theorem q_cap_endpoints :
    q (1 / 3) = 1 / 4 ∧ q (263 / 200) = 263 / 463 ∧ q (3 / 2) = 3 / 5 ∧
    q (7 / 4) = 7 / 11 ∧ q 2 = 2 / 3 ∧ q (7 / 3) = 7 / 10 := by norm_num [q]

/-- The separate lambda=3/4 coordinate, without treating it as a five-cap seam. -/
theorem q_three_quarters : q (3 / 4) = 3 / 7 := by norm_num [q]

theorem q_closed_domain {lam : ℝ} (hl : (1 / 3 : ℝ) ≤ lam) (hu : lam ≤ 7 / 3) :
    (1 / 4 : ℝ) ≤ q lam ∧ q lam ≤ 7 / 10 := by
  have hp : 0 ≤ lam := by linarith
  have h1 := q_le_q (a := 1 / 3) (by norm_num) hl
  have h2 := q_le_q hp hu
  norm_num [q] at h1 h2 ⊢
  exact ⟨h1, h2⟩

theorem childless_coefficients {D lam : ℝ} (hD : 0 < D) (hlam : 0 < lam) (y : ℝ) :
    message lam 0 = q lam ∧ logMass lam 0 = logActivity lam ∧
    J lam 0 = 0 ∧ Z D lam 0 y = message lam y * gamma D lam ∧ 0 < Z D lam 0 y := by
  refine ⟨message_zero lam, logMass_zero lam, J_zero lam, Z_zero D lam y, ?_⟩
  rw [Z_zero]
  exact mul_pos (message_pos hlam y) (gamma_pos hD hlam)

/-- At the physical zero-child endpoint the selected-parent correction vanishes.
No division by the child sum is used. -/
theorem AC_zero (D lam y : ℝ) :
    AC D lam 0 y = CC D lam 0 y + (capA D lam * message lam y - H D lam y) / y := by
  simp [AC, CC]

theorem CA_zero {D lam : ℝ} (hD : 0 < D) (hlam : 0 < lam) (y : ℝ) :
    CA D lam 0 y = CC D lam 0 y + L D lam y * (q lam / logActivity lam) ^ 2 := by
  have hp := (message_pos hlam y).ne'
  have hg := (gamma_pos hD hlam).ne'
  rw [CA, CC, message_zero, logMass_zero, Z_zero]
  field_simp <;> ring

theorem rate_ratio_rewrite {D lam : ℝ} (hD : 0 < D) (hlam : 0 < lam) :
    lam / gamma D lam = 12 * lam / (5 * D * logActivity lam) := by
  unfold gamma
  ring

theorem second_rate_rewrite (D lam : ℝ) :
    lam * (1 + 1 / gamma D lam) = lam + lam / gamma D lam := by ring

/-- Generic clearing of the first printed rate comparison, after positivity. -/
theorem rate_ratio_iff {D lam c : ℝ} (hD : 0 < D) (hlam : 0 < lam) :
    lam / gamma D lam < c ↔ lam < c * gamma D lam :=
  div_lt_iff₀ (gamma_pos hD hlam)

theorem second_rate_iff {D lam c : ℝ} (hD : 0 < D) (hlam : 0 < lam) :
    lam * (1 + 1 / gamma D lam) < c ↔ lam < (c - lam) * gamma D lam := by
  rw [second_rate_rewrite]
  have hh : lam + lam / gamma D lam < c ↔ lam / gamma D lam < c - lam := by constructor <;> intro h <;> linarith
  rw [hh, rate_ratio_iff hD hlam]

end Erdos993Lean.Analytic.V213.FreeCountVariance

-- Type and axiom audit commands.
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Cap.lower_pos
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Cap.lower_pos
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Cap.lower_lt_upper
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Cap.lower_lt_upper
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Cap.value_pos
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Cap.value_pos
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Cap.eta_pos
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Cap.eta_pos
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Cap.jBound_pos
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Cap.jBound_pos
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Cap.eta_mul_jBound
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Cap.eta_mul_jBound
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Cap.activity_pos
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Cap.activity_pos
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Cap.activity_domain
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Cap.activity_domain
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Cap.denominator_of_two_bounds
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Cap.denominator_of_two_bounds
#check Erdos993Lean.Analytic.V213.FreeCountVariance.selectedCap_contains
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.selectedCap_contains
#check Erdos993Lean.Analytic.V213.FreeCountVariance.closed_cap_cover
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.closed_cap_cover
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Dhat_pos
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Dhat_pos
#check Erdos993Lean.Analytic.V213.FreeCountVariance.selected_left_end
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.selected_left_end
#check Erdos993Lean.Analytic.V213.FreeCountVariance.selected_seam_one
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.selected_seam_one
#check Erdos993Lean.Analytic.V213.FreeCountVariance.selected_seam_two
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.selected_seam_two
#check Erdos993Lean.Analytic.V213.FreeCountVariance.selected_seam_three
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.selected_seam_three
#check Erdos993Lean.Analytic.V213.FreeCountVariance.selected_seam_four
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.selected_seam_four
#check Erdos993Lean.Analytic.V213.FreeCountVariance.selected_right_end
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.selected_right_end
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Dhat_endpoints
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Dhat_endpoints
#check Erdos993Lean.Analytic.V213.FreeCountVariance.both_seam_one
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.both_seam_one
#check Erdos993Lean.Analytic.V213.FreeCountVariance.both_seam_two
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.both_seam_two
#check Erdos993Lean.Analytic.V213.FreeCountVariance.both_seam_three
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.both_seam_three
#check Erdos993Lean.Analytic.V213.FreeCountVariance.both_seam_four
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.both_seam_four
#check Erdos993Lean.Analytic.V213.FreeCountVariance.q_le_q
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.q_le_q
#check Erdos993Lean.Analytic.V213.FreeCountVariance.q_lt_q
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.q_lt_q
#check Erdos993Lean.Analytic.V213.FreeCountVariance.q_cap_endpoints
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.q_cap_endpoints
#check Erdos993Lean.Analytic.V213.FreeCountVariance.q_three_quarters
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.q_three_quarters
#check Erdos993Lean.Analytic.V213.FreeCountVariance.q_closed_domain
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.q_closed_domain
#check Erdos993Lean.Analytic.V213.FreeCountVariance.childless_coefficients
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.childless_coefficients
#check Erdos993Lean.Analytic.V213.FreeCountVariance.AC_zero
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.AC_zero
#check Erdos993Lean.Analytic.V213.FreeCountVariance.CA_zero
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.CA_zero
#check Erdos993Lean.Analytic.V213.FreeCountVariance.rate_ratio_rewrite
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.rate_ratio_rewrite
#check Erdos993Lean.Analytic.V213.FreeCountVariance.second_rate_rewrite
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.second_rate_rewrite
#check Erdos993Lean.Analytic.V213.FreeCountVariance.rate_ratio_iff
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.rate_ratio_iff
#check Erdos993Lean.Analytic.V213.FreeCountVariance.second_rate_iff
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.second_rate_iff
