module
public import Erdos993Lean.F4U.Light.Construction.SupportDefinitions
public import Erdos993Lean.F4U.Light.Linking.Polynomial2
public import Erdos993Lean.F4U.Light.Construction.LogSeries
public import Mathlib.Tactic.FieldSimp

@[expose] public section

namespace F4Unified.LightConstruction
noncomputable section

def rationalContactValue (u s kappa phi T : ℝ) : ℝ :=
  u^2*T/phi-s*u/phi+
    ((u*phi+u*(u-2*(1-u)*phi)*T)/(u-(1-u)*phi)-s)^2/(2*kappa)

def contactCleared (u s kappa c phi T : ℝ) : ℝ :=
  2*kappa*(c*phi-u^2*T+s*u)*(u-(1-u)*phi)^2-
    phi*(u*phi+u*(u-2*(1-u)*phi)*T-s*(u-(1-u)*phi))^2

def literalContactValue (e u s kappa : ℝ) : ℝ :=
  childJ e u-s*childH u+(supportDerivative e u-s)^2/(2*kappa)

theorem contactCleared_identity (u s kappa c phi T : ℝ)
    (hphi : phi ≠ 0) (hk : kappa ≠ 0) (hw : u-(1-u)*phi ≠ 0) :
    contactCleared u s kappa c phi T =
      2*kappa*phi*(u-(1-u)*phi)^2*(c-rationalContactValue u s kappa phi T) := by
  unfold contactCleared rationalContactValue
  generalize hWeq : u-(1-u)*phi = W at hw ⊢
  field_simp [hphi, hk, hw]
  ring

theorem literalContactValue_eq_rational (e u s kappa : ℝ) (hu : u ≠ 0)
    (hphi : phi u ≠ 0) (hk : kappa ≠ 0) (hw : u-(1-u)*phi u ≠ 0) :
    literalContactValue e u s kappa =
      rationalContactValue u s kappa (phi u) (Real.log (e*(1-u)/u)) := by
  simp only [literalContactValue, rationalContactValue, supportDerivative,
    childJ, childH, ite_eq_right hu]
  field_simp
  ring

theorem literalContactValue_lt_of_cleared (e u s kappa c : ℝ) (hu : u ≠ 0)
    (hphi : 0 < phi u) (hk : 0 < kappa) (hw : u-(1-u)*phi u ≠ 0)
    (hclear : 0 < contactCleared u s kappa c (phi u) (Real.log (e*(1-u)/u))) :
    literalContactValue e u s kappa < c := by
  rw [literalContactValue_eq_rational e u s kappa hu hphi.ne' hk.ne' hw]
  have heq := contactCleared_identity u s kappa c (phi u)
    (Real.log (e*(1-u)/u)) hphi.ne' hk.ne' hw
  have hscale : 0 < 2*kappa*phi u*(u-(1-u)*phi u)^2 := by positivity
  rw [heq] at hclear
  exact sub_pos.mp ((mul_pos_iff_of_pos_left hscale).mp hclear)

theorem phi_eq_log_inv {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    phi u = Real.log (1/(1-u)) := by
  simp only [phi, ite_eq_right hu0.ne']
  rw [Real.log_div (by norm_num) (by linarith), Real.log_one]
  ring

/-- A collapsed interval is handled by its explicit midpoint, with no division
by a positive-width assumption. -/
theorem normalized_interval {value midpoint radius : ℝ} (hr : 0 ≤ radius)
    (hlo : midpoint-radius ≤ value) (hhi : value ≤ midpoint+radius) :
    |(value-midpoint)/radius| ≤ 1 ∧
      midpoint+radius*((value-midpoint)/radius) = value := by
  by_cases hz : radius = 0
  · have hv : value = midpoint := by linarith
    simp [hz, hv]
  · have hp : 0 < radius := lt_of_le_of_ne hr (Ne.symm hz)
    constructor
    · rw [abs_div, abs_of_pos hp, div_le_one hp]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    · field_simp [hz] <;> ring

#print axioms contactCleared_identity
#print axioms literalContactValue_eq_rational
#print axioms literalContactValue_lt_of_cleared
#print axioms phi_eq_log_inv
#print axioms normalized_interval

end
end F4Unified.LightConstruction
